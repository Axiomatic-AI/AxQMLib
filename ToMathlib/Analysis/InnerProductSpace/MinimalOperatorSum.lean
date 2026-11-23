/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumFreedom
public import ToMathlib.Analysis.InnerProductSpace.RankOneSum
public import ToMathlib.Analysis.InnerProductSpace.Matricization

/-! # The minimal operator-sum representation: at most `d²` operation elements

For a finite family of operation elements `E : ι → (H →L[ℂ] G)`, the **operator-sum map**
`ContinuousLinearMap.krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` may be indexed by an arbitrarily large `ι`.
This file proves that it can always be re-expressed with at most `dim G · dim H` operation
elements — and, in the square case `G = H`, at most `d²` where `d = dim H`. This is
Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Theorem 8.3** (the square
case, `exists_krausSumₗ_eq_fin_finrank_sq`), together with its `d`-to-`d′` generalization,
**Exercise 8.11** (`exists_krausSumₗ_eq_fin_finrank`).

## Main results

* `ContinuousLinearMap.krausSumₗ_eq_of_choi_eq` — **the Choi operator determines the operator-sum
  map**: if the vectorized (Choi) rank-one sums agree,
  `Σᵢ |vec Eᵢ⟩⟨vec Eᵢ| = Σₖ |vec Fₖ⟩⟨vec Fₖ|` on `G ⊗ H` (`vec = (matricize b).symm`), even over
  *different* index sets, then `krausSumₗ E = krausSumₗ F`.
* `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank` — **Exercise 8.11**: every operator-sum
  map on a `d`-input, `d′`-output space has an equal operator-sum map indexed by
  `Fin (dim G · dim H)`.
* `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank_sq` — **Theorem 8.3**: on a `d`-dimensional
  system (`G = H`), an equal operator-sum map indexed by `Fin (d²)`.

## Implementation notes

The engine is the linear-algebra reduction
`InnerProductSpace.exists_sum_rankOne_self_eq_fin_finrank` (the sum of rank-one projectors of any
finite family equals one over `Fin (finrank)`), applied to the **Choi vectors**
`vec Eᵢ = (TensorProduct.matricize b).symm Eᵢ ∈ G ⊗ H`, whose ambient space has
`finrank = dim G · dim H`. Un-vectorizing the reduced family `Wₖ` by `matricize b` yields the
operation elements `Fₖ`, whose Choi operator equals that of `E` by construction; the two
operator-sum maps then agree by `krausSumₗ_eq_of_choi_eq`, and reindexing to the dimension bound is
`ContinuousLinearMap.krausSumₗ_comp_equiv`.

The Choi-determines-map step is self-contained via the general operator-sum "freedom" API of
`ToMathlib.Analysis.InnerProductSpace.OperatorSumFreedom`: equal Choi operators over the (possibly
distinct) index sets `ι` and `κ` are padded to a common index `ι ⊕ κ` (appending zero operators —
`krausSumₗ_sumElim_zero_left`/`_right` — changes neither the Choi operator nor the operator-sum
map), where the vector form of Nielsen & Chuang Theorem 2.6
(`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup`) supplies the relating unitary;
transporting it back through `matricize` and applying `krausSumₗ_eq_of_unitary_smul` gives the equal
operator-sum maps. In particular this route uses only the vectorization `TensorProduct.matricize`
and the rank-one reduction; it does not require the full Choi–Jamiołkowski correspondence.

The bound `Fin (dim G · dim H)` (resp. `Fin d²`) is N&C's "at most `M`" with `1 ≤ M ≤ d²` in padded
form: the produced family has exactly `dim G · dim H` slots, some of which may be the zero operator
(a zero operation element contributes nothing to the operator-sum map).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **The Choi operator determines the operator-sum map.** Fix an orthonormal basis `b` of the input
space `H` and vectorize operation elements by `vec = (TensorProduct.matricize b).symm : (H →L G) →
(G ⊗ H)`. If two families `E : ι → (H →L[ℂ] G)` and `F : κ → (H →L[ℂ] G)` — over possibly
*different* finite index sets — have equal **Choi operators**
`Σᵢ |vec Eᵢ⟩⟨vec Eᵢ| = Σₖ |vec Fₖ⟩⟨vec Fₖ|` on `G ⊗ H`, then they induce the same operator-sum map,
`krausSumₗ E = krausSumₗ F`.

Pad both families to the common index `ι ⊕ κ` by appending zero operators (which changes neither the
Choi operator nor, by `krausSumₗ_sumElim_zero_left`/`_right`, the operator-sum map). The equal Choi
operators over `ι ⊕ κ` are equal sums of rank-one projectors of the two vectorized families, so the
vector form of Nielsen & Chuang Theorem 2.6
(`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup`) yields a unitary `u` with
`vec (padE a) = Σ_b uₐ_b • vec (padF b)`; applying the linear equivalence `matricize b` transports
this to the operation elements, `padE a = Σ_b uₐ_b • padF b`, and `krausSumₗ_eq_of_unitary_smul`
finishes. -/
theorem krausSumₗ_eq_of_choi_eq {ιb : Type*} [Fintype ιb] (b : OrthonormalBasis ιb ℂ H)
    {ι κ : Type*} [Fintype ι] [Fintype κ] {E : ι → H →L[ℂ] G} {F : κ → H →L[ℂ] G}
    (h : ∑ i, InnerProductSpace.rankOne ℂ ((TensorProduct.matricize b).symm (E i))
            ((TensorProduct.matricize b).symm (E i))
       = ∑ k, InnerProductSpace.rankOne ℂ ((TensorProduct.matricize b).symm (F k))
            ((TensorProduct.matricize b).symm (F k))) :
    krausSumₗ E = krausSumₗ F := by
  classical
  have : CompleteSpace (G ⊗[ℂ] H) := FiniteDimensional.completeSpace ℂ _
  set padE : ι ⊕ κ → G ⊗[ℂ] H :=
    Sum.elim (fun i => (TensorProduct.matricize b).symm (E i)) (fun _ => 0) with hpadE
  set padF : ι ⊕ κ → G ⊗[ℂ] H :=
    Sum.elim (fun _ => 0) (fun k => (TensorProduct.matricize b).symm (F k)) with hpadF
  have hchoi : ∑ a, InnerProductSpace.rankOne ℂ (padE a) (padE a)
      = ∑ a, InnerProductSpace.rankOne ℂ (padF a) (padF a) := by
    simp only [hpadE, hpadF, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      map_zero, Finset.sum_const_zero, add_zero, zero_add]
    exact h
  obtain ⟨u, hu, hrel⟩ :=
    (InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup padE padF).mp hchoi
  set EE : ι ⊕ κ → H →L[ℂ] G := Sum.elim E (fun _ => 0) with hEE
  set FF : ι ⊕ κ → H →L[ℂ] G := Sum.elim (fun _ => 0) F with hFF
  have hmapE : ∀ a, TensorProduct.matricize b (padE a) = EE a := by
    rintro (i | k)
    · simp only [hpadE, hEE, Sum.elim_inl, LinearEquiv.apply_symm_apply]
    · simp only [hpadE, hEE, Sum.elim_inr, map_zero]
  have hmapF : ∀ a, TensorProduct.matricize b (padF a) = FF a := by
    rintro (i | k)
    · simp only [hpadF, hFF, Sum.elim_inl, map_zero]
    · simp only [hpadF, hFF, Sum.elim_inr, LinearEquiv.apply_symm_apply]
  have hrel' : ∀ a, EE a = ∑ b', u a b' • FF b' := by
    intro a
    rw [← hmapE a, hrel a, map_sum]
    exact Finset.sum_congr rfl fun b' _ => by rw [map_smul, hmapF b']
  have hEEFF : krausSumₗ EE = krausSumₗ FF := krausSumₗ_eq_of_unitary_smul hu hrel'
  rw [hEE, hFF] at hEEFF
  rwa [krausSumₗ_sumElim_zero_right, krausSumₗ_sumElim_zero_left] at hEEFF

/-- **Minimal operator-sum representation, `d`-to-`d′` form** (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 8.11). Any operator-sum map `krausSumₗ E` of a family
`E : ι → (H →L[ℂ] G)` over an arbitrarily large finite index has an equal operator-sum map
`krausSumₗ F` whose family `F` is indexed by `Fin (dim G · dim H)`:
`∃ F : Fin (finrank ℂ G · finrank ℂ H) → (H →L[ℂ] G), krausSumₗ F = krausSumₗ E`.

Reduce the Choi operator `Σᵢ |vec Eᵢ⟩⟨vec Eᵢ|` on `G ⊗ H` (which has `finrank = dim G · dim H`) to
at most `finrank (G ⊗ H)` rank-one terms `Σₖ |Wₖ⟩⟨Wₖ|` by
`InnerProductSpace.exists_sum_rankOne_self_eq_fin_finrank`; un-vectorize `Fₖ = matricize b Wₖ`, so
its Choi operator equals that of `E`, and conclude by `krausSumₗ_eq_of_choi_eq`. The index is
reshaped from `Fin (finrank (G ⊗ H))` to `Fin (finrank G · finrank H)` via
`Module.finrank_tensorProduct` and `krausSumₗ_comp_equiv`. -/
theorem exists_krausSumₗ_eq_fin_finrank {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G) :
    ∃ F : Fin (Module.finrank ℂ G * Module.finrank ℂ H) → (H →L[ℂ] G),
      krausSumₗ F = krausSumₗ E := by
  classical
  set b := stdOrthonormalBasis ℂ H with hb
  have : FiniteDimensional ℂ (G ⊗[ℂ] H) := inferInstance
  obtain ⟨W, hW⟩ := InnerProductSpace.exists_sum_rankOne_self_eq_fin_finrank (𝕜 := ℂ)
    (fun i => (TensorProduct.matricize b).symm (E i))
  have hdim : Module.finrank ℂ (G ⊗[ℂ] H) = Module.finrank ℂ G * Module.finrank ℂ H := by
    rw [Module.finrank_tensorProduct]
  set F' : Fin (Module.finrank ℂ (G ⊗[ℂ] H)) → (H →L[ℂ] G) :=
    fun j => TensorProduct.matricize b (W j) with hF'
  have hEF' : krausSumₗ E = krausSumₗ F' := by
    refine krausSumₗ_eq_of_choi_eq b ?_
    rw [hW]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hF', LinearEquiv.symm_apply_apply]
  exact ⟨F' ∘ finCongr hdim.symm, by rw [krausSumₗ_comp_equiv]; exact hEF'.symm⟩

/-- **Minimal operator-sum representation on a `d`-dimensional system** (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Theorem 8.3). Any operator-sum map `krausSumₗ E` on a system
of dimension `d = finrank ℂ H` (input and output space both `H`) has an equal operator-sum map
`krausSumₗ F` whose family `F` is indexed by `Fin (d²)`:
`∃ F : Fin (finrank ℂ H ^ 2) → (H →L[ℂ] H), krausSumₗ F = krausSumₗ E`.

The `G = H` specialization of `exists_krausSumₗ_eq_fin_finrank`, with the index reshaped from
`Fin (d · d)` to `Fin (d²)` via `krausSumₗ_comp_equiv`. -/
theorem exists_krausSumₗ_eq_fin_finrank_sq {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] H) :
    ∃ F : Fin (Module.finrank ℂ H ^ 2) → (H →L[ℂ] H), krausSumₗ F = krausSumₗ E := by
  obtain ⟨F, hF⟩ := exists_krausSumₗ_eq_fin_finrank E
  have hsq : Module.finrank ℂ H ^ 2 = Module.finrank ℂ H * Module.finrank ℂ H := pow_two _
  exact ⟨F ∘ finCongr hsq, by rw [krausSumₗ_comp_equiv]; exact hF⟩

end ContinuousLinearMap
