/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Freedom in the operator-sum representation

General API for the operator-sum (Kraus) map `ContinuousLinearMap.krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†`
(defined in `ToMathlib.Analysis.InnerProductSpace.OperatorSum`) describing how the map behaves under
the natural reshapings of its family of operation elements. These are the structural facts behind
the "freedom in the operator-sum representation" of a quantum operation
(Nielsen & Chuang, *Quantum Computation and Quantum Information*, §8.2):

* `ContinuousLinearMap.krausSumₗ_comp_equiv` — **reindexing invariance**: reindexing the family by a
  bijection leaves the operator-sum map unchanged, `krausSumₗ (F ∘ e) = krausSumₗ F`.
* `ContinuousLinearMap.krausSumₗ_sumElim` — **additivity**: the operator-sum map of a concatenated
  family is the sum, `krausSumₗ (Sum.elim E F) = krausSumₗ E + krausSumₗ F`.
* `ContinuousLinearMap.krausSumₗ_const_zero` — the all-zero family induces the zero map, and its
  corollaries `krausSumₗ_sumElim_zero_right` / `_left` — appending zero operators is neutral (the
  "append zeros" padding used to bring two families to a common index).
* `ContinuousLinearMap.krausSumₗ_eq_of_unitary_smul` — **unitary freedom** (the "⟸" direction of
  Nielsen & Chuang Theorem 8.2): two families over a common index related by a unitary coefficient
  matrix, `Eₐ = Σ_b uₐ_b • F_b`, induce the same operator-sum map.

## Implementation notes

This general `krausSumₗ` API is kept in its own file, imported by consumers such as the minimal
operator-sum representation (`ToMathlib.Analysis.InnerProductSpace.MinimalOperatorSum`, Nielsen &
Chuang Theorem 8.3), rather than in the definitional file `OperatorSum.lean`. The full
characterization of Nielsen & Chuang Theorem 8.2 (both directions of the unitary-freedom `iff`) is a
separate development, `OperatorSum.krausSumₗ_eq_iff_exists_mem_unitaryGroup`, whose "⟸" direction
`krausSumₗ_eq_of_mem_unitaryGroup` is stated for a **same input/output** space (`H →L[ℂ] H`). The
`krausSumₗ_eq_of_unitary_smul` here is its input≠output generalization (`H →L[ℂ] G`), needed for the
`d`-to-`d′` minimal representation (Exercise 8.11); it is kept — not folded away — precisely because
it is strictly more general.
-/

@[expose] public section

open scoped InnerProductSpace
open ContinuousLinearMap

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Reindexing invariance of the operator-sum map.** Reindexing a family of operation elements by
a bijection `e : κ ≃ ι` leaves its operator-sum map unchanged: `krausSumₗ (F ∘ e) = krausSumₗ F`.
The operator-sum map is a sum over the index, so `Equiv.sum_comp e` re-labels the summands. -/
theorem krausSumₗ_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    (F : ι → H →L[ℂ] G) : krausSumₗ (F ∘ e) = krausSumₗ F := by
  refine LinearMap.ext fun ρ => ?_
  simp only [krausSumₗ_apply, Function.comp_apply]
  exact Equiv.sum_comp e (fun j => F j ∘L ρ ∘L adjoint (F j))

/-- **Additivity of the operator-sum map over concatenation.** The operator-sum map of the
concatenated family `Sum.elim E F` (over the index `ι ⊕ κ`) is the sum of the two operator-sum maps:
`krausSumₗ (Sum.elim E F) = krausSumₗ E + krausSumₗ F`. Immediate from splitting the sum over
`ι ⊕ κ` (`Fintype.sum_sum_type`). -/
theorem krausSumₗ_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι → H →L[ℂ] G)
    (F : κ → H →L[ℂ] G) : krausSumₗ (Sum.elim E F) = krausSumₗ E + krausSumₗ F := by
  refine LinearMap.ext fun ρ => ?_
  simp only [krausSumₗ_apply, LinearMap.add_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]

/-- The all-zero family of operation elements induces the zero operator-sum map:
`krausSumₗ (fun _ => 0) = 0`. Each summand `0 ρ 0† = 0`. -/
theorem krausSumₗ_const_zero {ι : Type*} [Fintype ι] :
    krausSumₗ (fun _ : ι => (0 : H →L[ℂ] G)) = 0 := by
  refine LinearMap.ext fun ρ => ?_
  simp [krausSumₗ_apply]

/-- Appending zero operation elements on the right of a family does not change its operator-sum map:
`krausSumₗ (Sum.elim E 0) = krausSumₗ E`. The `F = 0` case of additivity (`krausSumₗ_sumElim`). -/
theorem krausSumₗ_sumElim_zero_right {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι → H →L[ℂ] G) :
    krausSumₗ (Sum.elim E (fun _ : κ => (0 : H →L[ℂ] G))) = krausSumₗ E := by
  rw [krausSumₗ_sumElim, krausSumₗ_const_zero, add_zero]

/-- Appending zero operation elements on the left of a family does not change its operator-sum map:
`krausSumₗ (Sum.elim 0 F) = krausSumₗ F`. The `E = 0` case of additivity (`krausSumₗ_sumElim`). -/
theorem krausSumₗ_sumElim_zero_left {ι κ : Type*} [Fintype ι] [Fintype κ] (F : κ → H →L[ℂ] G) :
    krausSumₗ (Sum.elim (fun _ : ι => (0 : H →L[ℂ] G)) F) = krausSumₗ F := by
  rw [krausSumₗ_sumElim, krausSumₗ_const_zero, zero_add]

/-- **Unitary freedom in the operator-sum representation** (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, Theorem 8.2, "⟸" direction). If two finite families of operation elements
`E F : J → (H →L[ℂ] G)` over a common index are related by a unitary coefficient matrix
`u ∈ Matrix.unitaryGroup J ℂ`, `Eₐ = Σ_b uₐ_b • F_b`, then they induce the same operator-sum map:
`krausSumₗ E = krausSumₗ F`.

Expanding `Eₐ ρ Eₐ†` bilinearly gives `Σ_b Σ_c (uₐ_b · conj uₐ_c) • (F_b ρ F_c†)`; summing over `a`
collapses the coefficient `Σₐ conj uₐ_c · uₐ_b = (u⋆ u)_c_b = δ_c_b` by unitarity, leaving
`Σ_b F_b ρ F_b†`. This generalizes `ContinuousLinearMap.krausSumₗ_eq_of_mem_unitaryGroup` from the
same input/output space `H →L[ℂ] H` to an arbitrary output space `H →L[ℂ] G`. -/
theorem krausSumₗ_eq_of_unitary_smul {J : Type*} [Fintype J] [DecidableEq J]
    {u : Matrix J J ℂ} (hu : u ∈ Matrix.unitaryGroup J ℂ) {E F : J → H →L[ℂ] G}
    (hEF : ∀ a, E a = ∑ b, u a b • F b) :
    krausSumₗ E = krausSumₗ F := by
  have key : ∀ b c : J, (∑ a, (starRingEnd ℂ) (u a c) * u a b) = if c = b then (1 : ℂ) else 0 := by
    intro b c
    have h1 : (star u * u : Matrix J J ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    have h2 := congrFun (congrFun h1 c) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.star_apply, starRingEnd_apply]
  refine LinearMap.ext fun ρ => ?_
  simp only [krausSumₗ_apply, hEF, map_sum, map_smulₛₗ, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, Finset.smul_sum, smul_smul]
  calc ∑ a, ∑ c, ∑ b, ((starRingEnd ℂ) (u a c) * u a b) • ((F b).comp (ρ.comp (adjoint (F c))))
      = ∑ c, ∑ b, ∑ a, ((starRingEnd ℂ) (u a c) * u a b) •
          ((F b).comp (ρ.comp (adjoint (F c)))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ b, (∑ a, (starRingEnd ℂ) (u a c) * u a b) •
          ((F b).comp (ρ.comp (adjoint (F c)))) := by
        simp only [Finset.sum_smul]
    _ = ∑ c, ∑ b, (if c = b then (1 : ℂ) else 0) • ((F b).comp (ρ.comp (adjoint (F c)))) := by
        simp only [key]
    _ = ∑ b, (F b).comp (ρ.comp (adjoint (F b))) := by
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end ContinuousLinearMap
