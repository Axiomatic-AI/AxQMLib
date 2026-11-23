/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.MatricizationRank
import AxQM.Postulates.API.SchmidtNumber
import AxQM.Postulates.API.CompositeState
import AxQM.NC.Ch2.Problem2_2
import AxQM.NC.Ch2.Exercise2_74

/-!
# Nielsen & Chuang, Exercise 2.78 (product states, Schmidt number 1, and pure marginals)

Prove |psi> is a product state iff Schmidt number 1 iff rho^A pure.

The exercise establishes the equivalence, for a bipartite **pure** state `|ψ⟩`, of

* `|ψ⟩` is a **product state** `|a⟩|b⟩`;
* `|ψ⟩` has **Schmidt number `1`** (a single non-zero Schmidt coefficient);
* the **reduced density operator `ρᴬ = tr_B(|ψ⟩⟨ψ|)` is pure**;
* the **reduced density operator `ρᴮ = tr_A(|ψ⟩⟨ψ|)` is pure** (the exercise's "and thus `ρᴮ`").

## Formalisation

* `PureState.IsProduct` — the separability predicate `∃ a b, ψ = a ⊗ b`, phrased over
  `PureState.tmul`, the tensor product of states, rather than via a vector-level
  `ψ.vec = a ⊗ₜ b`.
* `PureState.isProduct_iff_schmidtNumber_eq_one` — `|ψ⟩` is a product state ↔ `Sch(ψ) = 1`.
* `PureState.isProduct_iff_isPure_reducedLeft` — `|ψ⟩` is a product state ↔ `ρᴬ` is pure.
* `PureState.isProduct_iff_isPure_reducedRight` — `|ψ⟩` is a product state ↔ `ρᴮ` is pure (the
  exercise's parenthetical "and thus `ρᴮ`", formalised in full rather than left to symmetry).

The exercise is assembled from the following results:

* the marginal-of-a-product facts `isPure_reducedLeft_toState_tmul` /
  `isPure_reducedRight_toState_tmul` (`ρᴬ = |a⟩⟨a|`, `ρᴮ = |b⟩⟨b|`) —
  `AxQM/NC/Ch2/Exercise2_74.lean`;
* the Schmidt-number/rank bridges `schmidtNumber_eq_rank_reducedLeft` /
  `schmidtNumber_eq_rank_reducedRight` (Problem 2.2(1) and its right mirror) —
  `AxQM/NC/Ch2/Problem2_2.lean`;
* the general facts `one_le_schmidtNumber` (`Sch(ψ) ≥ 1`) and `State.rank_eq_one_of_isPure`
  (a pure state has rank `1`) — `AxQM/Postulates/API/SchmidtNumber.lean`;
* the pure linear-algebra lemma `TensorProduct.exists_tmul_of_finrank_range_matricize_le_one`
  (rank-`≤ 1` matricization ⇒ simple tensor) —
  `ToMathlib/Analysis/InnerProductSpace/MatricizationRank.lean`.

## Design and proof

The equivalence pivots on the Schmidt number, through the bridges to both marginals
`Sch(ψ) = rank ρᴬ` (Problem 2.2(1)) and `Sch(ψ) = rank ρᴮ` (its right mirror).

* **Product ↔ Schmidt number 1.**
  *(→)* If `ψ = a ⊗ b` then `ψ.vec = a.vec ⊗ₜ b.vec` is a one-term product, so
  `Sch(ψ) ≤ 1` (`schmidtNumber_le_card_of_sum_tmul`, Problem 2.2(2), over a singleton); with
  `Sch(ψ) ≥ 1` (`one_le_schmidtNumber`) this forces `Sch(ψ) = 1`.
  *(←)* If `Sch(ψ) = 1` then `matricize ψ.vec` is a rank-`≤ 1` operator, so
  `ψ.vec = x ⊗ₜ y` is a simple tensor (`exists_tmul_of_finrank_range_matricize_le_one`). Since
  `‖ψ.vec‖ = 1`, `‖x‖‖y‖ = 1`, so `x`, `y` are non-zero and their normalisations `a = x/‖x‖`,
  `b = y/‖y‖` satisfy `ψ = a ⊗ b` (the two `‖·‖⁻¹` factors cancel against `‖x‖‖y‖ = 1`).

* **Product ↔ `ρᴬ` pure** and **Product ↔ `ρᴮ` pure.** Both are symmetric.
  *(→)* the marginals of a product pure state are `|a⟩⟨a|`, `|b⟩⟨b|` (Exercise 2.74 and its right
  mirror).
  *(←)* chains purity through the rank: `ρᴬ` (resp. `ρᴮ`) pure ⇒ `rank = 1`
  (`State.rank_eq_one_of_isPure`) ⇒ `Sch(ψ) = 1` (`schmidtNumber_eq_rank_reducedLeft` /
  `schmidtNumber_eq_rank_reducedRight`) ⇒ product. This routing avoids the harder spectral direction
  `rank ρ = 1 ⇒ ρ` pure, which the exercise does not need.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- A bipartite pure state `|ψ⟩` of `S ⊗ T` is a **product state** when it factors as `|a⟩|b⟩` for
pure states `a` of `S` and `b` of `T` — i.e. `ψ = a ⊗ b` (`PureState.tmul`). -/
def PureState.IsProduct (ψ : PureState (S ⊗ T)) : Prop :=
  ∃ (a : PureState S) (b : PureState T), ψ = a.tmul b

/-- **Nielsen & Chuang, Exercise 2.78 (first equivalence).** A bipartite pure state `|ψ⟩` is a
product state if and only if it has Schmidt number `1`. Forward: a product `ψ.vec = a.vec ⊗ₜ b.vec`
is a single-term decomposition, so `Sch(ψ) ≤ 1`, and `Sch(ψ) ≥ 1` (`one_le_schmidtNumber`) gives
equality. Backward: `Sch(ψ) = 1` makes `matricize ψ.vec` rank-`≤ 1`, hence `ψ.vec` a simple tensor
`x ⊗ₜ y` (`exists_tmul_of_finrank_range_matricize_le_one`); normalising `x`, `y` (whose norms
multiply to `1`) yields the product factorisation. -/
theorem PureState.isProduct_iff_schmidtNumber_eq_one (ψ : PureState (S ⊗ T)) :
    ψ.IsProduct ↔ ψ.schmidtNumber = 1 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine le_antisymm ?_ (a.tmul b).one_le_schmidtNumber
    calc (a.tmul b).schmidtNumber
        ≤ (Finset.univ : Finset Unit).card :=
          PureState.schmidtNumber_le_card_of_sum_tmul _ _ (fun _ => a.vec) (fun _ => b.vec)
            (by simp only [PureState.tmul_vec, Finset.univ_unique, Finset.sum_singleton]; rfl)
      _ = 1 := by simp
  · intro h
    set bT := stdOrthonormalBasis ℂ T.space with hbT
    have hle : Module.finrank ℂ ↥(LinearMap.range
        (TensorProduct.matricize bT (ψ.vec : S.space ⊗[ℂ] T.space)).toLinearMap) ≤ 1 := by
      have hop : TensorProduct.matricize bT (ψ.vec : S.space ⊗[ℂ] T.space) = ψ.schmidtOp := by
        rw [hbT]; rfl
      rw [hop, ← ψ.schmidtNumber_eq_finrank_range_matricize]
      exact h.le
    obtain ⟨x, y, hxy⟩ := @TensorProduct.exists_tmul_of_finrank_range_matricize_le_one
      ℂ S.space T.space _ _ _ _ _ _ _ _ (ψ.vec : S.space ⊗[ℂ] T.space) bT hle
    have hnorm : ‖x‖ * ‖y‖ = 1 := by
      rw [← TensorProduct.norm_tmul (𝕜 := ℂ) x y, ← hxy]; exact ψ.normalized
    have hnx : x ≠ 0 := norm_ne_zero_iff.mp (left_ne_zero_of_mul_eq_one hnorm)
    have hny : y ≠ 0 := norm_ne_zero_iff.mp (right_ne_zero_of_mul_eq_one hnorm)
    have hc1 : (((‖x‖ : ℝ) : ℂ)⁻¹ * ((‖y‖ : ℝ) : ℂ)⁻¹) = 1 := by
      rw [← mul_inv, ← Complex.ofReal_mul, hnorm, Complex.ofReal_one, inv_one]
    refine ⟨PureState.normalize x hnx, PureState.normalize y hny, ?_⟩
    apply PureState.ext
    rw [hxy, PureState.tmul_vec, PureState.normalize_vec, PureState.normalize_vec,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, hc1, one_smul]

/-- **Nielsen & Chuang, Exercise 2.78 (second equivalence).** A bipartite pure state `|ψ⟩` is a
product state if and only if its reduced density operator `ρᴬ = tr_B(|ψ⟩⟨ψ|)` is pure. Forward is
Exercise 2.74 (the marginal of a product pure state is `|a⟩⟨a|`). Backward chains purity through the
rank: `ρᴬ` pure ⇒ `rank ρᴬ = 1` (`State.rank_eq_one_of_isPure`) ⇒ `Sch(ψ) = 1`
(`schmidtNumber_eq_rank_reducedLeft`) ⇒ product (the first equivalence). -/
theorem PureState.isProduct_iff_isPure_reducedLeft (ψ : PureState (S ⊗ T)) :
    ψ.IsProduct ↔ ψ.toState.reducedLeft.IsPure := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact isPure_reducedLeft_toState_tmul a b
  · intro h
    rw [ψ.isProduct_iff_schmidtNumber_eq_one, ψ.schmidtNumber_eq_rank_reducedLeft]
    exact State.rank_eq_one_of_isPure h

/-- **Nielsen & Chuang, Exercise 2.78 (second equivalence, `ρᴮ` form — the "and thus `ρᴮ`").** A
bipartite pure state `|ψ⟩` is a product state if and only if its reduced density operator
`ρᴮ = tr_A(|ψ⟩⟨ψ|)` is pure. Symmetric to `isProduct_iff_isPure_reducedLeft`: forward is
`isPure_reducedRight_toState_tmul` (Exercise 2.74's right mirror), backward chains `ρᴮ` pure ⇒
`rank ρᴮ = 1` (`State.rank_eq_one_of_isPure`) ⇒ `Sch(ψ) = 1` (`schmidtNumber_eq_rank_reducedRight`)
⇒ product. -/
theorem PureState.isProduct_iff_isPure_reducedRight (ψ : PureState (S ⊗ T)) :
    ψ.IsProduct ↔ ψ.toState.reducedRight.IsPure := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact isPure_reducedRight_toState_tmul a b
  · intro h
    rw [ψ.isProduct_iff_schmidtNumber_eq_one, ψ.schmidtNumber_eq_rank_reducedRight]
    exact State.rank_eq_one_of_isPure h

end AxQM
