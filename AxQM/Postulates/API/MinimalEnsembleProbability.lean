/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MinimalEnsembleExistence
import AxQM.Postulates.API.PseudoInverse

/-!
# AxQM — the probability formula for a minimal ensemble (N&C Ex 2.73)

Nielsen & Chuang, Exercise 2.73, second part: *in any minimal ensemble `{pᵢ, |ψᵢ⟩}` for `ρ` the
weight of each state is*
`pᵢ = 1 / ⟨ψᵢ|ρ⁻¹|ψᵢ⟩`,
where `ρ⁻¹` is the pseudo-inverse (`State.pseudoInverse`). This file proves that identity in terms
of the state vectors, and names the real matrix element `⟨ψ|ρ⁻¹|ψ⟩`
(`State.pseudoInverseExpectation`) so that `AxQM/NC/Ch2/Exercise2_73.lean` can state the formula
for states.

## The proof

Both the given minimal ensemble `e` and the reduced eigenensemble `r = ρ.reducedEigenEnsemble` have
`rank ρ` elements and generate `ρ`, so Nielsen–Chuang Theorem 2.6
(`Ensemble.toState_op_eq_iff_unitarilyRelated`, in the equal-size form) supplies a
`rank ρ × rank ρ` unitary `u` relating their subnormalized vectors,
`|ψ̃ᵢ⟩ = ∑ⱼ uᵢⱼ |b̃ⱼ⟩` with `|b̃ⱼ⟩ = √μⱼ|gⱼ⟩`.

The reduced-eigen subnormalized vectors are **`ρ⁻¹`-orthonormal**:
`⟨b̃ₐ|ρ⁻¹|b̃_b⟩ = δₐ_b` (`reducedEigenEnsemble_inner_pseudoInverse_tildeVec`), because
`ρ⁻¹|gⱼ⟩ = μⱼ⁻¹|gⱼ⟩` and `√μₐ·√μ_b·μ_b⁻¹·⟨gₐ|g_b⟩ = δₐ_b`. Hence
`⟨ψ̃ᵢ|ρ⁻¹|ψ̃ᵢ⟩ = ∑ₖ |uᵢₖ|² = 1` (a row of a unitary matrix has unit norm), and since
`|ψ̃ᵢ⟩ = √pᵢ|ψᵢ⟩` this reads `pᵢ·⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = 1`.

## Main definitions

* `AxQM.State.pseudoInverseExpectation` — the real matrix element `⟨ψ|ρ⁻¹|ψ⟩` of the
  pseudo-inverse, `re ⟪ψ, ρ⁻¹ ψ⟫`.
* `AxQM.PureState.MemSupport` — the predicate `|ψ⟩ ∈ support ρ`.

## Main results

* `State.reducedEigenEnsemble_inner_pseudoInverse_tildeVec` — the reduced-eigen subnormalized
  vectors are `ρ⁻¹`-orthonormal.
* `Ensemble.IsMinimalFor.prob_mul_inner_pseudoInverse_eq_one` — **Exercise 2.73 (probability):**
  `pᵢ · ⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = 1` in every minimal ensemble, as an inner product of state vectors.
* `Ensemble.IsMinimalFor.pseudoInverseExpectation_eq_inv_prob` — the same as
  `⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = pᵢ⁻¹`, stated with `State.pseudoInverseExpectation`.

The statements of Exercise 2.73 are in `AxQM/NC/Ch2/Exercise2_73.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **The reduced-eigen subnormalized vectors are `ρ⁻¹`-orthonormal** (Nielsen–Chuang Exercise
2.73): `⟨b̃ₐ|ρ⁻¹|b̃_b⟩ = δₐ_b`, where `b̃ⱼ = √μⱼ|gⱼ⟩` are the subnormalized vectors of the reduced
eigenensemble. Since `gⱼ` is an eigenvector with non-zero eigenvalue `μⱼ`, `ρ⁻¹|gⱼ⟩ = μⱼ⁻¹|gⱼ⟩`, so
`⟨b̃ₐ|ρ⁻¹|b̃_b⟩ = √μₐ·√μ_b·μ_b⁻¹·⟨gₐ|g_b⟩`, which is `μₐ·μₐ⁻¹ = 1` on the diagonal (`gⱼ`
orthonormal) and `0` off it. The `ρ⁻¹`-inner-product analogue of the orthonormality of the reduced
eigenbasis, the mechanism turning the unitary relation into the row-norm sum below. -/
theorem reducedEigenEnsemble_inner_pseudoInverse_tildeVec (ρ : State S) (a b : Fin ρ.rank) :
    inner ℂ (ρ.reducedEigenEnsemble.tildeVec a)
      (ρ.pseudoInverse (ρ.reducedEigenEnsemble.tildeVec b)) = if a = b then 1 else 0 := by
  rw [show ρ.reducedEigenEnsemble.tildeVec a
        = (Real.sqrt (ρ.isDensity.isSymmetric.eigenvalues rfl (ρ.eigenIndexEquiv a).val) : ℂ)
          • ρ.isDensity.isSymmetric.eigenvectorBasis rfl (ρ.eigenIndexEquiv a).val from rfl,
    show ρ.reducedEigenEnsemble.tildeVec b
        = (Real.sqrt (ρ.isDensity.isSymmetric.eigenvalues rfl (ρ.eigenIndexEquiv b).val) : ℂ)
          • ρ.isDensity.isSymmetric.eigenvectorBasis rfl (ρ.eigenIndexEquiv b).val from rfl,
    map_smul, pseudoInverse_apply_eigenvectorBasis, inner_smul_left, inner_smul_right,
    inner_smul_right,
    orthonormal_iff_ite.mp (ρ.isDensity.isSymmetric.eigenvectorBasis rfl).orthonormal]
  by_cases hab : a = b
  · subst hab
    have hne : ρ.isDensity.isSymmetric.eigenvalues rfl (ρ.eigenIndexEquiv a).val ≠ 0 :=
      ρ.eigenvalues_eigenIndexEquiv_ne_zero a
    have hnn : 0 ≤ ρ.isDensity.isSymmetric.eigenvalues rfl (ρ.eigenIndexEquiv a).val :=
      ρ.isDensity.eigenvalues_nonneg rfl _
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← mul_assoc, Real.mul_self_sqrt hnn, mul_inv_cancel₀ hne,
      Complex.ofReal_one]
  · have hne : (ρ.eigenIndexEquiv a).val ≠ (ρ.eigenIndexEquiv b).val := fun heq =>
      hab (ρ.eigenIndexEquiv.injective (Subtype.ext heq))
    rw [ite_eq_right hne, ite_eq_right hab, mul_zero, mul_zero, mul_zero]

/-- **The pseudo-inverse expectation `⟨ψ|ρ⁻¹|ψ⟩`** (Nielsen–Chuang Exercise 2.73): the real matrix
element of the pseudo-inverse `ρ⁻¹` in the pure state `|ψ⟩`, `re ⟪ψ, ρ⁻¹ ψ⟫`. Real because `ρ⁻¹` is
self-adjoint; on a minimal ensemble it is `pᵢ⁻¹`
(`Ensemble.IsMinimalFor.pseudoInverseExpectation_eq_inv_prob`), so the weight of each state is its
reciprocal, `pᵢ = 1/⟨ψᵢ|ρ⁻¹|ψᵢ⟩`. -/
def pseudoInverseExpectation (ρ : State S) (ψ : PureState S) : ℝ :=
  (inner ℂ ψ.vec (ρ.pseudoInverse ψ.vec)).re

end State

namespace PureState

/-- **A pure state lies in the support of `ρ`** (Nielsen–Chuang Exercise 2.73): `|ψ⟩ ∈ support ρ`.
This is the hypothesis of the existence part of the exercise: the state vector `ψ.vec` lies in the
support of the density operator. -/
def MemSupport (ψ : PureState S) (ρ : State S) : Prop :=
  ψ.vec ∈ ρ.support

end PureState

namespace Ensemble

/-- **Exercise 2.73 (probability formula)** (Nielsen–Chuang): in any minimal ensemble
`{pᵢ, |ψᵢ⟩}` for `ρ`, each weight satisfies `pᵢ · ⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = 1`.

Both `e` and the reduced eigenensemble `r` have `rank ρ` elements and generate `ρ`, so Theorem 2.6
(`toState_op_eq_iff_unitarilyRelated`) gives a unitary `u` with `|ψ̃ᵢ⟩ = ∑ⱼ uᵢⱼ|b̃ⱼ⟩`. Then, by the
`ρ⁻¹`-orthonormality of the `b̃ⱼ` (`State.reducedEigenEnsemble_inner_pseudoInverse_tildeVec`),
`⟨ψ̃ᵢ|ρ⁻¹|ψ̃ᵢ⟩ = ∑ₖ conj(uᵢₖ)·uᵢₖ = 1` (the `i`-th diagonal entry of `u·u† = 1`); expanding
`|ψ̃ᵢ⟩ = √pᵢ|ψᵢ⟩` turns this into `pᵢ · ⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = 1`. -/
theorem IsMinimalFor.prob_mul_inner_pseudoInverse_eq_one {e : Ensemble S} {ρ : State S}
    (hmin : e.IsMinimalFor ρ) (i : Fin e.card) :
    (e.prob i : ℂ) * inner ℂ (e.states i).vec (ρ.pseudoInverse (e.states i).vec) = 1 := by
  classical
  -- `e` and the reduced eigenensemble have the same size and both generate `ρ`
  have hcard : e.card = ρ.reducedEigenEnsemble.card :=
    hmin.2.trans ρ.reducedEigenEnsemble_card.symm
  have hop : e.toState.op = ρ.reducedEigenEnsemble.toState.op := by
    rw [hmin.1, ρ.reducedEigenEnsemble_toState]
  -- Theorem 2.6: a unitary relates the subnormalized vectors
  obtain ⟨hc, u, hu, hrel⟩ := (Ensemble.toState_op_eq_iff_unitarilyRelated hcard).mp hop
  -- the `i`-th row of `u` has unit norm: `∑ₖ uᵢₖ·conj(uᵢₖ) = 1`
  have hunit : ∑ k, u i k * (starRingEnd ℂ) (u i k) = 1 := by
    have h2 : (u * star u) i i = 1 := by
      rw [Matrix.mem_unitaryGroup_iff.mp hu]; exact Matrix.one_apply_eq i
    rw [Matrix.mul_apply] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.star_apply, starRingEnd_apply]
  -- the reduced-eigen subnormalized vectors, reindexed along the size equality, stay `ρ⁻¹`-ON
  have hw : ∀ a b : Fin e.card,
      inner ℂ (ρ.reducedEigenEnsemble.tildeVec (Fin.cast hc a))
        (ρ.pseudoInverse (ρ.reducedEigenEnsemble.tildeVec (Fin.cast hc b)))
        = if a = b then 1 else 0 := by
    intro a b
    have hpt := State.reducedEigenEnsemble_inner_pseudoInverse_tildeVec ρ (Fin.cast hc a)
      (Fin.cast hc b)
    refine hpt.trans ?_
    by_cases h : a = b
    · subst h; simp
    · rw [ite_eq_right h]
      exact ite_eq_right (fun heq => h ((Fin.cast_inj hc).mp heq))
  -- `⟨ψ̃ᵢ|ρ⁻¹|ψ̃ᵢ⟩ = ∑ₖ uᵢₖ·conj(uᵢₖ) = 1`
  have hstep : inner ℂ (e.tildeVec i) (ρ.pseudoInverse (e.tildeVec i)) = 1 := by
    rw [hrel i]
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hw,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hunit
  -- unfold `|ψ̃ᵢ⟩ = √pᵢ|ψᵢ⟩` to read off the weight
  rw [show e.tildeVec i = (Real.sqrt (e.prob i) : ℂ) • (e.states i).vec from rfl, map_smul,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (e.prob_nonneg i)] at hstep
  exact hstep

/-- **Exercise 2.73 (probability formula), for states** (Nielsen–Chuang): the pseudo-inverse
expectation of each state of a minimal ensemble is the reciprocal of its weight,
`⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = pᵢ⁻¹`. From `prob_mul_inner_pseudoInverse_eq_one` (`pᵢ·⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = 1`) the complex
inner product equals `(pᵢ⁻¹ : ℝ)`, whose real part is `pᵢ⁻¹`; this gives the exercise's
`pᵢ = 1/⟨ψᵢ|ρ⁻¹|ψᵢ⟩`. -/
theorem IsMinimalFor.pseudoInverseExpectation_eq_inv_prob {e : Ensemble S} {ρ : State S}
    (hmin : e.IsMinimalFor ρ) (i : Fin e.card) :
    ρ.pseudoInverseExpectation (e.states i) = (e.prob i)⁻¹ := by
  have hp : (e.prob i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hmin.prob_pos i))
  have hpr : e.prob i ≠ 0 := ne_of_gt (hmin.prob_pos i)
  have hinner : inner ℂ (e.states i).vec (ρ.pseudoInverse (e.states i).vec)
      = ((e.prob i)⁻¹ : ℝ) := by
    apply mul_left_cancel₀ hp
    rw [hmin.prob_mul_inner_pseudoInverse_eq_one i, ← Complex.ofReal_mul, mul_inv_cancel₀ hpr,
      Complex.ofReal_one]
  simp only [State.pseudoInverseExpectation, hinner, Complex.ofReal_re]

end Ensemble

end AxQM
