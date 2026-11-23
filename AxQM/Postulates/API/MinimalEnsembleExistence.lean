/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MinimalEnsemble
import ToMathlib.Analysis.InnerProductSpace.Trace
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# AxQM — a minimal ensemble through a prescribed support vector

Nielsen & Chuang, Exercise 2.73, first part: *for any state `|ψ⟩` in the support of `ρ` there is a
minimal ensemble for `ρ` that contains `|ψ⟩`.* This file proves that existence
(`AxQM.exists_isMinimalFor_mem_of_mem_support`).

## The construction

The reduced eigenensemble (`State.reducedEigenEnsemble`) is a minimal ensemble whose subnormalized
vectors `|b̃ⱼ⟩ = √μⱼ|gⱼ⟩` (`μⱼ > 0`) span the support. By the unitary freedom in the ensemble
(Nielsen–Chuang Theorem 2.6), applying **any** `rank ρ × rank ρ` unitary `u` to these vectors —
`|ψ̃ᵢ⟩ = ∑ⱼ uᵢⱼ|b̃ⱼ⟩` — yields another family of subnormalized vectors generating the same `ρ`
(`InnerProductSpace.sum_rankOne_self_eq_of_mem_unitaryGroup`), hence another minimal ensemble.

To land `|ψ⟩` in the ensemble we choose `u`'s first row so that `|ψ̃₀⟩ ∝ |ψ⟩`. Writing
`ψ = ∑ⱼ ⟨gⱼ, ψ⟩ gⱼ` (`State.sum_reducedEigen_inner_smul_eq_of_mem_support`, valid because `ψ` is in
the support), the coefficient vector `aⱼ = ⟨gⱼ, ψ⟩ / √μⱼ` satisfies `∑ⱼ aⱼ|b̃ⱼ⟩ = ψ`; its
normalization `w = a/‖a‖` is a unit vector, which is the first row of a unitary `u`
(`EuclideanSpace.exists_mem_unitaryGroup_row_zero_eq`, the general "complete a unit vector to a
unitary matrix" fact, in `ToMathlib/`). Then `|ψ̃₀⟩ = ‖a‖⁻¹|ψ⟩`, which normalizes back to
`|ψ⟩`.

## Main definitions

* `AxQM.Ensemble.ofSubnormalized` — the ensemble read off from a family of subnormalized
  vectors `vᵢ` whose rank-one sum is a density operator `ρ` (`∑ᵢ |vᵢ⟩⟨vᵢ| = ρ`): weights `‖vᵢ‖²`
  and states `vᵢ/‖vᵢ‖` (a fixed default at the zero vectors, which carry weight `0`).

## Main results

* `AxQM.Ensemble.ofSubnormalized_toState` — it generates `ρ`.
* `AxQM.State.sum_reducedEigen_inner_smul_eq_of_mem_support` — a support vector
  reconstructs over the reduced eigenbasis, `ψ = ∑ⱼ ⟨gⱼ, ψ⟩ gⱼ`.
* `AxQM.exists_isMinimalFor_mem_of_mem_support` — **Exercise 2.73 (existence):** a state in
  the support of `ρ` lies in some minimal ensemble for `ρ`.

The statement of Exercise 2.73 is in `AxQM/NC/Ch2/Exercise2_73.lean`, and the probability formula
is proved separately in `AxQM/Postulates/API/MinimalEnsembleProbability.lean`.
-/

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- **The ensemble read off from a family of subnormalized vectors** whose rank-one projectors sum
to a density operator `ρ` (`∑ᵢ |vᵢ⟩⟨vᵢ| = ρ`, `hv`). Its weights are `pᵢ = ‖vᵢ‖²` and its pure
states the normalized vectors `vᵢ/‖vᵢ‖`, with a fixed default `d` at the zero vectors (which carry
weight `0`, so they do not affect the density operator). The subnormalized vectors of the resulting
ensemble are exactly the `vᵢ` (`ofSubnormalized_tildeVec`), so it generates `ρ`
(`ofSubnormalized_toState`). -/
def ofSubnormalized {n : ℕ} (v : Fin n → S.space) (ρ : State S)
    (hv : ∑ i, rankOne ℂ (v i) (v i) = ρ.op) (d : PureState S) : Ensemble S where
  card := n
  prob i := ‖v i‖ ^ 2
  states i :=
    if h : ‖v i‖ = 0 then d
    else ⟨(‖v i‖ : ℂ)⁻¹ • v i, by
      rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ h]⟩
  prob_nonneg i := sq_nonneg _
  sum_prob := by
    have hcoe : ∀ i, (LinearMap.trace ℂ S.space)
        (↑(rankOne ℂ (v i) (v i)) : S.space →ₗ[ℂ] S.space) = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [trace_rankOne, inner_self_eq_norm_sq_to_K]
      norm_cast
    have key : ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      calc ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ)
          = ∑ i, (LinearMap.trace ℂ S.space)
              (↑(rankOne ℂ (v i) (v i)) : S.space →ₗ[ℂ] S.space) :=
            Finset.sum_congr rfl fun i _ => (hcoe i).symm
        _ = (LinearMap.trace ℂ S.space)
              (↑(∑ i, rankOne ℂ (v i) (v i)) : S.space →ₗ[ℂ] S.space) := by
            rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
        _ = (LinearMap.trace ℂ S.space) (↑ρ.op : S.space →ₗ[ℂ] S.space) := by rw [hv]
        _ = 1 := ρ.trace_op_eq_one
    exact_mod_cast key

@[simp]
theorem ofSubnormalized_card {n : ℕ} (v : Fin n → S.space) (ρ : State S)
    (hv : ∑ i, rankOne ℂ (v i) (v i) = ρ.op) (d : PureState S) :
    (ofSubnormalized v ρ hv d).card = n := rfl

theorem ofSubnormalized_states_vec_of_ne_zero {n : ℕ} (v : Fin n → S.space) (ρ : State S)
    (hv : ∑ i, rankOne ℂ (v i) (v i) = ρ.op) (d : PureState S) {i : Fin n} (hi : v i ≠ 0) :
    ((ofSubnormalized v ρ hv d).states i).vec = (‖v i‖ : ℂ)⁻¹ • v i := by
  simp only [ofSubnormalized, dite_eq_right (norm_ne_zero_iff.mpr hi)]

/-- **The subnormalized vectors of `ofSubnormalized` are the input vectors** `vᵢ`. On a non-zero
`vᵢ` the weight `√(‖vᵢ‖²) = ‖vᵢ‖` cancels the normalization `‖vᵢ‖⁻¹`; on a zero `vᵢ` the weight is
`0`. -/
theorem ofSubnormalized_tildeVec {n : ℕ} (v : Fin n → S.space) (ρ : State S)
    (hv : ∑ i, rankOne ℂ (v i) (v i) = ρ.op) (d : PureState S) (i : Fin n) :
    (ofSubnormalized v ρ hv d).tildeVec i = v i := by
  rcases eq_or_ne (v i) 0 with h | h
  · have hp : (ofSubnormalized v ρ hv d).prob i = 0 := by simp [ofSubnormalized, h]
    unfold tildeVec
    rw [hp, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, h]
  · unfold tildeVec
    rw [ofSubnormalized_states_vec_of_ne_zero v ρ hv d h]
    change (Real.sqrt (‖v i‖ ^ 2) : ℂ) • ((‖v i‖ : ℂ)⁻¹ • v i) = v i
    rw [Real.sqrt_sq (norm_nonneg _), smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), Complex.ofReal_one, one_smul]

/-- **`ofSubnormalized` generates `ρ`.** Its density operator is `∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|` with the
subnormalized vectors equal to the input `vᵢ` (`ofSubnormalized_tildeVec`), which sum to `ρ` by
hypothesis. -/
theorem ofSubnormalized_toState {n : ℕ} (v : Fin n → S.space) (ρ : State S)
    (hv : ∑ i, rankOne ℂ (v i) (v i) = ρ.op) (d : PureState S) :
    (ofSubnormalized v ρ hv d).toState = ρ := by
  refine State.ext ?_
  rw [toState_op_eq_sum_rankOne_tildeVec, ← hv]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun x => rankOne ℂ x x) (ofSubnormalized_tildeVec v ρ hv d i)

end Ensemble

namespace State

/-- **A support vector reconstructs over the reduced eigenbasis** (Nielsen–Chuang Exercise 2.73): if
`ψ ∈ support ρ` then `ψ = ∑ⱼ ⟨gⱼ, ψ⟩ gⱼ`, the sum over the reduced eigenensemble's states `gⱼ`
(eigenvectors with non-zero eigenvalue). The full eigenbasis reconstruction `ψ = ∑ₖ ⟨bₖ, ψ⟩ bₖ`
(`OrthonormalBasis.sum_repr'`) drops its zero-eigenvalue terms because a support vector is
orthogonal
to those eigenvectors (`inner_eigenvectorBasis_eq_zero_of_mem_support`), leaving the reduced sum
(`sum_eigenIndexEquiv`). -/
theorem sum_reducedEigen_inner_smul_eq_of_mem_support (ρ : State S) {ψ : S.space}
    (hψ : ψ ∈ ρ.support) :
    ∑ j, inner ℂ (ρ.reducedEigenEnsemble.states j).vec ψ •
      (ρ.reducedEigenEnsemble.states j).vec = ψ := by
  have hf : ∀ k, ρ.isDensity.isSymmetric.eigenvalues rfl k = 0 →
      inner ℂ (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k) ψ •
        ρ.isDensity.isSymmetric.eigenvectorBasis rfl k = (0 : S.space) := by
    intro k hk
    rw [ρ.inner_eigenvectorBasis_eq_zero_of_mem_support hψ k hk, zero_smul]
  rw [show (∑ j, inner ℂ (ρ.reducedEigenEnsemble.states j).vec ψ •
        (ρ.reducedEigenEnsemble.states j).vec)
      = ∑ j, (fun k => inner ℂ (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k) ψ •
          ρ.isDensity.isSymmetric.eigenvectorBasis rfl k) (ρ.eigenIndexEquiv j).val from rfl,
    ρ.sum_eigenIndexEquiv _ hf]
  exact (ρ.isDensity.isSymmetric.eigenvectorBasis rfl).sum_repr' ψ

end State

/-- **Nielsen–Chuang Exercise 2.73 (existence).** For a state `|ψ⟩` in the support of `ρ` there is a
*minimal* ensemble for `ρ` (size `rank ρ`, `Ensemble.IsMinimalFor`) that **contains** `|ψ⟩` (one of
its pure states is `|ψ⟩`).

The reduced eigenensemble supplies subnormalized vectors `|b̃ⱼ⟩` generating `ρ`; the coordinate
matrix `u` of an orthonormal basis whose first vector is `w = a/‖a‖` (with `aⱼ = ⟨gⱼ, ψ⟩/√μⱼ`)
is a unitary carrying `|b̃ⱼ⟩` to a new minimal family `|ψ̃ᵢ⟩ = ∑ⱼ uᵢⱼ|b̃ⱼ⟩` generating the same `ρ`
(`InnerProductSpace.sum_rankOne_self_eq_of_mem_unitaryGroup`), whose first member `|ψ̃₀⟩ = ‖a‖⁻¹|ψ⟩`
normalizes to `|ψ⟩`. -/
theorem exists_isMinimalFor_mem_of_mem_support (ρ : State S) (ψ : PureState S)
    (h : ψ.vec ∈ ρ.support) :
    ∃ e : Ensemble S, e.IsMinimalFor ρ ∧ ∃ i, (e.states i).vec = ψ.vec := by
  classical
  -- the support is non-trivial (contains the unit vector `ψ`), so `rank ρ > 0`
  have hψ0 : ψ.vec ≠ 0 := by
    intro hz; simpa [hz] using ψ.normalized
  have hr0 : 0 < ρ.rank := by
    rw [ρ.rank_eq_finrank_support]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨ψ.vec, h⟩, by
      simpa [Subtype.ext_iff] using hψ0⟩
  have : NeZero ρ.rank := ⟨hr0.ne'⟩
  -- reduced eigenensemble data
  set g : Fin ρ.rank → S.space := fun j => (ρ.reducedEigenEnsemble.states j).vec with hg
  set μ : Fin ρ.rank → ℝ := fun j => ρ.reducedEigenEnsemble.prob j with hμ
  have hμpos : ∀ j, 0 < μ j := fun j => ρ.reducedEigenEnsemble_prob_pos j
  have hbtilde : ∀ j, ρ.reducedEigenEnsemble.tildeVec j = (Real.sqrt (μ j) : ℂ) • g j :=
    fun j => rfl
  -- the coefficient function `αⱼ = ⟨gⱼ, ψ⟩ / √μⱼ` and the vector `a` it names
  set α : Fin ρ.rank → ℂ :=
    fun j => inner ℂ (g j) ψ.vec * ((Real.sqrt (μ j) : ℝ) : ℂ)⁻¹ with hα
  set a : EuclideanSpace ℂ (Fin ρ.rank) := (WithLp.equiv 2 (Fin ρ.rank → ℂ)).symm α with ha
  have ha_apply : ∀ j, a.ofLp j = α j := fun j => by
    rw [ha, WithLp.equiv_symm_apply_ofLp]
  -- `∑ⱼ αⱼ|b̃ⱼ⟩ = ψ`
  have ha_sum : ∑ j, a.ofLp j • ρ.reducedEigenEnsemble.tildeVec j = ψ.vec := by
    have hterm : ∀ j, a.ofLp j • ρ.reducedEigenEnsemble.tildeVec j =
        inner ℂ (g j) ψ.vec • g j := by
      intro j
      rw [ha_apply, hα, hbtilde j, smul_smul, mul_assoc,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (hμpos j))), mul_one]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact ρ.sum_reducedEigen_inner_smul_eq_of_mem_support h
  -- `a ≠ 0` (else `ψ = 0`)
  have ha_ne : a ≠ 0 := by
    intro hz
    apply hψ0
    rw [← ha_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : a.ofLp j = 0 := by rw [hz]; simp
    rw [this, zero_smul]
  have ha_norm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha_ne
  set w : EuclideanSpace ℂ (Fin ρ.rank) := (‖a‖ : ℂ)⁻¹ • a with hw
  have hw_norm : ‖w‖ = 1 := by
    rw [hw, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ ha_norm]
  -- any unit vector is the first row of a unitary matrix; rotate the reduced eigenensemble by it
  obtain ⟨u, hu, hu_row⟩ := EuclideanSpace.exists_mem_unitaryGroup_row_zero_eq w hw_norm
  -- the new subnormalized vectors and that they generate `ρ`
  set v : Fin ρ.rank → S.space :=
    fun i => ∑ j, u i j • ρ.reducedEigenEnsemble.tildeVec j with hv_def
  have hb_sum : ∑ i, rankOne ℂ (ρ.reducedEigenEnsemble.tildeVec i)
      (ρ.reducedEigenEnsemble.tildeVec i) = ρ.op := by
    rw [← ρ.reducedEigenEnsemble.toState_op_eq_sum_rankOne_tildeVec, ρ.reducedEigenEnsemble_toState]
  have hop : ∑ i, rankOne ℂ (v i) (v i) = ρ.op := by
    simp only [hv_def]
    rw [sum_rankOne_self_eq_of_mem_unitaryGroup hu (fun j => ρ.reducedEigenEnsemble.tildeVec j)]
    exact hb_sum
  -- `|ψ̃₀⟩ = ‖a‖⁻¹ • ψ`
  have hv0 : v 0 = (‖a‖ : ℂ)⁻¹ • ψ.vec := by
    have hstep : ∀ j, u 0 j • ρ.reducedEigenEnsemble.tildeVec j =
        (‖a‖ : ℂ)⁻¹ • (a.ofLp j • ρ.reducedEigenEnsemble.tildeVec j) := by
      intro j
      have hu0 : u 0 j = (‖a‖ : ℂ)⁻¹ * a.ofLp j := by
        rw [hu_row, hw, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      rw [hu0, mul_smul]
    simp only [hv_def]
    rw [Finset.sum_congr rfl fun j _ => hstep j, ← Finset.smul_sum, ha_sum]
  have hv0_ne : v 0 ≠ 0 := by
    rw [hv0]
    exact smul_ne_zero (inv_ne_zero (by exact_mod_cast ha_norm)) hψ0
  -- assemble the ensemble
  refine ⟨Ensemble.ofSubnormalized v ρ hop ψ, ⟨Ensemble.ofSubnormalized_toState v ρ hop ψ, rfl⟩,
    (0 : Fin ρ.rank), ?_⟩
  rw [Ensemble.ofSubnormalized_states_vec_of_ne_zero v ρ hop ψ hv0_ne, hv0, norm_smul, norm_inv,
    Complex.norm_real, norm_norm, ψ.normalized, mul_one, smul_smul, Complex.ofReal_inv, inv_inv,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha_norm), one_smul]

end AxQM
