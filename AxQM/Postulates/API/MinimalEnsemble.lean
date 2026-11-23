/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ReducedEigenEnsemble
import AxQM.Postulates.API.UnitaryFreedom
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# AxQM — minimal ensembles for a density operator

Nielsen & Chuang, Exercise 2.73, single out the **minimal ensembles** of a density operator `ρ`:
an ensemble `{pᵢ, |ψᵢ⟩}` for `ρ` is *minimal* when its number of elements equals the **rank** of
`ρ`. This is the smallest an ensemble generating `ρ` can be — the reduced eigenensemble
(`State.reducedEigenEnsemble`) realises it — and the exercise studies which support vectors can
appear in a minimal ensemble, and with what probability.

This file introduces the predicate and its two structural facts; the existence of a minimal ensemble
through a prescribed support vector (Exercise 2.73, part 1) and the probability formula
`pᵢ = 1/⟨ψᵢ|ρ⁻¹|ψᵢ⟩` (part 2) use it in `AxQM/Postulates/API/MinimalEnsembleExistence.lean` and
`AxQM/Postulates/API/MinimalEnsembleProbability.lean`.

## Main definitions

* `AxQM.Ensemble.IsMinimalFor` — the predicate `e.IsMinimalFor ρ`: the ensemble `e`
  generates `ρ` (`e.toState = ρ`) and has exactly `ρ.rank` elements (`e.card = ρ.rank`).

## Main results

* `Ensemble.IsMinimalFor.prob_pos` — in a minimal ensemble **every** weight is strictly positive
  (there is no probability-zero padding). If some `pᵢ = 0` the corresponding subnormalized vector
  `|ψ̃ᵢ⟩ = √pᵢ|ψᵢ⟩` vanishes, so the range of `ρ = ∑ⱼ |ψ̃ⱼ⟩⟨ψ̃ⱼ|` is spanned by fewer than `card`
  vectors, forcing `rank ρ < card = rank ρ` — a contradiction.
* `Ensemble.IsMinimalFor.states_mem_support` — every state `|ψᵢ⟩` of a minimal ensemble lies in the
  support of `ρ`. If `u ∈ ker ρ` then `0 = ⟨u|ρ|u⟩ = ∑ⱼ pⱼ|⟨ψⱼ|u⟩|²`, and since every `pⱼ > 0`
  each `⟨ψⱼ|u⟩ = 0`; thus `|ψᵢ⟩ ⊥ ker ρ`, i.e. `|ψᵢ⟩ ∈ (ker ρ)ᗮ = support ρ`.
* `State.reducedEigenEnsemble_isMinimalFor` — the reduced eigenensemble is a minimal ensemble; the
  canonical witness that minimal ensembles exist.
-/

open scoped InnerProductSpace
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- **A minimal ensemble for `ρ`** (Nielsen–Chuang Exercise 2.73): an ensemble `e` that generates
`ρ` (`e.toState = ρ`) and has exactly `ρ.rank` elements (`e.card = ρ.rank`) — the fewest an ensemble
generating `ρ` can have. A predicate on `Ensemble` tying it to a specific
`ρ`, so existence/uniqueness statements quantify faithfully over `∀ e, e.IsMinimalFor ρ → …`. -/
def IsMinimalFor (e : Ensemble S) (ρ : State S) : Prop :=
  e.toState = ρ ∧ e.card = ρ.rank

/-- **Every weight of a minimal ensemble is strictly positive** (Nielsen–Chuang Exercise 2.73): a
minimal ensemble carries no probability-zero padding. Suppose `pᵢ = 0`. Then the subnormalized
vector `|ψ̃ᵢ⟩ = √pᵢ|ψᵢ⟩` is `0`, so the density operator `ρ = ∑ⱼ |ψ̃ⱼ⟩⟨ψ̃ⱼ|`
(`toState_op_eq_sum_rankOne_tildeVec`) has its range inside the span of the `< card` **non-zero**
subnormalized vectors; by `finrank_span_finset_le_card` the rank is at most `card - 1`. But
minimality gives `rank ρ = card`, a contradiction. -/
theorem IsMinimalFor.prob_pos {e : Ensemble S} {ρ : State S}
    (hmin : e.IsMinimalFor ρ) (i : Fin e.card) : 0 < e.prob i := by
  classical
  rcases (e.prob_nonneg i).eq_or_lt with hpi | hpi
  · exfalso
    -- the offending subnormalized vector vanishes
    have htv0 : e.tildeVec i = 0 := by
      simp only [Ensemble.tildeVec, ← hpi, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
    -- `ρ = ∑ⱼ |ψ̃ⱼ⟩⟨ψ̃ⱼ|`
    have hop : ρ.op = ∑ j, rankOne ℂ (e.tildeVec j) (e.tildeVec j) := by
      rw [← hmin.1]; exact e.toState_op_eq_sum_rankOne_tildeVec
    -- the finset of non-zero subnormalized vectors
    set T := (Finset.univ.filter (fun k => e.tildeVec k ≠ 0)).image e.tildeVec with hT
    -- every subnormalized vector lies in the span of `T` (zero ones trivially)
    have htv_mem : ∀ j, e.tildeVec j ∈ Submodule.span ℂ (↑T : Set S.space) := by
      intro j
      rcases eq_or_ne (e.tildeVec j) 0 with h | h
      · rw [h]; exact Submodule.zero_mem _
      · exact Submodule.subset_span (by
          rw [hT, Finset.coe_image]
          exact Set.mem_image_of_mem e.tildeVec
            (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)))
    -- hence `range ρ ⊆ span T`
    have hsub : LinearMap.range (ρ.op : S.space →ₗ[ℂ] S.space) ≤
        Submodule.span ℂ (↑T : Set S.space) := by
      rw [LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
      intro v
      rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hop, sum_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [rankOne_apply]
      exact Submodule.smul_mem _ _ (htv_mem j)
    -- `rank ρ ≤ card T`
    have h1 : ρ.rank ≤ T.card :=
      le_trans (Submodule.finrank_mono hsub) (finrank_span_finset_le_card T)
    -- but `card T ≤ card - 1`, since `i` is excluded by `htv0`
    have hfilter : Finset.univ.filter (fun k => e.tildeVec k ≠ 0) ⊆ Finset.univ.erase i := by
      intro j hj
      rw [Finset.mem_filter] at hj
      exact Finset.mem_erase.mpr ⟨fun hji => hj.2 (hji ▸ htv0), Finset.mem_univ j⟩
    have h2 : T.card ≤ e.card - 1 := by
      rw [hT]
      calc (Finset.image e.tildeVec (Finset.univ.filter (fun k => e.tildeVec k ≠ 0))).card
          ≤ (Finset.univ.filter (fun k => e.tildeVec k ≠ 0)).card := Finset.card_image_le
        _ ≤ (Finset.univ.erase i).card := Finset.card_le_card hfilter
        _ = e.card - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    -- combine with minimality and `card ≥ 1` (witnessed by `i`)
    have hcard : e.card = ρ.rank := hmin.2
    have hi : (i : ℕ) < e.card := i.isLt
    omega
  · exact hpi

/-- **Every state of a minimal ensemble lies in the support of `ρ`** (Nielsen–Chuang Exercise 2.73):
an ensemble realising `ρ` minimally has all its pure states in the support. Writing
`support ρ = (ker ρ)ᗮ`, take `u ∈ ker ρ`. Applying `⟨u| · ⟩` to `ρ u = ∑ⱼ pⱼ⟨ψⱼ|u⟩|ψⱼ⟩ = 0` gives
`∑ⱼ pⱼ|⟨ψⱼ|u⟩|² = 0`; every summand is `≥ 0` and every `pⱼ > 0` (`IsMinimalFor.prob_pos`), so each
`⟨ψⱼ|u⟩ = 0`. In particular `⟨u|ψᵢ⟩ = 0`, i.e. `|ψᵢ⟩ ⊥ ker ρ`. -/
theorem IsMinimalFor.states_mem_support {e : Ensemble S} {ρ : State S}
    (hmin : e.IsMinimalFor ρ) (i : Fin e.card) : (e.states i).vec ∈ ρ.support := by
  rw [State.support_eq_orthogonal_ker, Submodule.mem_orthogonal]
  intro u hu
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hu
  -- expand `ρ u`
  have hopu : ρ.op u =
      ∑ j, (e.prob j : ℂ) • inner ℂ (e.states j).vec u • (e.states j).vec := by
    rw [← hmin.1]; exact e.toState_op_apply u
  -- `∑ⱼ pⱼ ⟨ψⱼ|u⟩ ⟨u|ψⱼ⟩ = ⟨u|ρ u⟩ = 0`
  have hsum0 : ∑ j, (e.prob j : ℂ) *
      (inner ℂ (e.states j).vec u * inner ℂ u (e.states j).vec) = 0 := by
    have hexp : inner ℂ u (ρ.op u) = ∑ j, (e.prob j : ℂ) *
        (inner ℂ (e.states j).vec u * inner ℂ u (e.states j).vec) := by
      rw [hopu, inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, inner_smul_right]
    rw [← hexp, hu, inner_zero_right]
  -- turn the complex identity into a real, non-negative sum
  have hterm : ∀ j, (e.prob j : ℂ) *
      (inner ℂ (e.states j).vec u * inner ℂ u (e.states j).vec) =
        ((e.prob j * ‖inner ℂ (e.states j).vec u‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [← inner_conj_symm u (e.states j).vec, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hsumR : ∑ j, e.prob j * ‖inner ℂ (e.states j).vec u‖ ^ 2 = 0 := by
    have hc : ((∑ j, e.prob j * ‖inner ℂ (e.states j).vec u‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum, ← hsum0]
      exact Finset.sum_congr rfl fun j _ => (hterm j).symm
    exact_mod_cast hc
  -- extract the `i`-th term and use `pᵢ > 0`
  have hterm0 : e.prob i * ‖inner ℂ (e.states i).vec u‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (e.prob_nonneg j) (sq_nonneg _))).mp hsumR i (Finset.mem_univ i)
  have hz : inner ℂ (e.states i).vec u = 0 := by
    have h2 : ‖inner ℂ (e.states i).vec u‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm0 with h | h
      · exact absurd h (ne_of_gt (hmin.prob_pos i))
      · exact h
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2)
  rw [← inner_conj_symm, hz, map_zero]

end Ensemble

namespace State

/-- **The reduced eigenensemble is a minimal ensemble** (Nielsen–Chuang Exercise 2.73): it generates
`ρ` (`reducedEigenEnsemble_toState`) and has exactly `ρ.rank` elements
(`reducedEigenEnsemble_card`). The canonical witness that a minimal ensemble for `ρ` exists. -/
theorem reducedEigenEnsemble_isMinimalFor (ρ : State S) :
    ρ.reducedEigenEnsemble.IsMinimalFor ρ :=
  ⟨ρ.reducedEigenEnsemble_toState, ρ.reducedEigenEnsemble_card⟩

end State

end AxQM
