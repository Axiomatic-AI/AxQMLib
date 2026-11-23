/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChi
import AxQM.Postulates.API.Ensemble
import AxQM.Postulates.API.EntropyConcavity

/-!
# The channel Holevo χ quantity is achieved by pure-state ensembles (N&C Exercise 12.11, Part 1)

Nielsen & Chuang, Exercise 12.11 (p. 555), asks to show that the maximum defining the Holevo χ
quantity of a channel `E` (eq. (12.71), the left-hand side of the HSW theorem),

`χ(E) = max_{{pⱼ, ρⱼ}} [ S(E(∑ⱼ pⱼ ρⱼ)) − ∑ⱼ pⱼ S(E(ρⱼ)) ]`,

may be achieved using an ensemble of **pure** states. This file supplies the
machinery for that reduction: the χ-value set restricted to pure-state input ensembles
(`channelHolevoChiPureSet`) and the reduction

`χ(E) = sSup (channelHolevoChiPureSet E)`   for a channel `E`

(`channelHolevoChi_eq_sSup_channelHolevoChiPureSet`). The second part of the exercise — that at most
`d²` pure states suffice, `d` the input dimension — is a separate Carathéodory-type argument, in
`AxQM/Core/ChannelHolevoChiPureCard.lean`.

## Proof idea

Restricting the maximization to pure ensembles cannot *increase* the supremum, since pure ensembles
are a subset of all ensembles. For the reverse, we **refine** an arbitrary input ensemble
`{pⱼ, ρⱼ}` into a pure one without decreasing the output-ensemble χ: replace each `ρⱼ` by its
eigenensemble `{λⱼₖ, |ψⱼₖ⟩}` (`Ensemble.ofState`, which reproduces `ρⱼ` by
`Ensemble.ofState_toState`). The refined ensemble `{pⱼ λⱼₖ, |ψⱼₖ⟩}` has the **same mixture**
`∑ⱼₖ pⱼ λⱼₖ |ψⱼₖ⟩⟨ψⱼₖ| = ∑ⱼ pⱼ ρⱼ`, so the first term `S(E(mixture))` is unchanged, while, because a
channel is affine over mixtures (`map_mix_of_isChannel`) and the von Neumann entropy is **concave**
(`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`), each `S(E(ρⱼ)) ≥ ∑ₖ λⱼₖ S(E ψⱼₖ)`,
so the subtracted average output entropy only *decreases*. Hence the refined pure ensemble has
output χ `≥` the original, and the pure supremum matches the full one.

## Main definitions and results

* `AxQM.channelHolevoChiPureSet` — the χ-value set over pure-state input ensembles.
* `AxQM.Ensemble.toState_eq_mix` — an ensemble's density operator is the `State.mix` of its
  pure components (an `Ensemble`↔`Mixture` bridge).
* `AxQM.channelHolevoChi_eq_sSup_channelHolevoChiPureSet` — **the Part 1 reduction**.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **An ensemble's density operator is the `State.mix` of its pure components**:
`ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ| = State.mix p (fun i => |ψᵢ⟩⟨ψᵢ|)`. Both sides have the same operator
`∑ᵢ (pᵢ : ℂ) • |ψᵢ⟩⟨ψᵢ|` (`Ensemble.toState_op`, `State.mix_op`). Bridges the eigenensemble
construction (`Ensemble.ofState`) to the mixture `State.mix`, so channel-affineness
and entropy concavity apply to a spectral decomposition. -/
theorem Ensemble.toState_eq_mix (e : Ensemble S) :
    e.toState = State.mix e.prob e.prob_nonneg e.sum_prob (fun i => (e.states i).toState) := by
  apply State.ext
  rw [Ensemble.toState_op, State.mix_op]

/-- The set of Holevo χ values `χ({pⱼ, E(ψⱼ)})` of the *output* ensemble obtained by pushing a
finite **pure-state** input ensemble `{pⱼ, |ψⱼ⟩}` (indexed by `Fin n`, WLOG for finite ensembles)
through `E`. Its supremum is the pure-restricted channel Holevo χ; `channelHolevoChi_eq_sSup_…`
shows it equals the full `channelHolevoChi E` when `E` is a channel. -/
def channelHolevoChiPureSet (E : State S → State S) : Set ℝ :=
  {x | ∃ (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
      (ψ : Fin n → PureState S), x = State.holevoChi p hp hsum (fun i => E (ψ i).toState)}

/-- **Any finite pure-state ensemble contributes its output-χ to `channelHolevoChiPureSet`.**
The ensemble may be indexed by an arbitrary finite type `κ`; it is reindexed to `Fin (card κ)` via
`Fintype.equivFin`, leaving the χ value unchanged (`State.holevoChi_equiv`). -/
theorem holevoChi_pureEnsemble_mem (E : State S → State S) {κ : Type*} [Fintype κ]
    (q : κ → ℝ) (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (ψ : κ → PureState S) :
    State.holevoChi q hq hqsum (fun i => E (ψ i).toState) ∈ channelHolevoChiPureSet E := by
  let e := (Fintype.equivFin κ).symm
  have hp' : ∀ i, 0 ≤ q (e i) := fun i => hq _
  have hsum' : ∑ i, q (e i) = 1 := by rw [Equiv.sum_comp e q]; exact hqsum
  exact ⟨Fintype.card κ, fun i => q (e i), hp', hsum', fun i => ψ (e i),
    (State.holevoChi_equiv e q hq hqsum (fun k => E (ψ k).toState) hp' hsum').symm⟩

/-- **The pure-state χ set is contained in the full χ set** (`channelHolevoChiSet`): a pure-state
ensemble is an ensemble. In particular the pure set is bounded above. -/
theorem channelHolevoChiPureSet_subset (E : State S → State S) :
    channelHolevoChiPureSet E ⊆ channelHolevoChiSet E := by
  rintro x ⟨n, p, hp, hsum, ψ, rfl⟩
  exact ⟨n, p, hp, hsum, fun i => (ψ i).toState, rfl⟩

/-- **Refinement into a pure ensemble does not decrease the output-χ.** For a channel `E` and any
input ensemble `{pⱼ, ρⱼ}`, there is a pure-state ensemble (its output-χ lies in
`channelHolevoChiPureSet E`) whose output Holevo χ is at least that of `{pⱼ, E(ρⱼ)}`. The pure
ensemble is the eigenensemble refinement `{pⱼ λⱼₖ, |ψⱼₖ⟩}`; it has the same mixture, and by
concavity of the entropy across each component's spectral decomposition the subtracted average
output entropy only decreases. -/
theorem exists_pure_holevoChi_ge_of_isChannel {E : State S → State S} (hE : IsChannel E)
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : Fin n → State S) :
    ∃ y ∈ channelHolevoChiPureSet E,
      State.holevoChi p hp hsum (fun i => E (ρ i)) ≤ y := by
  classical
  -- refined weights and pure states, indexed by the sigma of per-component eigenensembles
  set q : (j : Fin n) × Fin ((Ensemble.ofState (ρ j)).card) → ℝ :=
    fun x => p x.1 * (Ensemble.ofState (ρ x.1)).prob x.2 with hq_def
  set ψ : (j : Fin n) × Fin ((Ensemble.ofState (ρ j)).card) → PureState S :=
    fun x => (Ensemble.ofState (ρ x.1)).states x.2 with hψ_def
  have hq : ∀ x, 0 ≤ q x := fun x =>
    mul_nonneg (hp x.1) ((Ensemble.ofState (ρ x.1)).prob_nonneg x.2)
  have hqsum : ∑ x, q x = 1 := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    simp only [hq_def]
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, (Ensemble.ofState (ρ j)).sum_prob, mul_one]
  -- the refinement has the same mixture as the original ensemble
  have hmixeq : State.mix q hq hqsum (fun x => (ψ x).toState) = State.mix p hp hsum ρ := by
    apply State.ext
    rw [State.mix_op, State.mix_op, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrho : ∑ k, (((Ensemble.ofState (ρ j)).prob k : ℂ)) •
        ((Ensemble.ofState (ρ j)).states k).toState.op = (ρ j).op := by
      rw [← Ensemble.toState_op (Ensemble.ofState (ρ j)), Ensemble.ofState_toState]
    rw [← hrho, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hq_def, hψ_def]
    rw [Complex.ofReal_mul, smul_smul]
  -- per component: concavity of the entropy across the eigenensemble
  have hj : ∀ j, ∑ k, (Ensemble.ofState (ρ j)).prob k *
      (E (((Ensemble.ofState (ρ j)).states k).toState)).vonNeumannEntropy
        ≤ (E (ρ j)).vonNeumannEntropy := by
    intro j
    have hEρj : E (ρ j) = State.mix (Ensemble.ofState (ρ j)).prob
        (Ensemble.ofState (ρ j)).prob_nonneg (Ensemble.ofState (ρ j)).sum_prob
        (fun k => E (((Ensemble.ofState (ρ j)).states k).toState)) := by
      conv_lhs => rw [← Ensemble.ofState_toState (ρ j)]
      rw [Ensemble.toState_eq_mix, map_mix_of_isChannel hE]
    rw [hEρj]
    exact State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix' _ _ _ _
  -- the average output entropy of the refinement is ≤ that of the original ensemble
  have hentineq : ∑ x, q x * (E ((ψ x).toState)).vonNeumannEntropy
      ≤ ∑ i, p i * (E (ρ i)).vonNeumannEntropy := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_le_sum fun j _ => ?_
    have hfac : ∑ k, q ⟨j, k⟩ * (E ((ψ ⟨j, k⟩).toState)).vonNeumannEntropy
        = p j * ∑ k, (Ensemble.ofState (ρ j)).prob k *
          (E (((Ensemble.ofState (ρ j)).states k).toState)).vonNeumannEntropy := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hq_def, hψ_def]
      ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left (hj j) (hp j)
  -- assemble: the refined pure ensemble's output-χ dominates the original's
  refine ⟨State.holevoChi q hq hqsum (fun x => E (ψ x).toState),
    holevoChi_pureEnsemble_mem E q hq hqsum ψ, ?_⟩
  rw [holevoChi_comp_eq_of_isChannel hE, holevoChi_comp_eq_of_isChannel hE, hmixeq]
  linarith [hentineq]

/-- **N&C Exercise 12.11, Part 1: the channel Holevo χ maximum is achieved by pure-state
ensembles.** For a channel `E`, the Holevo χ quantity `χ(E)` (eq. (12.71), the left-hand side of the
HSW theorem) equals the supremum of the output Holevo χ over **pure-state** input ensembles alone:

`χ(E) = sSup (channelHolevoChiPureSet E)`.

The `≤`-direction restricted to pure ensembles is trivial (they are a subset); the reverse is the
eigenensemble refinement `exists_pure_holevoChi_ge_of_isChannel`, which produces, for every
ensemble, a pure ensemble of at least the same output-χ. -/
theorem channelHolevoChi_eq_sSup_channelHolevoChiPureSet {E : State S → State S}
    (hE : IsChannel E) :
    channelHolevoChi E = sSup (channelHolevoChiPureSet E) := by
  rcases (channelHolevoChiSet E).eq_empty_or_nonempty with hempty | hne
  · -- no ensembles at all ⇒ the pure set is empty too
    have hpe : channelHolevoChiPureSet E = ∅ :=
      Set.eq_empty_of_subset_empty (hempty ▸ channelHolevoChiPureSet_subset E)
    rw [hpe]
    exact congrArg sSup hempty
  · have hbdd : BddAbove (channelHolevoChiPureSet E) :=
      BddAbove.mono (channelHolevoChiPureSet_subset E) (channelHolevoChiSet_bddAbove E)
    apply le_antisymm
    · -- χ(E) = sSup full ≤ sSup pure, via the refinement of each ensemble
      apply csSup_le hne
      rintro x ⟨n, p, hp, hsum, ρ, rfl⟩
      obtain ⟨y, hy_mem, hxy⟩ := exists_pure_holevoChi_ge_of_isChannel hE p hp hsum ρ
      exact hxy.trans (le_csSup hbdd hy_mem)
    · -- sSup pure ≤ sSup full = χ(E); the pure set is nonempty (refine any full witness)
      refine csSup_le_csSup (channelHolevoChiSet_bddAbove E) ?_ (channelHolevoChiPureSet_subset E)
      obtain ⟨x, n, p, hp, hsum, ρ, rfl⟩ := hne
      obtain ⟨y, hy_mem, _⟩ := exists_pure_holevoChi_ge_of_isChannel hE p hp hsum ρ
      exact ⟨y, hy_mem⟩

end AxQM
