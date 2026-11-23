/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChiPure
import AxQM.Postulates.API.EntropyMixLine
import ToMathlib.Analysis.Convex.SupportReduction
import ToMathlib.Analysis.InnerProductSpace.SelfAdjointFinrank

/-!
# The channel Holevo χ maximum is achieved by `≤ d²` pure states (N&C Exercise 12.11, Part 2)

Nielsen & Chuang, Exercise 12.11 (p. 555) asks to show that the maximum defining the Holevo χ
quantity of a channel `E` (eq. (12.71), the left-hand side of the HSW theorem) is achieved by an
ensemble of at most `d²` **pure** states, where `d = dim` of the channel input. Part 1
(`AxQM/Core/ChannelHolevoChiPure.lean`) reduced the maximization to pure-state ensembles; this
file supplies the second, **cardinality** reduction and the final statement

`χ(E) = sSup (channelHolevoChiPureLeCardSet E)`   for a channel `E`

(`channelHolevoChi_eq_sSup_channelHolevoChiPureLeCardSet`), where `channelHolevoChiPureLeCardSet E`
restricts the supremum to pure-state input ensembles of at most `S.dim ^ 2` elements.

## Proof idea

A pure-state ensemble `{pⱼ, |ψⱼ⟩}` contributes the output χ `S(E(∑ⱼ pⱼ|ψⱼ⟩⟨ψⱼ|)) − ∑ⱼ pⱼ S(E ψⱼ)`.
The rank-one projections `|ψⱼ⟩⟨ψⱼ|` are **self-adjoint operators** — points of the real vector space
`selfAdjoint (S.space →L[ℂ] S.space)`, of real dimension `d²`
(`finrank_real_selfAdjoint_continuousLinearMap`,
`ToMathlib/Analysis/InnerProductSpace/SelfAdjointFinrank.lean`) — and each has **unit trace**, so
all lie on the affine hyperplane `{φ = 1}` for the real-trace functional `φ = re ∘ tr`. The abstract
hyperplane-refined Carathéodory theorem `exists_reduced_weights_le_finrank`
(`ToMathlib/Analysis/Convex/SupportReduction.lean`) then replaces
the weights `pⱼ` by nonnegative weights `w'ⱼ` with

* the **same barycenter** `∑ⱼ w'ⱼ |ψⱼ⟩⟨ψⱼ| = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|` — so the output mixture, hence
  `S(E(mixture))`, is unchanged;
* the **same total** `∑ⱼ w'ⱼ = 1` — so `w'` is again a probability distribution;
* a **no-larger objective** `∑ⱼ w'ⱼ S(E ψⱼ) ≤ ∑ⱼ pⱼ S(E ψⱼ)` — so the subtracted average output
  entropy only decreases, i.e. the output χ does not decrease; and
* **support of size `≤ d²`**.

Dropping the (harmless) zero-weight states leaves a pure ensemble of `≤ d²` states with output χ at
least as large (`exists_pureLeCard_holevoChi_ge_of_isChannel`); composing with Part 1 gives the
final statement. The `d²` bound is *tight* (self-adjoint operators, not the full
`2d²`-real-dimensional operator space), matching N&C, and needs no Fenchel–Eggleston `+1`.

## Main definitions and results

* `AxQM.channelHolevoChiPureLeCardSet` — the χ-value set over pure-state input ensembles of
  at most `d²` elements.
* `AxQM.exists_pureLeCard_holevoChi_ge_of_isChannel` — every pure ensemble is refined into
  a `≤ d²`-element pure ensemble of at least the same output χ.
* `AxQM.channelHolevoChi_eq_sSup_channelHolevoChiPureLeCardSet` — **the Part 2 reduction**.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.3.2, Theorem 12.8, eq. (12.71); Exercise 12.11.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The set of Holevo χ values `χ({pⱼ, E(ψⱼ)})` of the *output* ensemble obtained by pushing a
finite **pure-state** input ensemble `{pⱼ, |ψⱼ⟩}` of at most `d² = S.dim ^ 2` states (indexed by
`Fin n` with `n ≤ S.dim ^ 2`) through `E`. Its supremum equals the full `channelHolevoChi E` when
`E` is a
channel (`channelHolevoChi_eq_sSup_channelHolevoChiPureLeCardSet`); `d` is the dimension of the
channel input. -/
def channelHolevoChiPureLeCardSet (E : State S → State S) : Set ℝ :=
  {x | ∃ (n : ℕ) (_ : n ≤ S.dim ^ 2) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
      (ψ : Fin n → PureState S), x = State.holevoChi p hp hsum (fun i => E (ψ i).toState)}

/-- **Any finite pure-state ensemble of at most `d²` states contributes its output-χ to
`channelHolevoChiPureLeCardSet`.** The ensemble may be indexed by an arbitrary finite type `κ` with
`Fintype.card κ ≤ S.dim ^ 2`; it is reindexed to `Fin (card κ)` via `Fintype.equivFin`, leaving
the χ value unchanged (`State.holevoChi_equiv`) and the cardinality bound intact. -/
theorem holevoChi_pureEnsemble_card_le_mem (E : State S → State S) {κ : Type*} [Fintype κ]
    (hκ : Fintype.card κ ≤ S.dim ^ 2)
    (q : κ → ℝ) (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (ψ : κ → PureState S) :
    State.holevoChi q hq hqsum (fun i => E (ψ i).toState) ∈ channelHolevoChiPureLeCardSet E := by
  let e := (Fintype.equivFin κ).symm
  have hp' : ∀ i, 0 ≤ q (e i) := fun i => hq _
  have hsum' : ∑ i, q (e i) = 1 := by rw [Equiv.sum_comp e q]; exact hqsum
  exact ⟨Fintype.card κ, hκ, fun i => q (e i), hp', hsum', fun i => ψ (e i),
    (State.holevoChi_equiv e q hq hqsum (fun k => E (ψ k).toState) hp' hsum').symm⟩

/-- **The `≤ d²` pure-state χ set is contained in the pure-state χ set**
(`channelHolevoChiPureSet`): a `≤ d²`-element pure ensemble is a pure ensemble. In particular it is
bounded above. -/
theorem channelHolevoChiPureLeCardSet_subset (E : State S → State S) :
    channelHolevoChiPureLeCardSet E ⊆ channelHolevoChiPureSet E := by
  rintro x ⟨n, _, p, hp, hsum, ψ, rfl⟩
  exact ⟨n, p, hp, hsum, ψ, rfl⟩

/-- **Cardinality reduction: a pure ensemble is refined into a `≤ d²`-element pure ensemble without
decreasing the output-χ.** For a channel `E` and any pure-state input ensemble `{pⱼ, |ψⱼ⟩}`, there
is a pure-state ensemble of at most `d² = S.dim ^ 2` states (its output-χ lies in
`channelHolevoChiPureLeCardSet E`) whose output Holevo χ is at least that of `{pⱼ, E(ψⱼ)}`.

The rank-one projections `|ψⱼ⟩⟨ψⱼ|` are unit-trace self-adjoint operators — points of the affine
hyperplane `{re ∘ tr = 1}` in the `d²`-real-dimensional space `selfAdjoint (S.space →L[ℂ] S.space)`
(`finrank_real_selfAdjoint_continuousLinearMap`). The hyperplane-refined Carathéodory theorem
`exists_reduced_weights_le_finrank` reduces the weights to support `≤ d²` while preserving the
barycenter `∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|` (hence the output mixture and `S(E(mixture))`) and the total, and not
increasing `∑ⱼ pⱼ S(E ψⱼ)` (hence not decreasing the output χ). -/
theorem exists_pureLeCard_holevoChi_ge_of_isChannel {E : State S → State S} (hE : IsChannel E)
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ψ : Fin n → PureState S) :
    ∃ y ∈ channelHolevoChiPureLeCardSet E,
      State.holevoChi p hp hsum (fun i => E (ψ i).toState) ≤ y := by
  classical
  -- the ambient real vector space: self-adjoint operators, of real dimension `d²`
  set V := selfAdjoint.submodule ℝ (S.space →L[ℂ] S.space) with hVdef
  have hsa : ∀ j, (ψ j).toState.op ∈ V := fun j =>
    selfAdjoint.mem_iff.mpr (State.isSelfAdjoint_op _)
  -- the real-trace functional `re ∘ tr`, built locally
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := fun A => (LinearMap.trace ℂ S.space (A : S.space →L[ℂ] S.space)).re
      map_add' := fun A B => by
        simp only [Submodule.coe_add, ContinuousLinearMap.toLinearMap_add, map_add, Complex.add_re]
      map_smul' := fun r A => by
        have key : ((r • A : V) : S.space →L[ℂ] S.space)
            = (↑r : ℂ) • (A : S.space →L[ℂ] S.space) := by
          rw [SetLike.val_smul, Complex.coe_smul]
        simp only [RingHom.id_apply, smul_eq_mul, key, ContinuousLinearMap.toLinearMap_smul,
            map_smul,
          Complex.re_ofReal_mul] }
  -- each rank-one projection lies on the hyperplane `{φ = 1}` (unit trace)
  have hv1 : ∀ j : Fin n, φ ⟨(ψ j).toState.op, hsa j⟩ = 1 := by
    intro j
    change (LinearMap.trace ℂ S.space ((ψ j).toState.op : S.space →L[ℂ] S.space)).re = 1
    rw [State.trace_op_eq_one]; simp
  -- support reduction, minimizing the output-entropy objective `t j = S(E ψⱼ)`
  obtain ⟨w', hw'0, hbary, htot, hobj, s, hs_iff, hs_card⟩ :=
    exists_reduced_weights_le_finrank (v := fun j => (⟨(ψ j).toState.op, hsa j⟩ : V)) φ hv1
      (fun j => (E (ψ j).toState).vonNeumannEntropy) hp
  have hw'z : ∀ j ∉ s, w' j = 0 := fun j hj => by
    by_contra h; exact hj ((hs_iff j).mp h)
  -- the reduced weights over the (`≤ d²`-element) support `s`
  have hq0 : ∀ i : ↥s, 0 ≤ w' ↑i := fun i => hw'0 _
  have hqsum : ∑ i : ↥s, w' ↑i = 1 := by
    rw [Finset.sum_coe_sort s w', Finset.sum_subset s.subset_univ (fun j _ hj => hw'z j hj),
      htot, hsum]
  have hcard : Fintype.card ↥s ≤ S.dim ^ 2 := by
    rw [Fintype.card_coe]
    exact hs_card.trans_eq (finrank_real_selfAdjoint_continuousLinearMap (E := S.space))
  refine ⟨State.holevoChi (fun i : ↥s => w' ↑i) hq0 hqsum (fun i => E (ψ ↑i).toState),
    holevoChi_pureEnsemble_card_le_mem E hcard _ hq0 hqsum (fun i => ψ ↑i), ?_⟩
  -- the reduced ensemble has the same mixture (same barycenter of the `|ψⱼ⟩⟨ψⱼ|`)
  have hmix : State.mix (fun i : ↥s => w' ↑i) hq0 hqsum (fun i => (ψ ↑i).toState)
      = State.mix p hp hsum (fun j => (ψ j).toState) := by
    apply State.ext
    rw [State.mix_op, State.mix_op,
      Finset.sum_coe_sort s (fun j => (↑(w' j) : ℂ) • (ψ j).toState.op),
      Finset.sum_subset s.subset_univ (fun j _ hj => by rw [hw'z j hj]; simp)]
    have h := congrArg V.subtype hbary
    rw [map_sum, map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    -- both endpoints are `Complex.coe_smul` cast-normalizations of `h`'s ℝ-smul sum
    simpa only [Complex.coe_smul] using h
  -- and no larger average output entropy
  have hentr : ∑ i : ↥s, w' ↑i * (E (ψ ↑i).toState).vonNeumannEntropy
      ≤ ∑ j, p j * (E (ψ j).toState).vonNeumannEntropy := by
    rw [Finset.sum_coe_sort s (fun j => w' j * (E (ψ j).toState).vonNeumannEntropy),
      Finset.sum_subset s.subset_univ (fun j _ hj => by rw [hw'z j hj]; ring)]
    exact hobj
  rw [holevoChi_comp_eq_of_isChannel hE, holevoChi_comp_eq_of_isChannel hE, hmix]
  linarith [hentr]

/-- **N&C Exercise 12.11, Part 2: the channel Holevo χ maximum is achieved by an ensemble of `≤ d²`
pure states.** For a channel `E`, the Holevo χ quantity `χ(E)` (eq. (12.71), the left-hand side of
the HSW theorem) equals the supremum of the output Holevo χ over **pure-state** input ensembles of
at most `d² = S.dim ^ 2` elements alone, `d` the dimension of the channel input:

`χ(E) = sSup (channelHolevoChiPureLeCardSet E)`.

By Part 1 (`channelHolevoChi_eq_sSup_channelHolevoChiPureSet`) it suffices to match the supremum
over *all* pure ensembles. The `≥`-direction restricted to `≤ d²`-element ensembles is trivial
(they are a subset); the reverse is the cardinality reduction
`exists_pureLeCard_holevoChi_ge_of_isChannel`, which produces, for every pure ensemble, a
`≤ d²`-element pure ensemble of at least the same output-χ. -/
theorem channelHolevoChi_eq_sSup_channelHolevoChiPureLeCardSet {E : State S → State S}
    (hE : IsChannel E) :
    channelHolevoChi E = sSup (channelHolevoChiPureLeCardSet E) := by
  rw [channelHolevoChi_eq_sSup_channelHolevoChiPureSet hE]
  rcases (channelHolevoChiPureSet E).eq_empty_or_nonempty with hempty | hne
  · -- no pure ensembles at all ⇒ the `≤ d²` set is empty too
    have hle : channelHolevoChiPureLeCardSet E = ∅ :=
      Set.eq_empty_of_subset_empty (hempty ▸ channelHolevoChiPureLeCardSet_subset E)
    rw [hempty, hle]
  · have hbddPure : BddAbove (channelHolevoChiPureSet E) :=
      BddAbove.mono (channelHolevoChiPureSet_subset E) (channelHolevoChiSet_bddAbove E)
    have hbddLe : BddAbove (channelHolevoChiPureLeCardSet E) :=
      BddAbove.mono (channelHolevoChiPureLeCardSet_subset E) hbddPure
    apply le_antisymm
    · -- sSup pure ≤ sSup (≤ d²), via the cardinality reduction of each pure ensemble
      apply csSup_le hne
      rintro x ⟨m, q, hq, hqsum, ψ', rfl⟩
      obtain ⟨y, hy_mem, hxy⟩ := exists_pureLeCard_holevoChi_ge_of_isChannel hE q hq hqsum ψ'
      exact hxy.trans (le_csSup hbddLe hy_mem)
    · -- sSup (≤ d²) ≤ sSup pure; the `≤ d²` set is nonempty (reduce any pure witness)
      refine csSup_le_csSup hbddPure ?_ (channelHolevoChiPureLeCardSet_subset E)
      obtain ⟨x, m, q, hq, hqsum, ψ', rfl⟩ := hne
      obtain ⟨y, hy_mem, _⟩ := exists_pureLeCard_holevoChi_ge_of_isChannel hE q hq hqsum ψ'
      exact ⟨y, hy_mem⟩

end AxQM
