/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ProductStateCode
import AxQM.Postulates.API.MeasurementCoarseGrain

/-!
# Expurgation of a product-state code: from average error to maximum error (N&C eq. (12.83))

The random-coding half of the Holevo–Schumacher–Westmoreland theorem (Nielsen & Chuang,
Theorem 12.8) produces, for any rate `R < χ(E)`, a family of product-state codes whose **average**
error probability `p_av` tends to `0`.  The operational notion of achievability, however, demands
codes whose **maximum** error probability tends to `0` — Bob must decode *every* message reliably,
not merely a random one.  N&C's eq. (12.83) closes this gap by **expurgation**: from a code with
average error `p_av`, at least half the messages have error probability `≤ 2·p_av`, so *discarding
the worse half of the codewords* leaves a subcode, of essentially the same rate, whose maximum error
probability is at most `2·p_av`.

This file supplies the code-level ingredients of that step — the subcode
constructions `restrict`/`truncate` and the expurgation lemma `exists_expurgated` — working with the
`AxQM.ProductStateCode` model (`Core/ProductStateCode`):

* `AxQM.ProductStateCode.restrict` — the **subcode on a chosen set of messages**
  `G : Finset (Fin K)`.  Its encoder keeps only the codewords indexed by `G` (reindexed to
  `Fin G.card` via `Finset.equivFin`), and its decoder is the original decoder with the outcomes
  announcing a *discarded* message folded into the inconclusive element `E₀` — exactly the
  measurement coarse-graining `Measurement.coarseGrain` (`Postulates/API/MeasurementCoarseGrain`,
  N&C eq. (12.83)) along the map `Option (Fin K) → Option (Fin G.card)` that carries each retained
  message to itself and everything else to `none`.
* `AxQM.ProductStateCode.restrict_errorProb` — a **retained message keeps its error
  probability**: `(c.restrict G).errorProb k = c.errorProb ↑(G.equivFin.symm k)`.  The decoding
  outcome announcing a retained message has a singleton coarse-graining fibre, so
  `coarseGrain_bornProb_of_filter_eq_singleton` preserves its Born probability.
* `AxQM.ProductStateCode.exists_expurgated` — the **expurgation lemma** proper: for any
  code `c` with `K ≥ 1` messages there is a subcode `c'` on `K'` messages with `K ≤ 2·K'` (at
  least half the messages survive) and `c'.maxError ≤ 2·c.avgError`.  The message count bound is
  the Markov
  argument — the set of *bad* messages (error `> 2·p_av`) has size `≤ K/2`, since it would otherwise
  contribute more than `K·p_av` to the total error — and the maximum-error bound is immediate from
  `restrict_errorProb` on the retained (good) messages.
* `AxQM.ProductStateCode.truncate` — the **subcode on the first `m` messages** (`m ≤ K`):
  the initial-segment special case of `restrict`, kept as its own construction so the message set is
  *definitionally* `Fin m` (no `Finset.card` cast).  Its encoder reuses message `Fin.castLE h k`,
  and its decoder folds every discarded message (index `≥ m`, and the original inconclusive outcome)
  into the inconclusive element via `Measurement.coarseGrain`.  Companions
  `truncate_outputCodeword`, `truncate_successProb`, `truncate_errorProb` — a **retained message
  keeps its (output codeword, success, error) probability**, again by the singleton-fibre lemma
  `coarseGrain_bornProb_of_filter_eq_singleton` — and `truncate_maxError_le` — **truncation does not
  increase the maximum error**, `(c.truncate h).maxError ≤ c.maxError`.  This is the exact
  message-count trimming used to shrink an expurgated code to a target rate
  (`Core/ProductStateAvgAchievable`).

The subcodes `restrict`/`truncate` are built with the measurement constructor
`Measurement.coarseGrain`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

namespace ProductStateCode

variable {S : QSystem} {E : State S → State S} {n K : ℕ}

/-- **Restriction of a product-state code to a chosen set of messages** `G : Finset (Fin K)`
(the codeword-deletion construction underlying N&C's expurgation step, eq. (12.83)).

The subcode `c.restrict G` has message set `Fin G.card`, reindexing the retained messages via
`Finset.equivFin`.  Its encoder reuses message `↑(G.equivFin.symm k)` of `c`, and its decoder is
the original decoder coarse-grained along the outcome map that carries a retained message to its new
index and *every discarded message (and the original inconclusive outcome) to `none`* — i.e. the
outcomes announcing deleted codewords are folded into the subcode's inconclusive element `E₀`. -/
def restrict (c : ProductStateCode E n K) (G : Finset (Fin K)) :
    ProductStateCode E n G.card where
  encoder k := c.encoder (G.equivFin.symm k)
  decoder :=
    c.decoder.coarseGrain fun o =>
      match o with
      | none => none
      | some M => if h : M ∈ G then some (G.equivFin ⟨M, h⟩) else none

/-- The output codeword of a retained message is unchanged: `c.restrict G` reuses `c`'s codeword for
the original message `↑(G.equivFin.symm k)`. -/
theorem restrict_outputCodeword (c : ProductStateCode E n K) (G : Finset (Fin K))
    (k : Fin G.card) :
    (c.restrict G).outputCodeword k = c.outputCodeword (G.equivFin.symm k) := rfl

/-- **A retained message keeps its success probability.** The decoding outcome announcing a retained
message `k` has a singleton coarse-graining fibre — only the original message `↑(G.equivFin.symm k)`
maps to it — so `Measurement.coarseGrain_bornProb_of_filter_eq_singleton` preserves its Born
probability:
`(c.restrict G).successProb k = c.successProb ↑(G.equivFin.symm k)`. -/
theorem restrict_successProb (c : ProductStateCode E n K) (G : Finset (Fin K)) (k : Fin G.card) :
    (c.restrict G).successProb k = c.successProb (G.equivFin.symm k) := by
  classical
  set M₀ : Fin K := (G.equivFin.symm k : Fin K) with hM₀def
  have hM₀mem : M₀ ∈ G := (G.equivFin.symm k).2
  -- The coarse-graining outcome map used by `restrict`.
  set gmap : Option (Fin K) → Option (Fin G.card) := fun o =>
    match o with
    | none => none
    | some M => if h : M ∈ G then some (G.equivFin ⟨M, h⟩) else none with hgmap
  -- The fibre of the retained outcome `some k` is the singleton `{some M₀}`.
  have hfib : (Finset.univ.filter fun o => gmap o = some k) = {some M₀} := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    cases o with
    | none => simp [hgmap]
    | some M =>
        simp only [hgmap]
        by_cases hM : M ∈ G
        · rw [dite_eq_left hM]
          simp only [Option.some.injEq, ← Equiv.eq_symm_apply, Subtype.ext_iff, ← hM₀def]
        · rw [dite_eq_right hM]
          simp only [reduceCtorEq, Option.some.injEq, false_iff]
          rintro rfl; exact hM hM₀mem
  -- Read off the born probabilities through the singleton-fibre coarse-graining lemma.
  exact Measurement.coarseGrain_bornProb_of_filter_eq_singleton c.decoder gmap
    (c.outputCodeword M₀) (some k) (some M₀) hfib

/-- **A retained message keeps its error probability**:
`(c.restrict G).errorProb k = c.errorProb ↑(G.equivFin.symm k)`.  Immediate from
`restrict_successProb` and `errorProb = 1 − successProb`. -/
theorem restrict_errorProb (c : ProductStateCode E n K) (G : Finset (Fin K)) (k : Fin G.card) :
    (c.restrict G).errorProb k = c.errorProb (G.equivFin.symm k) := by
  simp only [ProductStateCode.errorProb, restrict_successProb]

/-- **The expurgation lemma** (Nielsen & Chuang, Theorem 12.8, eq. (12.83)).  For any product-state
code `c` with `K ≥ 1` messages there is a subcode `c'` on `K'` messages such that at least half the
messages survive (`K ≤ 2·K'`) and the subcode's *maximum* error probability is at most twice the
original *average* error probability (`c'.maxError ≤ 2·c.avgError`).

Take `G` to be the *good* messages, those with `errorProb ≤ 2·p_av`, and `c' = c.restrict G`.  Each
retained message keeps its error probability (`restrict_errorProb`), which is `≤ 2·p_av` by
construction, giving the maximum-error bound.  For the count bound, the *bad* messages
`Gᶜ` (error `> 2·p_av`) satisfy `2·|Gᶜ| ≤ K` by Markov's inequality — otherwise they alone would
contribute more than `K·p_av` to the total error `∑ errorProb = K·p_av` — and `|G| + |Gᶜ| = K` then
gives `K ≤ 2·|G| = 2·K'`. -/
theorem exists_expurgated [NeZero K] (c : ProductStateCode E n K) :
    ∃ (K' : ℕ) (c' : ProductStateCode E n K'),
      K ≤ 2 * K' ∧ c'.maxError ≤ 2 * c.avgError := by
  classical
  have hKne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  -- The good messages: those whose error probability is at most twice the average.
  set G : Finset (Fin K) := Finset.univ.filter fun M => c.errorProb M ≤ 2 * c.avgError with hGdef
  have hGprop : ∀ M ∈ G, c.errorProb M ≤ 2 * c.avgError := by
    intro M hM; rw [hGdef, Finset.mem_filter] at hM; exact hM.2
  have hbad : ∀ M ∈ Gᶜ, 2 * c.avgError < c.errorProb M := by
    intro M hM
    rw [hGdef, Finset.mem_compl, Finset.mem_filter, not_and, not_le] at hM
    exact hM (Finset.mem_univ M)
  -- Total error is `K · p_av`.
  have hsumErr : ∑ M, c.errorProb M = (K : ℝ) * c.avgError := by
    rw [ProductStateCode.avgError]; field_simp
  -- Markov: at most half the messages are bad, `2·|Gᶜ| ≤ K`.
  have h2B : 2 * (Gᶜ : Finset (Fin K)).card ≤ K := by
    rcases c.avgError_nonneg.lt_or_eq with hpos | hzero
    · -- `p_av > 0`: the bad messages each carry error `> 2·p_av`, so Markov cancels `p_av`.
      have hchain : ((Gᶜ : Finset (Fin K)).card : ℝ) * (2 * c.avgError) ≤ (K : ℝ) * c.avgError := by
        calc ((Gᶜ : Finset (Fin K)).card : ℝ) * (2 * c.avgError)
            = ∑ _M ∈ Gᶜ, 2 * c.avgError := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ M ∈ Gᶜ, c.errorProb M := Finset.sum_le_sum fun M hM => le_of_lt (hbad M hM)
          _ ≤ ∑ M, c.errorProb M :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun M _ _ => c.errorProb_nonneg M)
          _ = (K : ℝ) * c.avgError := hsumErr
      have h2c : (2 * ((Gᶜ : Finset (Fin K)).card : ℝ)) ≤ (K : ℝ) :=
        le_of_mul_le_mul_right (by nlinarith [hchain]) hpos
      exact_mod_cast h2c
    · -- `p_av = 0`: every error probability is `0`, so there are no bad messages.
      have hsum0 : ∑ M, c.errorProb M = 0 := by rw [hsumErr, ← hzero, mul_zero]
      have hallzero := (Finset.sum_eq_zero_iff_of_nonneg fun M _ => c.errorProb_nonneg M).mp hsum0
      have hcompl : (Gᶜ : Finset (Fin K)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro M hM
        have hlt := hbad M hM
        rw [hallzero M (Finset.mem_univ M), ← hzero, mul_zero] at hlt
        exact lt_irrefl (0 : ℝ) hlt
      rw [hcompl, Finset.card_empty, mul_zero]; exact Nat.zero_le K
  -- `|G| + |Gᶜ| = K`, hence `K ≤ 2·|G|`.
  have hcard : G.card + (Gᶜ : Finset (Fin K)).card = K := by
    have h := Finset.card_add_card_compl G; rwa [Fintype.card_fin] at h
  refine ⟨G.card, c.restrict G, by omega, ?_⟩
  -- The maximum error of the subcode: every retained message is good.
  rw [ProductStateCode.maxError]
  refine Real.iSup_le (fun k => ?_) (by have := c.avgError_nonneg; linarith)
  rw [restrict_errorProb]
  exact hGprop _ (G.equivFin.symm k).2

/-- **Truncation of a product-state code to its first `m` messages** (`m ≤ K`).  The subcode
`c.truncate h` has message set `Fin m`, encodes message `k` as `c`'s message `Fin.castLE h k`, and
decodes with `c`'s decoder coarse-grained (`Measurement.coarseGrain`) along the outcome map carrying
each retained message `M` with `M < m` to itself and *everything else* (larger messages, and the
original inconclusive outcome) to `none`.  It is the initial-segment special case of `restrict`,
kept as its own construction so the message set is *definitionally* `Fin m` (no `Finset.card`
cast) — the exact message count needed to shrink an expurgated code to a target rate. -/
def truncate (c : ProductStateCode E n K) {m : ℕ} (h : m ≤ K) : ProductStateCode E n m where
  encoder k := c.encoder (Fin.castLE h k)
  decoder :=
    c.decoder.coarseGrain fun o =>
      match o with
      | none => none
      | some M => if hM : M.val < m then some ⟨M.val, hM⟩ else none

/-- The output codeword of a retained message is unchanged: `c.truncate h` reuses `c`'s codeword for
the original message `Fin.castLE h k`. -/
theorem truncate_outputCodeword (c : ProductStateCode E n K) {m : ℕ} (h : m ≤ K) (k : Fin m) :
    (c.truncate h).outputCodeword k = c.outputCodeword (Fin.castLE h k) := rfl

/-- **A retained message keeps its success probability**:
`(c.truncate h).successProb k = c.successProb (Fin.castLE h k)`.  The decoding outcome announcing a
retained message `k` has a singleton coarse-graining fibre — only the original message
`Fin.castLE h k` maps to it — so `Measurement.coarseGrain_bornProb_of_filter_eq_singleton` preserves
its Born probability. -/
theorem truncate_successProb (c : ProductStateCode E n K) {m : ℕ} (h : m ≤ K) (k : Fin m) :
    (c.truncate h).successProb k = c.successProb (Fin.castLE h k) := by
  classical
  set gmap : Option (Fin K) → Option (Fin m) := fun o =>
    match o with
    | none => none
    | some M => if hM : M.val < m then some ⟨M.val, hM⟩ else none with hgmap
  -- The fibre of the retained outcome `some k` is the singleton `{some (Fin.castLE h k)}`.
  have hfib : (Finset.univ.filter fun o => gmap o = some k) = {some (Fin.castLE h k)} := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    cases o with
    | none => simp [hgmap]
    | some M =>
        simp only [hgmap]
        by_cases hM : M.val < m
        · rw [dite_eq_left hM]
          simp only [Option.some.injEq, Fin.ext_iff, Fin.val_castLE]
        · rw [dite_eq_right hM]
          simp only [reduceCtorEq, Option.some.injEq, false_iff]
          rintro rfl
          exact hM (by simp only [Fin.val_castLE]; exact k.2)
  exact Measurement.coarseGrain_bornProb_of_filter_eq_singleton c.decoder gmap
    (c.outputCodeword (Fin.castLE h k)) (some k) (some (Fin.castLE h k)) hfib

/-- **A retained message keeps its error probability**:
`(c.truncate h).errorProb k = c.errorProb (Fin.castLE h k)`. -/
theorem truncate_errorProb (c : ProductStateCode E n K) {m : ℕ} (h : m ≤ K) (k : Fin m) :
    (c.truncate h).errorProb k = c.errorProb (Fin.castLE h k) := by
  simp only [ProductStateCode.errorProb, truncate_successProb]

/-- **Truncation does not increase the maximum error probability**: every retained message of
`c.truncate h` keeps its (original) error probability, which is at most `c.maxError`, so
`(c.truncate h).maxError ≤ c.maxError`. -/
theorem truncate_maxError_le (c : ProductStateCode E n K) {m : ℕ} (h : m ≤ K) :
    (c.truncate h).maxError ≤ c.maxError := by
  rw [ProductStateCode.maxError]
  refine Real.iSup_le (fun k => ?_) c.maxError_nonneg
  rw [truncate_errorProb]
  exact c.errorProb_le_maxError _

end ProductStateCode

end AxQM
