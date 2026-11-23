/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.NoisyChannel

/-!
# Expurgation: from average error to maximum error (Shannon's noisy channel coding theorem)

The achievability half of Shannon's noisy channel coding theorem (Nielsen & Chuang, Theorem 12.7;
Cover–Thomas, Theorem 7.7.1) produces, by random coding, a block code whose *average* decoding error
over the messages is small. Reliable communication in the sense of Nielsen & Chuang eq. (12.66) is
measured by the *maximum* decoding error `Real.ChannelCode.maxErrorProb`, so the average bound must
be upgraded to a maximum bound. This is the standard **expurgation** step: throw away the worst half
of the codewords, and the surviving half have small maximum error at essentially the same rate.

This file is pure block-code combinatorics — it does not use the random-coding machinery — and
provides the two reusable pieces:

* `Real.ChannelCode.comp` — the **sub-code** selecting the `g`-indexed sub-family of the messages of
  a code (`g : Fin M' → Fin M`), re-indexing the decoder accordingly (decode an output to the unique
  message `i` with `g i = code.decode y`, falling back to a default message otherwise). For an
  injective `g`, selecting messages only shrinks each conditional error event, so
  `Real.ChannelCode.condErrorProb_comp_le` bounds each conditional error of the sub-code by the
  corresponding error of the parent code, and `Real.ChannelCode.maxErrorProb_comp_le` bounds the
  block error of the sub-code by any common bound on the selected conditional errors.
* `Real.exists_channelCode_maxErrorProb_le` — the **expurgation existence** statement: a code on `M`
  messages with average error `M⁻¹ ∑ₘ condErrorProb m ≤ a` has a sub-code on `⌈M/2⌉ = (M + 1) / 2`
  messages with `maxErrorProb ≤ 2 a`. A Markov/counting argument shows at least `⌈M/2⌉` of the
  messages have conditional error `≤ 2 a`; selecting exactly those via `comp` and
  `Finset.orderEmbOfCardLe` bounds the maximum error.

The `n → ∞` assembly (extracting a good deterministic codebook from the random-coding limit by the
probabilistic method, expurgating it, and matching the message count to the rate) is not in this
file.

## Main declarations

* `Real.ChannelCode.comp` — the `g`-selected sub-code.
* `Real.ChannelCode.condErrorProb_comp_le` — a selected message's conditional error is at most the
  parent's.
* `Real.ChannelCode.maxErrorProb_comp_le` — selecting messages does not increase the block error.
* `Real.exists_channelCode_maxErrorProb_le` — expurgation: average error `≤ a` on `M` messages gives
  maximum error `≤ 2 a` on `(M + 1) / 2` messages.
-/

@[expose] public section

open Finset

namespace Real

variable {ι κ : Type*} [Fintype κ]

/-! ### Selecting a sub-family of messages -/

open Classical in
/-- The **sub-code** of `code : ChannelCode ι κ n M` selecting the `g`-indexed sub-family of its
messages, for `g : Fin M' → Fin M`. Message `i : Fin M'` is encoded as the parent codeword
`code.encode (g i)`; an output string `y` is decoded to the unique `i` with `g i = code.decode y`
when one exists (for injective `g` there is at most one), and to the fallback message `dflt`
otherwise. When `g` selects a subset of messages this restricts the code to that subset. -/
noncomputable def ChannelCode.comp {n M M' : ℕ} (code : ChannelCode ι κ n M) (g : Fin M' → Fin M)
    (dflt : Fin M') : ChannelCode ι κ n M' where
  encode i := code.encode (g i)
  decode y := if h : ∃ i, g i = code.decode y then h.choose else dflt

/-- **Selecting messages shrinks the conditional error.** For an injective selection
`g : Fin M' → Fin M`, the conditional block-error probability of message `i` in the sub-code
`code.comp g dflt` is at most that of the corresponding parent message `g i`: a decoding error in
the sub-code forces the parent decoder to miss `g i` (if the parent decoded to `g i`, injectivity
makes the sub-code decode to `i`), so the sub-code's error event is a subset of the parent's. -/
theorem ChannelCode.condErrorProb_comp_le {q : ι → κ → ℝ} (hN : IsChannel q) {n M M' : ℕ}
    (code : ChannelCode ι κ n M) {g : Fin M' → Fin M} (hg : Function.Injective g) (dflt : Fin M')
    (i : Fin M') : (code.comp g dflt).condErrorProb q i ≤ code.condErrorProb q (g i) := by
  classical
  have henc : (code.comp g dflt).encode i = code.encode (g i) := rfl
  rw [ChannelCode.condErrorProb, ChannelCode.condErrorProb, henc]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => channelSeqProb_nonneg hN _ _)
  intro y hy
  simp only [mem_filter, mem_univ, true_and] at hy ⊢
  intro hcontra
  apply hy
  change (if h : ∃ i', g i' = code.decode y then h.choose else dflt) = i
  have hex : ∃ i', g i' = code.decode y := ⟨i, hcontra.symm⟩
  rw [dite_eq_left hex]
  exact hg (hex.choose_spec.trans hcontra)

/-- **Selecting messages does not increase the block error.** If every selected parent message has
conditional error at most `b` (with `0 ≤ b`), then the block-error probability of the sub-code
`code.comp g dflt` is at most `b`. Combined with `condErrorProb_comp_le`, this is the mechanism of
expurgation: dropping the high-error messages leaves a code with a uniformly small block error. -/
theorem ChannelCode.maxErrorProb_comp_le {q : ι → κ → ℝ} (hN : IsChannel q) {n M M' : ℕ}
    (code : ChannelCode ι κ n M) {g : Fin M' → Fin M} (hg : Function.Injective g) (dflt : Fin M')
    {b : ℝ} (hb : ∀ i, code.condErrorProb q (g i) ≤ b) (hb0 : 0 ≤ b) :
    (code.comp g dflt).maxErrorProb q ≤ b := by
  rw [ChannelCode.maxErrorProb]
  exact Real.iSup_le (fun i => (code.condErrorProb_comp_le hN hg dflt i).trans (hb i)) hb0

/-! ### Expurgation -/

/-- **Expurgation (average error → maximum error).** A block code on `M > 0` messages whose
*average* conditional error `M⁻¹ ∑ₘ condErrorProb m` is at most `a` has a sub-code on
`⌈M/2⌉ = (M + 1) / 2`
messages whose *maximum* error `maxErrorProb` is at most `2 a`.

By a Markov/counting argument, at most `⌊M/2⌋` messages can have conditional error exceeding `2 a`
(otherwise the average would exceed `a`), so at least `(M + 1) / 2` messages have conditional error
`≤ 2 a`. Selecting exactly `(M + 1) / 2` of those good messages with `Finset.orderEmbOfCardLe` and
forming the corresponding sub-code (`ChannelCode.comp`) bounds every conditional error — hence the
block error — by `2 a` (`maxErrorProb_comp_le`). This is Cover–Thomas Theorem 7.7.1's expurgation
step, which upgrades the codebook-averaged error of the random-coding argument to the worst-case
error of Nielsen & Chuang eq. (12.66). -/
theorem exists_channelCode_maxErrorProb_le {q : ι → κ → ℝ} (hN : IsChannel q) {n M : ℕ} (hM : 0 < M)
    (code : ChannelCode ι κ n M) {a : ℝ}
    (havg : (M : ℝ)⁻¹ * ∑ m, code.condErrorProb q m ≤ a) :
    ∃ code' : ChannelCode ι κ n ((M + 1) / 2), code'.maxErrorProb q ≤ 2 * a := by
  classical
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set S : ℝ := ∑ m, code.condErrorProb q m with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ => code.condErrorProb_nonneg hN m
  -- `0 ≤ a` and `S ≤ M · a`.
  have ha0 : 0 ≤ a := le_trans (by positivity) havg
  have hSle : S ≤ (M : ℝ) * a := by
    have h := mul_le_mul_of_nonneg_left havg hMR.le
    rwa [mul_inv_cancel_left₀ (ne_of_gt hMR)] at h
  -- The good and bad message sets.
  set Bad : Finset (Fin M) := univ.filter (fun m => ¬ code.condErrorProb q m ≤ 2 * a) with hBaddef
  set Good : Finset (Fin M) := univ.filter (fun m => code.condErrorProb q m ≤ 2 * a) with hGooddef
  -- Markov: the bad messages carry mass `≥ Bad.card · (2a)`, which is `≤ S ≤ M · a`.
  have hMarkov : (Bad.card : ℝ) * (2 * a) ≤ (M : ℝ) * a := by
    calc (Bad.card : ℝ) * (2 * a) = ∑ _m ∈ Bad, (2 * a) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Bad, code.condErrorProb q m := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [hBaddef, mem_filter, not_le] at hm
          exact hm.2.le
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun m _ _ => code.condErrorProb_nonneg hN m)
      _ ≤ (M : ℝ) * a := hSle
  -- Hence at most `⌊M/2⌋` bad messages, so at least `(M+1)/2` good ones.
  have hBadcard : 2 * Bad.card ≤ M := by
    rcases eq_or_lt_of_le ha0 with ha | ha
    · -- `a = 0`: the average is `0`, so every conditional error is `0`, so `Bad` is empty.
      have hS0 : S = 0 := le_antisymm (by rw [← ha] at hSle; simpa using hSle) hSnn
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun m _ => code.condErrorProb_nonneg hN m)).mp (hSdef ▸ hS0)
      have hBadempty : Bad = ∅ := by
        rw [hBaddef, Finset.filter_eq_empty_iff]
        intro m _
        rw [not_not, hall m (mem_univ m)]
        linarith
      rw [hBadempty]; simp
    · -- `0 < a`: cancel `a` from the Markov inequality.
      have key : (2 * (Bad.card : ℝ)) * a ≤ (M : ℝ) * a := by
        calc (2 * (Bad.card : ℝ)) * a = (Bad.card : ℝ) * (2 * a) := by ring
          _ ≤ (M : ℝ) * a := hMarkov
      have : (2 * (Bad.card : ℝ)) ≤ (M : ℝ) := le_of_mul_le_mul_right key ha
      exact_mod_cast this
  -- `Good` and `Bad` partition the messages, so `(M+1)/2 ≤ Good.card`.
  have hpart : Good.card + Bad.card = M := by
    rw [hGooddef, hBaddef]
    simpa using Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M)))
      (fun m => code.condErrorProb q m ≤ 2 * a)
  have hGoodcard : (M + 1) / 2 ≤ Good.card := by omega
  -- Select `(M+1)/2` good messages as an injective `g`; their parent errors are all `≤ 2a`.
  set g : Fin ((M + 1) / 2) → Fin M := ⇑(Good.orderEmbOfCardLe hGoodcard) with hgdef
  have hginj : Function.Injective g := (Good.orderEmbOfCardLe hGoodcard).injective
  have hgle : ∀ i, code.condErrorProb q (g i) ≤ 2 * a := by
    intro i
    have hmem : g i ∈ Good := Good.orderEmbOfCardLe_mem hGoodcard i
    rw [hGooddef, mem_filter] at hmem
    exact hmem.2
  -- The corresponding sub-code has maximum error `≤ 2a`.
  have hM'pos : 0 < (M + 1) / 2 := by omega
  exact ⟨code.comp g ⟨0, hM'pos⟩, code.maxErrorProb_comp_le hN hginj _ hgle (by linarith)⟩

end Real
