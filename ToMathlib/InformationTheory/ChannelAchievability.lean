/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.ChannelRandomCodingLimit
public import ToMathlib.InformationTheory.ChannelExpurgation

/-!
# Fixed-input achievability of Shannon's noisy channel coding theorem

The achievability half of Shannon's noisy channel coding theorem (Nielsen & Chuang, Theorem 12.7;
Cover–Thomas, Theorem 7.7.1) states that every rate below the channel mutual information is
achievable. This file assembles the pieces developed upstream into the **fixed-input** achievability
statement

`Real.isAchievableRate_of_lt_channelMutualInfo` :
  `R · log 2 < channelMutualInfo q p → IsAchievableRate q R`,

for a channel `q`, an input distribution `p`, and a rate `R` (in bits). Lifting this over the
capacity-attaining input distribution (Theorem 12.7's `max_{p(x)} H(X : Y)`) and combining with the
proven converse closes the full identity `C(N) = max_{p(x)} H(X : Y)`; that final step is not
proved in this file.

## Proof outline

The three upstream inputs are the random-coding limit
`Real.tendsto_expectedError_channelRandomCode` (the codebook-*averaged* error tends to `0` for a
rate below the mutual information), the expurgation lemma `Real.exists_channelCode_maxErrorProb_le`
(average error `≤ a` on `M` messages ⟹ *maximum* error `≤ 2a` on `⌈M/2⌉ = (M + 1) / 2` messages),
and the definition of achievability `Real.IsAchievableRate` (a family of block codes with
`⌈2 ^ (n R)⌉ = ⌈exp (n · R · log 2)⌉₊` messages whose maximum error tends to `0`). Assembling them:

* **Probabilistic method** (`Real.exists_le_weighted_sum`): the codebook-averaged error is a
  probability-weighted mean over codebooks, so some deterministic codebook realises an average error
  no larger than that mean. Hence for every `n` there is a deterministic joint-typicality code with
  average error `≤ 𝔼_C[avg error]`.
* **Expurgation per `n`** (`Real.exists_tendsto_maxErrorProb_of_lt_channelMutualInfo`): expurgating
  that deterministic code yields, for a rate `R'` with `R' · log 2 < channelMutualInfo q p`, a code
  on `(⌈exp (n R' log 2)⌉₊ + 1) / 2` messages with *maximum* error bounded by
  `2 · 𝔼_C[avg error]`, a vanishing sequence.
* **Assembly** (`Real.isAchievableRate_of_forall_exists_maxErrorProb_le`): a family of codes on
  `K n ≥ ⌈exp (n R log 2)⌉₊` messages with maximum error `→ 0` gives `IsAchievableRate q R`, by
  restricting each code (via `Real.ChannelCode.comp` with the canonical inclusion `Fin.castLE`) to
  exactly `⌈exp (n R log 2)⌉₊` messages, which only shrinks the error, and squeezing.

The **rate arithmetic** ties them together: expurgation halves the message count, so to achieve the
target rate `R` (with `R · log 2 < channelMutualInfo q p`) the random coding is run at a strictly
larger rate `R' = R + (channelMutualInfo q p − R · log 2) / (2 · log 2)` (still below the mutual
information). Since `R < R'`, the expurgated count
`(⌈exp (n R' log 2)⌉₊ + 1) / 2 ≥ ⌈exp (n R log 2)⌉₊` eventually, so the assembly lemma applies.
Rates `R ≤ 0` are handled directly by single-message codes.

## Main declarations

* `Real.exists_le_weighted_sum` — some point is at most a probability-weighted mean.
* `Real.isAchievableRate_of_forall_exists_maxErrorProb_le` — build achievability from a family of
  codes with enough messages and vanishing maximum error.
* `Real.exists_tendsto_maxErrorProb_of_lt_channelMutualInfo` — random coding + probabilistic method
  + expurgation: a vanishing sequence bounding the maximum error of expurgated codes.
* `Real.isAchievableRate_of_lt_channelMutualInfo` — **fixed-input achievability**: a rate below the
  channel mutual information is achievable.
-/

@[expose] public section

open Finset Filter Topology

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### The probabilistic method -/

/-- **A point below the weighted mean.** If `w` is a probability weight on a finite type `D`
(`0 ≤ w d` and `∑ d, w d = 1`), then some point's `f`-value is at most the `w`-weighted mean
`∑ d, w d * f d`. This is the probabilistic method used to extract a good deterministic codebook
from the codebook-averaged decoding error. -/
theorem exists_le_weighted_sum {D : Type*} [Fintype D] {w f : D → ℝ}
    (hw0 : ∀ d, 0 ≤ w d) (hw1 : ∑ d, w d = 1) : ∃ d, f d ≤ ∑ d', w d' * f d' := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  set E := ∑ d', w d' * f d' with hE
  have hnn : ∀ d ∈ (univ : Finset D), 0 ≤ w d * (f d - E) :=
    fun d _ => mul_nonneg (hw0 d) (by linarith [hcon d])
  have hz : ∑ d, w d * (f d - E) = 0 := by
    have hexpand : ∑ d, w d * (f d - E) = (∑ d, w d * f d) - (∑ d, w d) * E := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hexpand, hw1, one_mul, ← hE, sub_self]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
  have hw0all : ∀ d, w d = 0 := fun d =>
    (mul_eq_zero.mp (hall d (mem_univ d))).resolve_right (sub_ne_zero.mpr (ne_of_gt (hcon d)))
  exact one_ne_zero (hw1.symm.trans (Finset.sum_eq_zero fun d _ => hw0all d))

/-! ### Assembling a rate from per-`n` codes -/

omit [Fintype ι] in
/-- **Achievability from a family of large-enough codes.** If, for every block length `n`, there is
a block code on `K n` messages with maximum error `≤ g n`, where `g → 0` and eventually
`⌈exp (n R log 2)⌉₊ ≤ K n`, then the rate `R` is achievable. Each code is restricted (via
`ChannelCode.comp` along the canonical inclusion `Fin.castLE`) to exactly `⌈exp (n R log 2)⌉₊` of
its messages — which only shrinks the maximum error — and the resulting family is squeezed to
`0`. -/
theorem isAchievableRate_of_forall_exists_maxErrorProb_le {q : ι → κ → ℝ} (hN : IsChannel q)
    [Nonempty ι] {R : ℝ} {K : ℕ → ℕ} {g : ℕ → ℝ}
    (hcode : ∀ n, ∃ code : ChannelCode ι κ n (K n), code.maxErrorProb q ≤ g n)
    (hK : ∀ᶠ (n : ℕ) in atTop, ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ ≤ K n)
    (hg : Tendsto g atTop (𝓝 0)) : IsAchievableRate q R := by
  classical
  choose code hcodele using hcode
  refine ⟨fun n : ℕ => if h : ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ ≤ K n
      then (code n).comp (Fin.castLE h) ⟨0, Nat.ceil_pos.mpr (Real.exp_pos _)⟩
      else ⟨fun _ _ => Classical.arbitrary ι,
        fun _ => ⟨0, Nat.ceil_pos.mpr (Real.exp_pos _)⟩⟩, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Filter.Eventually.of_forall fun n => ChannelCode.maxErrorProb_nonneg hN _) ?_
  filter_upwards [hK] with n hn
  rw [dite_eq_left hn]
  exact ChannelCode.maxErrorProb_comp_le hN (code n) (Fin.castLE_injective hn) _
    (fun i => (ChannelCode.condErrorProb_le_maxErrorProb q (code n) _).trans (hcodele n))
    ((ChannelCode.maxErrorProb_nonneg hN (code n)).trans (hcodele n))

/-! ### Random coding, the probabilistic method, and expurgation -/

/-- **Expurgated deterministic codes with vanishing maximum error.** For a channel `q`, an input
distribution `p`, and a rate `R` (in bits) with `R · log 2 < channelMutualInfo q p`, there is a
sequence `e → 0` and, for every block length `n`, a block code on `(⌈exp (n R log 2)⌉₊ + 1) / 2`
messages whose *maximum* decoding error is at most `e n`.

The random-coding limit `tendsto_expectedError_channelRandomCode` drives the codebook-averaged error
to `0`; the probabilistic method (`exists_le_weighted_sum`) extracts, for each `n`, a deterministic
joint-typicality code whose average error is at most that expectation; expurgation
(`exists_channelCode_maxErrorProb_le`) upgrades the average bound to a maximum bound at the cost of
halving the message count. Thus `e n = 2 · 𝔼_C[avg error] → 0`. -/
theorem exists_tendsto_maxErrorProb_of_lt_channelMutualInfo {q : ι → κ → ℝ} (hN : IsChannel q)
    {p : ι → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {R : ℝ}
    (hR : R * Real.log 2 < channelMutualInfo q p) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ n, ∃ code : ChannelCode ι κ n ((⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ + 1) / 2),
        code.maxErrorProb q ≤ e n := by
  obtain ⟨ε, _, htend⟩ := tendsto_expectedError_channelRandomCode hN hp0 hp1 hR
  refine ⟨fun n => 2 * (∑ C : Fin ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ → (Fin n → ι),
      channelCodebookProb p C * ((⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ)⁻¹ *
        ∑ m, (channelJointTypicalCode q p n ε
          ⟨0, Nat.ceil_pos.mpr (Real.exp_pos _)⟩ C).condErrorProb q m)), ?_, ?_⟩
  · simpa using (htend fun n => ⟨0, Nat.ceil_pos.mpr (Real.exp_pos _)⟩).const_mul 2
  · intro n
    obtain ⟨C, hC⟩ := exists_le_weighted_sum
      (f := fun C => (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ)⁻¹ *
        ∑ m, (channelJointTypicalCode q p n ε
          ⟨0, Nat.ceil_pos.mpr (Real.exp_pos _)⟩ C).condErrorProb q m)
      (fun C => channelCodebookProb_nonneg hp0 C) (sum_channelCodebookProb hp1)
    exact exists_channelCode_maxErrorProb_le hN (Nat.ceil_pos.mpr (Real.exp_pos _))
      (channelJointTypicalCode q p n ε ⟨0, Nat.ceil_pos.mpr (Real.exp_pos _)⟩ C) hC

/-! ### Fixed-input achievability -/

/-- **Fixed-input achievability** (achievability half of Nielsen & Chuang, Theorem 12.7). For a
channel `q`, an input distribution `p`, and a rate `R` (in bits) with
`R · log 2 < channelMutualInfo q p = H(X : Y)`, the rate `R` is achievable: there is a family of
block codes with `⌈2 ^ (n R)⌉` messages whose block error probability tends to `0`.

Rates `R ≤ 0` are trivially achievable with single-message codes. For `R > 0`, the random coding is
run at the strictly larger rate `R' = R + (channelMutualInfo q p − R · log 2) / (2 · log 2)` (still
below the mutual information); the expurgated codes it produces have
`(⌈exp (n R' log 2)⌉₊ + 1) / 2 ≥ ⌈exp (n R log 2)⌉₊` messages eventually — because `R < R'` makes
the message count grow strictly faster — so the assembly lemma
`isAchievableRate_of_forall_exists_maxErrorProb_le` applies. -/
theorem isAchievableRate_of_lt_channelMutualInfo {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {R : ℝ}
    (hR : R * Real.log 2 < channelMutualInfo q p) : IsAchievableRate q R := by
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hp1
    exact one_ne_zero hp1.symm
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt R 0 with hR0 | hR0
  · -- `R ≤ 0`: single-message codes have zero error.
    refine ⟨fun n => ⟨fun _ _ => Classical.arbitrary ι,
      fun _ => ⟨0, Nat.ceil_pos.mpr (Real.exp_pos _)⟩⟩, ?_⟩
    refine tendsto_const_nhds.congr fun n => ?_
    have hstep : (n : ℝ) * R * Real.log 2 ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨mul_nonpos_iff.mpr (Or.inl ⟨Nat.cast_nonneg n, hR0⟩), hlog2.le⟩)
    refine (ChannelCode.maxErrorProb_eq_zero_of_le_one _ (Nat.ceil_le.mpr ?_)).symm
    rw [Nat.cast_one]
    exact (Real.exp_le_exp.mpr hstep).trans_eq Real.exp_zero
  · -- `R > 0`: random coding at a strictly larger rate `R'`, then expurgate and restrict.
    set R' := R + (channelMutualInfo q p - R * Real.log 2) / (2 * Real.log 2) with hR'def
    have hgap : 0 < (channelMutualInfo q p - R * Real.log 2) / (2 * Real.log 2) :=
      div_pos (by linarith) (by positivity)
    have hRR' : R < R' := by rw [hR'def]; linarith
    have hR'lt : R' * Real.log 2 < channelMutualInfo q p := by
      have h2 : R' * Real.log 2 = (R * Real.log 2 + channelMutualInfo q p) / 2 := by
        rw [hR'def]; field_simp; ring
      rw [h2]; linarith
    obtain ⟨e, he0, hcodes⟩ :=
      exists_tendsto_maxErrorProb_of_lt_channelMutualInfo hN hp0 hp1 hR'lt
    have hlin : Tendsto (fun n : ℕ => (n : ℝ) * ((R' - R) * Real.log 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos (by linarith) hlog2)
    have ht : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * ((R' - R) * Real.log 2))) atTop atTop :=
      Real.tendsto_exp_atTop.comp hlin
    refine isAchievableRate_of_forall_exists_maxErrorProb_le
      (K := fun n => (⌈Real.exp ((n : ℝ) * R' * Real.log 2)⌉₊ + 1) / 2) (g := e) hN hcodes ?_ he0
    filter_upwards [ht.eventually_ge_atTop 3] with n hn3
    -- Real bound: `exp (n R' log 2) ≥ 2 · exp (n R log 2) + 1`.
    have hexpR : (1 : ℝ) ≤ Real.exp ((n : ℝ) * R * Real.log 2) :=
      Real.one_le_exp (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hR0.le) hlog2.le)
    have hsplit : (n : ℝ) * R' * Real.log 2
        = (n : ℝ) * R * Real.log 2 + (n : ℝ) * ((R' - R) * Real.log 2) := by ring
    have hbig : 2 * Real.exp ((n : ℝ) * R * Real.log 2) + 1
        ≤ Real.exp ((n : ℝ) * R' * Real.log 2) := by
      rw [hsplit, Real.exp_add]
      nlinarith [hexpR, hn3, mul_nonneg (sub_nonneg.mpr hexpR) (sub_nonneg.mpr hn3),
        Real.exp_pos ((n : ℝ) * ((R' - R) * Real.log 2))]
    -- Convert to the natural-number count inequality and discharge with `omega`.
    have hnat : 2 * ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊
        ≤ ⌈Real.exp ((n : ℝ) * R' * Real.log 2)⌉₊ + 1 := by
      have hca : (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ)
          < Real.exp ((n : ℝ) * R * Real.log 2) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
      have hcb : Real.exp ((n : ℝ) * R' * Real.log 2)
          ≤ (⌈Real.exp ((n : ℝ) * R' * Real.log 2)⌉₊ : ℝ) := Nat.le_ceil _
      have hcast : ((2 * ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℕ) : ℝ)
          ≤ ((⌈Real.exp ((n : ℝ) * R' * Real.log 2)⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith [hca, hcb, hbig]
      exact_mod_cast hcast
    omega

end Real
