/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.ChannelRandomCoding
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The `n → ∞` limit of the random-coding error (Shannon's noisy channel coding theorem)

The achievability half of Shannon's noisy channel coding theorem (Nielsen & Chuang, Theorem 12.7;
Cover–Thomas, ch. 7.7) drives the codebook-averaged decoding error of the joint-typicality random
code to `0`. The exact per-`n` bound is `Real.channelRandomCode_expectedAvgError_le`
(`ToMathlib.InformationTheory.ChannelRandomCoding`):

`𝔼_C[avg error] ≤ (1 − ∑_{typ} channelPairSeqProb q p) + (M − 1) · exp(-n (H(X:Y) − 3ε))`,

for a codebook of `M` messages, block length `n`, and tolerance `ε`. This file takes the limit: for
a rate `R` (in bits) with `R · log 2 < H(X : Y) = channelMutualInfo q p` and the message count
`M(n) = ⌈exp(n · R · log 2)⌉₊ = ⌈2^{nR}⌉` of `Real.IsAchievableRate`, both terms of the bound vanish
as `n → ∞`, so the codebook-averaged error tends to `0`
(`Real.tendsto_expectedError_channelRandomCode`).

The two contributions decay for independent reasons, each isolated as a lemma:

* **The true-atypical term** `1 − ∑_{typ} channelPairSeqProb q p → 0`
  (`Real.tendsto_one_sub_sum_channelTypicalPairs`) is the joint asymptotic equipartition property:
  the jointly typical set carries probability `→ 1` (`Real.exists_le_sum_channelTypicalPairs`), and
  it is a sub-mass of the total probability `1` (`Real.sum_channelPairSeqProb`), so its complement
  `→ 0`.
* **The packing term** `(M(n) − 1) · exp(-n (H(X:Y) − 3ε)) → 0`
  (`Real.tendsto_channelPackingTerm`): choosing `ε` with `H(X:Y) − 3ε > R · log 2` makes the
  exponent `R · log 2 − (H(X:Y) − 3ε) =: −γ` negative, and `M(n) − 1 ≤ exp(n · R · log 2)`, so the
  term is squeezed by `exp(-n γ) = (exp(-γ))ⁿ → 0`.

Combining the two by a squeeze (both `≥ 0`, sum `≤` the vanishing bound) gives the main result. The
tolerance `ε = (H(X:Y) − R · log 2) / 6` is small enough that `H(X:Y) − 3ε = (H(X:Y) + R·log 2)/2`
strictly exceeds `R · log 2`. Extracting an actual good deterministic code from this
expected-error-`→ 0` statement (the probabilistic method + expurgation) is not done here.

## Main declarations

* `Real.tendsto_channelPackingTerm` — the packing term `(⌈exp(n R log 2)⌉₊ − 1)·exp(-n(I − 3ε)) → 0`
  whenever `R · log 2 < I − 3ε`.
* `Real.tendsto_one_sub_sum_channelTypicalPairs` — the joint-AEP complement
  `1 − ∑_{typ} channelPairSeqProb q p → 0`.
* `Real.tendsto_expectedError_channelRandomCode` — the codebook-averaged decoding error of the
  joint-typicality random code tends to `0` for any rate `R` with
  `R · log 2 < channelMutualInfo q p`.
-/

@[expose] public section

open Finset Filter Topology

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Decay of the two contributions to the codebook-averaged error -/

/-- **The packing term vanishes.** For reals `R, I, ε` with `R · log 2 < I − 3ε`, the packing
contribution of the random-coding error bound, `(⌈exp(n · R · log 2)⌉₊ − 1) · exp(-n (I − 3ε))`,
tends to `0` as `n → ∞`. The message count `⌈exp(n R log 2)⌉₊ − 1 ≤ exp(n R log 2)` cancels all but
`exp(-n γ)` of the decay exponent `γ = (I − 3ε) − R · log 2 > 0`, and `exp(-n γ) = (exp(-γ))ⁿ → 0`
since `0 ≤ exp(-γ) < 1`. -/
theorem tendsto_channelPackingTerm {R I ε : ℝ} (hlt : R * Real.log 2 < I - 3 * ε) :
    Tendsto (fun n : ℕ => ((⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) - 1) *
        Real.exp (-(n : ℝ) * (I - 3 * ε))) atTop (𝓝 0) := by
  set γ := (I - 3 * ε) - R * Real.log 2 with hγ
  have hγpos : 0 < γ := by rw [hγ]; linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
      (h := fun n : ℕ => (Real.exp (-γ)) ^ n) tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith))
  · -- the term is nonnegative
    intro n
    have h1 : (1 : ℝ) ≤ (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos _)
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · -- the term is at most `(exp(-γ))ⁿ`
    intro n
    have hMle : (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) - 1
        ≤ Real.exp ((n : ℝ) * R * Real.log 2) := by
      have h := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R * Real.log 2)).le
      linarith
    calc ((⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) - 1) * Real.exp (-(n : ℝ) * (I - 3 * ε))
        ≤ Real.exp ((n : ℝ) * R * Real.log 2) * Real.exp (-(n : ℝ) * (I - 3 * ε)) :=
          mul_le_mul_of_nonneg_right hMle (Real.exp_pos _).le
      _ = Real.exp (-(n : ℝ) * γ) := by rw [← Real.exp_add]; congr 1; rw [hγ]; ring
      _ = (Real.exp (-γ)) ^ n := by rw [← Real.exp_natCast_mul]; congr 1; ring

/-- **The true-atypical term vanishes** (the joint asymptotic equipartition property). For `ε > 0`,
the complement of the jointly typical mass,
`1 − ∑_{(x,y) ∈ channelTypicalPairs} channelPairSeqProb`, tends to `0` as `n → ∞`. The joint AEP
(`exists_le_sum_channelTypicalPairs`) makes the typical mass exceed `1 − δ` eventually, and it never
exceeds the total mass `1` (`sum_channelPairSeqProb`), so its complement lies in `[0, δ]`
eventually. -/
theorem tendsto_one_sub_sum_channelTypicalPairs {q : ι → κ → ℝ} (hN : IsChannel q)
    {p : ι → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => 1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, _, hNle⟩ := exists_le_sum_channelTypicalPairs hN hp0 hp1 hε (half_pos hη)
  refine ⟨N, fun n hn => ?_⟩
  have hmass_le : ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun xy _ _ => channelPairSeqProb_nonneg hN hp0 xy).trans_eq (sum_channelPairSeqProb hN hp1)
  have hge := hNle n hn
  have hnn : (0 : ℝ) ≤ 1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy := by
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-! ### The random-coding limit -/

/-- **The random-coding limit** (achievability half of Nielsen & Chuang, Theorem 12.7). For a
channel `q`, an input distribution `p`, and a rate `R` (in bits) with
`R · log 2 < channelMutualInfo q p = H(X : Y)`, there is a tolerance `ε > 0` such that — for the
message count `M(n) = ⌈exp(n · R · log 2)⌉₊ = ⌈2^{nR}⌉` of `IsAchievableRate` and *any* fallback
message family `m₀` — the expectation over the i.i.d. random codebook of the average decoding error
of the joint-typicality code tends to `0` as `n → ∞`:

`∑_C channelCodebookProb p C · (M(n)⁻¹ ∑ₘ condErrorProb (channelJointTypicalCode … (m₀ n) C) m)
→ 0`.

Choosing `ε = (channelMutualInfo q p − R · log 2) / 6` makes `channelMutualInfo q p − 3ε` strictly
exceed `R · log 2`, so the per-`n` bound `channelRandomCode_expectedAvgError_le` is squeezed between
`0` and `(1 − typical mass) + (M(n) − 1) · exp(-n (H(X:Y) − 3ε))`, whose true-atypical term vanishes
by the joint AEP (`tendsto_one_sub_sum_channelTypicalPairs`) and whose packing term vanishes by
`tendsto_channelPackingTerm`. Since the expected error is `0` for a rate below the mutual
information, a good deterministic code exists — the substance of the achievability argument. -/
theorem tendsto_expectedError_channelRandomCode {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {R : ℝ}
    (hR : R * Real.log 2 < channelMutualInfo q p) :
    ∃ ε > 0, ∀ m₀ : ∀ n : ℕ, Fin ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊,
      Tendsto (fun n : ℕ =>
        ∑ C : Fin ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ → (Fin n → ι),
          channelCodebookProb p C *
            ((⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ)⁻¹ *
              ∑ m, (channelJointTypicalCode q p n ε (m₀ n) C).condErrorProb q m))
        atTop (𝓝 0) := by
  have hIpos : 0 < channelMutualInfo q p - R * Real.log 2 := sub_pos.mpr hR
  set ε := (channelMutualInfo q p - R * Real.log 2) / 6 with hεdef
  have hεpos : 0 < ε := div_pos hIpos (by norm_num)
  have hlt : R * Real.log 2 < channelMutualInfo q p - 3 * ε := by rw [hεdef]; linarith
  refine ⟨ε, hεpos, fun m₀ => ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
      (h := fun n : ℕ =>
        (1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy)
          + ((⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) - 1) *
              Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)))
      tendsto_const_nhds ?_ ?_ ?_
  · -- the squeezing bound tends to `0`
    simpa only [add_zero] using
      (tendsto_one_sub_sum_channelTypicalPairs hN hp0 hp1 hεpos).add
        (tendsto_channelPackingTerm hlt)
  · -- the expected error is nonnegative
    intro n
    refine Finset.sum_nonneg fun C _ => mul_nonneg (channelCodebookProb_nonneg hp0 C) ?_
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => ?_)
    exact (channelJointTypicalCode q p n ε (m₀ n) C).condErrorProb_nonneg hN m
  · -- the expected error is bounded by the squeezing bound (the per-`n` random-coding estimate)
    exact fun n => channelRandomCode_expectedAvgError_le hN hp0 hp1 (m₀ n)

end Real
