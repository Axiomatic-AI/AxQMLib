/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ProductStateCapacity
import AxQM.Core.ProductStateCodeExpurgation
import AxQM.Core.ProductStateCodePrettyGood
import AxQM.Core.ChannelHolevoChi
import ToMathlib.Analysis.SpecificLimits.ExpNatMul

/-!
# From average-error codes to an achievable rate (N&C Theorem 12.8, achievability, eq. (12.83))

The random-coding half of the Holevo–Schumacher–Westmoreland theorem (Nielsen & Chuang,
Theorem 12.8) produces, for every rate `R < χ(E)`, a family of product-state codes whose **average**
error probability `p_av` tends to `0` (the culmination of the error estimate of Box 12.5,
eqs. (12.72)–(12.82)).  Operational achievability, however, is stated with the **maximum** error
probability (`IsProductStateAchievableRate`, `AxQM/Core/ProductStateCapacity.lean`): Bob must decode
*every* message reliably.  N&C's closing paragraph after eq. (12.83) bridges the two by
**expurgation** — discard the worse half of the codewords — at an asymptotically negligible rate
cost.

This file formalises both that bridge and the random-coding bound feeding it, as code-level
statements:

* `AxQM.IsProductStateAvgAchievableRate E R` — the **average-error analogue** of
  `IsProductStateAchievableRate`: a family of product-state codes
  `codeₙ : ProductStateCode E n ⌈exp (n·R)⌉₊` whose *average* error `avgError` tends to `0`.

* `AxQM.isProductStateAvgAchievableRate_of_lt_channelHolevoChi` — the **random-coding
  bound** (Box 12.5, eqs. (12.72)–(12.83)): every rate `R < χ(E)` is average-achievable.  From
  `χ(E) = sSup` of the output-ensemble χ's it picks a near-optimal input ensemble with output χ
  `> R`, feeds the derandomized per-block bound
  `ProductStateCode.exists_const_avgError_prettyGood_le`
  a rate-`R` message count `K = ⌈eⁿᴿ⌉₊`, and squeezes the resulting
  `p̄ ≤ C/n + (K−1)·exp(−n(χ₀−2ε))` to `0` (the confusion exponent stays negative because
  `K−1 < eⁿᴿ`).  See its docstring for the three steps.

* `AxQM.IsProductStateAvgAchievableRate.isProductStateAchievableRate_of_lt` — the
  **bridge**: if `R` is average-achievable then every strictly smaller rate `R' < R` is achievable
  (`IsProductStateAchievableRate E R'`).

  The strict inequality is intrinsic to the expurgation, exactly as in N&C: expurgation halves the
  codebook, losing a factor of two in the message count (an asymptotically vanishing rate cost that
  a strictly smaller target rate absorbs).  Concretely, for each block length `n`:

  1. **Expurgate** the average-error code `codeₙ` (`ProductStateCode.exists_expurgated`,
     N&C eq. (12.83)): a subcode `c'ₙ` on `K'ₙ` messages with `⌈eⁿᴿ⌉ ≤ 2·K'ₙ` (at least half the
     messages survive) and `maxError c'ₙ ≤ 2·avgError codeₙ`.
  2. **Count**: since `K'ₙ ≥ ⌈eⁿᴿ⌉/2 ≥ eⁿᴿ/2` and `⌈eⁿᴿ'⌉ ≤ eⁿᴿ' + 1`, for large `n` the target
     message count `⌈eⁿᴿ'⌉` is `≤ K'ₙ` (because `eⁿᴿ'/eⁿᴿ = e⁻ⁿ⁽ᴿ⁻ᴿ'⁾ → 0` when `R > 0`; when
     `R ≤ 0` both counts collapse to `1`).
  3. **Truncate** `c'ₙ` to its first `⌈eⁿᴿ'⌉` messages (`ProductStateCode.truncate`,
     `truncate_maxError_le`): a genuine rate-`R'` code whose maximum error is
     `≤ maxError c'ₙ ≤ 2·avgError codeₙ → 0`.  (For the finitely many small `n` where the count
     bound fails, any code — a one-outcome junk decoder — serves; the limit is unaffected.)

  A squeeze on `0 ≤ maxErrorₙ ≤ 2·avgError codeₙ → 0` gives `maxError → 0`, i.e. `R'` achievable.

It builds on `AxQM/Core/ProductStateCapacity.lean` and `AxQM/Core/ProductStateCodeExpurgation.lean`.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A **junk product-state code**: encode every message to an arbitrary input state and always
announce the inconclusive outcome `none`.  It conveys no information; it only fills the
finitely-many block lengths a code family leaves otherwise unconstrained — `n = 0`, or the small `n`
where a count bound fails — which do not affect the `n → ∞` error limit.  `[Nonempty (State S)]`
supplies the (irrelevant) input state the encoder must name.  The decoder is
`certainMeasurement none`. -/
def ProductStateCode.junk [Nonempty (State S)] (E : State S → State S) (n K : ℕ) :
    ProductStateCode E n K where
  encoder := fun _ _ => Classical.arbitrary (State S)
  decoder := certainMeasurement none

/-- A rate `R` (in **nats** per channel use) is **average-achievable** for the memoryless channel
`E` when there is a family of product-state codes `codeₙ : ProductStateCode E n ⌈exp (n·R)⌉₊`, one
per block length `n`, whose *average* error probability `avgError` tends to `0` as `n → ∞`.  This is
the average-error analogue of `IsProductStateAchievableRate` (which uses `maxError`) and the natural
output of the random-coding error estimate (Nielsen & Chuang, Theorem 12.8, eqs. (12.72)–(12.82)):
the expected average error over random codebooks tends to `0`, so some codebook achieves it. -/
def IsProductStateAvgAchievableRate (E : State S → State S) (R : ℝ) : Prop :=
  ∃ code : (n : ℕ) → ProductStateCode E n ⌈Real.exp ((n : ℝ) * R)⌉₊,
    Tendsto (fun n => (code n).avgError) atTop (𝓝 0)

/-- **The average-error → achievability bridge** (Nielsen & Chuang, Theorem 12.8, the expurgation
paragraph after eq. (12.83)).  If a rate `R` is average-achievable for `E`, then every strictly
smaller rate `R' < R` is achievable (`IsProductStateAchievableRate E R'`).

Expurgation (`ProductStateCode.exists_expurgated`) turns each average-error code into a subcode with
at least half the messages and maximum error at most twice the average; the surviving message count
`K'ₙ ≥ ⌈eⁿᴿ⌉/2` still exceeds the target `⌈eⁿᴿ'⌉` for large `n` (as `R' < R`), so truncating
(`ProductStateCode.truncate`) yields a genuine rate-`R'` code with `maxError → 0`.  See the module
docstring for the full argument.  `[Nonempty (State S)]` supplies the (irrelevant) input state the
junk codes for small `n` must name. -/
theorem IsProductStateAvgAchievableRate.isProductStateAchievableRate_of_lt [Nonempty (State S)]
    {E : State S → State S} {R R' : ℝ} (hRR : R' < R) (h : IsProductStateAvgAchievableRate E R) :
    IsProductStateAchievableRate E R' := by
  classical
  obtain ⟨code, hcode⟩ := h
  -- Expurgate each block: a subcode `c' n` with `⌈eⁿᴿ⌉ ≤ 2·K' n` and `maxError ≤ 2·avgError`.
  have hexp : ∀ n : ℕ, ∃ (K' : ℕ) (c' : ProductStateCode E n K'),
      ⌈Real.exp ((n : ℝ) * R)⌉₊ ≤ 2 * K' ∧ c'.maxError ≤ 2 * (code n).avgError := by
    intro n
    have : NeZero ⌈Real.exp ((n : ℝ) * R)⌉₊ := ⟨(Nat.ceil_pos.mpr (Real.exp_pos _)).ne'⟩
    exact (code n).exists_expurgated
  choose K' c' hK' hmax using hexp
  -- Each block keeps at least one message.
  have hKpos : ∀ n : ℕ, 1 ≤ K' n := by
    intro n
    have h1 : 1 ≤ ⌈Real.exp ((n : ℝ) * R)⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
    have h2 := hK' n
    omega
  -- The target message count `⌈eⁿᴿ'⌉` fits inside the surviving `K' n` for large `n`.
  have hcount : ∀ᶠ n : ℕ in atTop, ⌈Real.exp ((n : ℝ) * R')⌉₊ ≤ K' n := by
    rcases le_or_gt R 0 with hR0 | hRpos
    · -- `R ≤ 0`: then `R' < R ≤ 0`, so `eⁿᴿ' ≤ 1 ≤ K' n` for every `n`.
      refine Eventually.of_forall fun n => ?_
      have hle1 : ⌈Real.exp ((n : ℝ) * R')⌉₊ ≤ 1 := by
        rw [Nat.ceil_le, Nat.cast_one]
        exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      exact le_trans hle1 (hKpos n)
    · -- `R > 0`: exponential growth makes `eⁿᴿ'/eⁿᴿ → 0`, so eventually `eⁿᴿ' + 1 ≤ eⁿᴿ/2 ≤ K' n`.
      have hftend : Tendsto (fun n : ℕ =>
          Real.exp ((n : ℝ) * (R' - R)) + Real.exp ((n : ℝ) * (-R))) atTop (𝓝 0) := by
        have e1 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (R' - R))) atTop (𝓝 0) :=
          Real.tendsto_exp_nat_mul_atTop_nhds_zero (by linarith)
        have e2 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (-R))) atTop (𝓝 0) :=
          Real.tendsto_exp_nat_mul_atTop_nhds_zero (by linarith)
        simpa using e1.add e2
      have hev : ∀ᶠ n : ℕ in atTop,
          Real.exp ((n : ℝ) * (R' - R)) + Real.exp ((n : ℝ) * (-R)) < 1 / 2 :=
        hftend.eventually (eventually_lt_nhds (by norm_num))
      filter_upwards [hev] with n hn
      -- `eⁿᴿ' + 1 = (e^{n(R'-R)} + e^{-nR})·eⁿᴿ < (1/2)·eⁿᴿ`.
      have hexpR : (0 : ℝ) < Real.exp ((n : ℝ) * R) := Real.exp_pos _
      have h1 : (n : ℝ) * (R' - R) + (n : ℝ) * R = (n : ℝ) * R' := by ring
      have h2 : (n : ℝ) * (-R) + (n : ℝ) * R = 0 := by ring
      have hid : Real.exp ((n : ℝ) * R') + 1 =
          (Real.exp ((n : ℝ) * (R' - R)) + Real.exp ((n : ℝ) * (-R))) * Real.exp ((n : ℝ) * R) := by
        rw [add_mul, ← Real.exp_add, ← Real.exp_add, h1, h2, Real.exp_zero]
      have hlt : Real.exp ((n : ℝ) * R') + 1 < Real.exp ((n : ℝ) * R) / 2 := by
        rw [hid]
        have hmul := mul_lt_mul_of_pos_right hn hexpR
        linarith [hmul]
      -- `eⁿᴿ/2 ≤ K' n`, from `⌈eⁿᴿ⌉ ≤ 2·K' n`.
      have hKR : Real.exp ((n : ℝ) * R) / 2 ≤ (K' n : ℝ) := by
        have hc : Real.exp ((n : ℝ) * R) ≤ (⌈Real.exp ((n : ℝ) * R)⌉₊ : ℝ) := Nat.le_ceil _
        have hc2 : (⌈Real.exp ((n : ℝ) * R)⌉₊ : ℝ) ≤ 2 * (K' n : ℝ) := by
          exact_mod_cast hK' n
        linarith
      -- `⌈eⁿᴿ'⌉ < eⁿᴿ' + 1 ≤ eⁿᴿ/2 ≤ K' n`.
      have hceil : (⌈Real.exp ((n : ℝ) * R')⌉₊ : ℝ) < Real.exp ((n : ℝ) * R') + 1 :=
        Nat.ceil_lt_add_one (Real.exp_pos _).le
      have : (⌈Real.exp ((n : ℝ) * R')⌉₊ : ℝ) < (K' n : ℝ) := by linarith
      exact_mod_cast this.le
  -- The junk code for the finitely many small `n` where the count bound fails (any code has
  -- `maxError ≤ 1`, so it does not affect the limit).
  set junk : (n : ℕ) → ProductStateCode E n ⌈Real.exp ((n : ℝ) * R')⌉₊ :=
    fun n => ProductStateCode.junk E n ⌈Real.exp ((n : ℝ) * R')⌉₊ with hjunk
  -- Build the rate-`R'` family: truncate where possible, junk otherwise.
  refine ⟨fun n =>
      if hn : ⌈Real.exp ((n : ℝ) * R')⌉₊ ≤ K' n then (c' n).truncate hn else junk n, ?_⟩
  -- `maxError → 0` by squeezing `0 ≤ maxErrorₙ ≤ 2·avgError codeₙ`.
  have hR0 : Tendsto (fun n => 2 * (code n).avgError) atTop (𝓝 0) := by
    simpa using hcode.const_mul (2 : ℝ)
  have hub : ∀ᶠ n : ℕ in atTop,
      (if hn : ⌈Real.exp ((n : ℝ) * R')⌉₊ ≤ K' n then (c' n).truncate hn
        else junk n).maxError ≤ 2 * (code n).avgError := by
    filter_upwards [hcount] with n hn
    rw [dite_eq_left hn]
    exact le_trans ((c' n).truncate_maxError_le hn) (hmax n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR0
    (Eventually.of_forall fun n => ProductStateCode.maxError_nonneg _) hub

/-- **Every rate below `χ(E)` is average-achievable** — the analytic core of the random-coding
half of the Holevo–Schumacher–Westmoreland theorem (Nielsen & Chuang, Theorem 12.8, Box 12.5,
eqs. (12.72)–(12.83)).  For any rate `R < χ(E)` (the channel Holevo χ quantity `channelHolevoChi E`)
there is a family of product-state codes `codeₙ : ProductStateCode E n ⌈eⁿᴿ⌉₊` whose *average* error
probability tends to `0`: `IsProductStateAvgAchievableRate E R`.

This turns the whole Box 12.5 error estimate into the achievability input the operational assembly
consumes.  The three steps of the argument:

1. **Near-optimal input ensemble.** `χ(E) = sSup` of the output-ensemble χ's (`channelHolevoChi`,
   `channelHolevoChiSet`), so `R < χ(E)` gives (`exists_lt_of_lt_csSup`, using
   `channelHolevoChiSet_nonempty`) an input ensemble `{pₐ, ρₐ}` whose output χ
   `χ₀ = χ({pₐ, E(ρₐ)})` strictly exceeds `R`.  Take the margin `ε = (χ₀ − R)/4 > 0`, so the
   surviving exponent `β = (χ₀ − 2ε) − R = (χ₀ − R)/2 > 0`.

2. **Derandomized per-block bound.** `ProductStateCode.exists_const_avgError_prettyGood_le` (the
   preceding development, eqs. (12.79)–(12.83)) supplies a constant `C ≥ 0` such that for every
   block length `n ≥ 1` and message count `K ≥ 1` there is a code `cₙ` with
   `p̄(cₙ) ≤ C/n + (K − 1)·exp(−n(χ₀ − 2ε))`.  Take `K = Kₙ = ⌈eⁿᴿ⌉₊` (a rate-`R` code family);
   for the finitely-many-irrelevant `n = 0` a junk one-message code fills the family.

3. **The bound vanishes.** `Kₙ − 1 < eⁿᴿ` (`Nat.ceil_lt_add_one`), so the confusion term
   `(Kₙ − 1)·exp(−n(χ₀ − 2ε)) ≤ eⁿᴿ·exp(−n(χ₀ − 2ε)) = exp(−nβ)` with `β > 0`.  Hence
   `p̄(cₙ) ≤ C/n + exp(−nβ) → 0`, and a squeeze gives `p̄ → 0`.

Composed with the average → maximum error bridge
(`IsProductStateAvgAchievableRate.isProductStateAchievableRate_of_lt`) this yields the achievability
direction `χ(E) ≤ C⁽¹⁾(E)` of the HSW theorem; the final `le_antisymm`
with the converse `productStateCapacity_le_channelHolevoChi` is in
`AxQM/NC/Ch12/Theorem12_8.lean`.  The channel `E` is an arbitrary state-map. -/
theorem isProductStateAvgAchievableRate_of_lt_channelHolevoChi [Nonempty (State S)]
    {E : State S → State S} {R : ℝ} (hR : R < channelHolevoChi E) :
    IsProductStateAvgAchievableRate E R := by
  classical
  -- Step 1: a near-optimal input ensemble `{p, ρ}` with output χ strictly above `R`.
  obtain ⟨χv, hmem, hRχ⟩ := exists_lt_of_lt_csSup (channelHolevoChiSet_nonempty E) hR
  obtain ⟨N, p, hp, hsum, ρ, rfl⟩ := hmem
  -- `hRχ : R < χ₀`, `χ₀ = χ({pₐ, E(ρₐ)})`.
  have hεpos : (0 : ℝ) < (State.holevoChi p hp hsum (fun a => E (ρ a)) - R) / 4 := by
    linarith
  -- Step 2: the derandomized per-block bound at margin `ε = (χ₀ − R)/4`.
  obtain ⟨C, -, hbound⟩ := ProductStateCode.exists_const_avgError_prettyGood_le
    p hp hsum E ρ (∑ a, p a * (E (ρ a)).vonNeumannEntropy)
    ((State.holevoChi p hp hsum (fun a => E (ρ a)) - R) / 4) hεpos rfl
  set χ₀ := State.holevoChi p hp hsum (fun a => E (ρ a)) with hχ₀
  set ε := (χ₀ - R) / 4 with hεdef
  set β := χ₀ - 2 * ε - R with hβ
  have hβpos : 0 < β := by rw [hβ, hεdef]; linarith
  -- A code for each block length `n ≥ 1` meeting the bound with `K = Kₙ = ⌈eⁿᴿ⌉₊`.
  have hcode : ∀ n : ℕ, 0 < n → ∃ c : ProductStateCode E n ⌈Real.exp ((n : ℝ) * R)⌉₊,
      c.avgError ≤ C / (n : ℝ)
        + ((⌈Real.exp ((n : ℝ) * R)⌉₊ : ℝ) - 1) * Real.exp (-(n : ℝ) * (χ₀ - 2 * ε)) :=
    fun n hn => hbound n hn ⌈Real.exp ((n : ℝ) * R)⌉₊ (Nat.ceil_pos.mpr (Real.exp_pos _))
  choose code hcodebound using hcode
  -- A junk one-message code for the (limit-irrelevant) `n = 0`.
  set junk : (n : ℕ) → ProductStateCode E n ⌈Real.exp ((n : ℝ) * R)⌉₊ :=
    fun n => ProductStateCode.junk E n ⌈Real.exp ((n : ℝ) * R)⌉₊ with hjunk
  refine ⟨fun n => if hn : 0 < n then code n hn else junk n, ?_⟩
  -- Step 3: `avgError → 0` by squeezing against `C/n + exp(−nβ) → 0`.
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ) + Real.exp (-(n : ℝ) * β)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have h2 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * β)) atTop (𝓝 0) := by
      simpa only [neg_mul, mul_neg] using
        Real.tendsto_exp_nat_mul_atTop_nhds_zero (show -β < 0 by linarith)
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => ProductStateCode.avgError_nonneg _) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [dite_eq_left hn]
  refine (hcodebound n hn).trans ?_
  -- The confusion term collapses: `(Kₙ − 1)·exp(−n(χ₀ − 2ε)) ≤ eⁿᴿ·exp(−n(χ₀ − 2ε)) = exp(−nβ)`.
  have hexpeq : Real.exp ((n : ℝ) * R) * Real.exp (-(n : ℝ) * (χ₀ - 2 * ε))
      = Real.exp (-(n : ℝ) * β) := by
    rw [← Real.exp_add]; congr 1; rw [hβ]; ring
  gcongr
  rw [← hexpeq]
  gcongr
  have h := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R)).le
  linarith

end AxQM
