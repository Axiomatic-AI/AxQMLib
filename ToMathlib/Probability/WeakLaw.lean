/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The weak law of large numbers

We prove the **`L²` weak law of large numbers** for real-valued random variables, in
`ProbabilityTheory.tendstoInMeasure_sum_range_div`: if `X : ℕ → Ω → ℝ` is a sequence of pairwise
independent, identically distributed random variables with finite second moment
(`MemLp (X 0) 2 μ`), then the sample averages `(∑ i ∈ range n, X i) / n` converge *in measure*
(equivalently, *in probability*) to the common mean `𝔼[X 0]`.

The proof is the classical Chebyshev argument (this is Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Theorem 12.3, Box 12.3): the variance of the sample average is
`Var[X 0] / n`, so by Chebyshev's inequality the probability of an `ε`-deviation is at most
`Var[X 0] / (n ε²)`, which tends to `0`.

This complements `ProbabilityTheory.strong_law_ae`, the strong law (almost-sure convergence, which
requires only integrability), and `Real.iid_average_deviation_le`
(`ToMathlib/InformationTheory/IIDConcentration.lean`), the elementary finite-alphabet specialization
used for the asymptotic equipartition property.

## Main results

* `ProbabilityTheory.variance_sum_range_div`: the variance of the sample average
  `(∑ i ∈ range n, X i) / n` is `Var[X 0] / n` (N&C Eq. 12.34).
* `ProbabilityTheory.integral_sum_range_div`: the mean of the sample average
  `(∑ i ∈ range n, X i) / n` is `𝔼[X 0]` (the centering identity).
* `ProbabilityTheory.meas_abs_sum_range_div_sub_ge_le`: the quantitative Chebyshev bound
  `ℙ {ω | ε ≤ |Sₙ ω - 𝔼[X 0]|} ≤ Var[X 0] / (n ε²)` (N&C Eq. 12.38).
* `ProbabilityTheory.tendstoInMeasure_sum_range_div`: the weak law of large numbers, stated as
  convergence in measure of the sample averages to `𝔼[X 0]`.
* `ProbabilityTheory.tendsto_meas_abs_sum_range_div_sub_gt`: the same result in the literal form of
  N&C Theorem 12.3, `p(|Sₙ - 𝔼[X 0]| > ε) → 0` for every `ε > 0`.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Variance of the sample average** (Nielsen & Chuang, Eq. 12.34). For pairwise independent,
identically distributed, square-integrable real random variables `X`, the variance of the sample
average `(∑ i ∈ range n, X i) / n` is `Var[X 0] / n`. (For `n = 0` both sides are `0`.) -/
theorem variance_sum_range_div (hℒp : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    variance (fun ω => (∑ i ∈ range n, X i ω) / n) μ = variance (X 0) μ / n := by
  have hmem : ∀ i, MemLp (X i) 2 μ := fun i => (hident i).memLp_iff.mpr hℒp
  have hfunsum : (fun ω => ∑ i ∈ range n, X i ω) = ∑ i ∈ range n, X i := by
    funext ω; rw [Finset.sum_apply]
  have hsum : variance (fun ω => ∑ i ∈ range n, X i ω) μ = (n : ℝ) * variance (X 0) μ := by
    rw [hfunsum, IndepFun.variance_sum (fun i _ => hmem i) (hindep.set_pairwise _),
      Finset.sum_congr rfl (fun i _ => (hident i).variance_eq), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hcast : (fun ω => (∑ i ∈ range n, X i ω) / (n : ℝ))
      = fun ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω := by funext ω; rw [div_eq_inv_mul]
  rw [hcast, variance_const_mul, hsum]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp

/-- **Mean of the sample average.** For identically distributed, integrable real random variables
`X`, the mean of the sample average `(∑ i ∈ range n, X i) / n` is the common mean `𝔼[X 0]` (for
`n > 0`). This needs only the first moment (`Integrable (X 0)`), not the second. -/
theorem integral_sum_range_div (hint : Integrable (X 0) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {n : ℕ} (hn : 0 < n) :
    ∫ ω, (∑ i ∈ range n, X i ω) / (n : ℝ) ∂μ = ∫ x, X 0 x ∂μ := by
  have hint' : ∀ i, Integrable (X i) μ := fun i => (hident i).integrable_iff.mpr hint
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [integral_div, integral_finsetSum (range n) (fun i _ => hint' i),
    Finset.sum_congr rfl (fun i _ => (hident i).integral_eq), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hn0]

/-- **Chebyshev bound for the sample average** (Nielsen & Chuang, Eq. 12.38). For pairwise
independent, identically distributed, square-integrable real random variables `X`, the probability
that the sample average `Sₙ = (∑ i ∈ range n, X i) / n` deviates from the common mean `𝔼[X 0]` by at
least `ε` is at most `Var[X 0] / (n ε²)`. -/
theorem meas_abs_sum_range_div_sub_ge_le [IsFiniteMeasure μ] (hℒp : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - ∫ x, X 0 x ∂μ|}
      ≤ ENNReal.ofReal (variance (X 0) μ / (n * ε ^ 2)) := by
  have hmem : ∀ i, MemLp (X i) 2 μ := fun i => (hident i).memLp_iff.mpr hℒp
  have hmemavg : MemLp (fun ω => (∑ i ∈ range n, X i ω) / (n : ℝ)) 2 μ := by
    have hsum := memLp_finsetSum (range n) (fun i _ => hmem i)
    simpa [div_eq_inv_mul] using hsum.const_mul (n : ℝ)⁻¹
  have hmean := integral_sum_range_div (hℒp.integrable one_le_two) hident hn
  have hcheb := meas_ge_le_variance_div_sq hmemavg hε
  rw [hmean, variance_sum_range_div hℒp hindep hident n, div_div] at hcheb
  exact hcheb

/-- **Weak law of large numbers** (Nielsen & Chuang, Theorem 12.3). For pairwise independent,
identically distributed, square-integrable real random variables `X`, the sample averages
`(∑ i ∈ range n, X i) / n` converge in measure (equivalently, in probability) to the common mean
`𝔼[X 0]`. -/
theorem tendstoInMeasure_sum_range_div [IsProbabilityMeasure μ] (hℒp : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ (fun n ω => (∑ i ∈ range n, X i ω) / n) atTop (fun _ => ∫ x, X 0 x ∂μ) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hbound : Tendsto (fun n : ℕ => ENNReal.ofReal (variance (X 0) μ / ((n : ℝ) * ε ^ 2)))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => variance (X 0) μ / ((n : ℝ) * ε ^ 2)) atTop (nhds 0) := by
      have heq : (fun n : ℕ => variance (X 0) μ / ((n : ℝ) * ε ^ 2))
          = fun n : ℕ => variance (X 0) μ / ε ^ 2 / (n : ℝ) := by
        funext n; rw [div_div, mul_comm (n : ℝ)]
      rw [heq]; exact tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [Real.norm_eq_abs] using
    meas_abs_sum_range_div_sub_ge_le hℒp hindep hident hn hε

/-- **Weak law of large numbers, literal N&C form** (Nielsen & Chuang, Theorem 12.3). For pairwise
independent, identically distributed, square-integrable real random variables `X`, for every
`ε > 0` the probability that the sample average `Sₙ = (∑ i ∈ range n, X i) / n` deviates from the
common mean `𝔼[X 0]` by more than `ε` tends to `0`, i.e. `p(|Sₙ - 𝔼[X 0]| > ε) → 0`. -/
theorem tendsto_meas_abs_sum_range_div_sub_gt [IsProbabilityMeasure μ] (hℒp : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε < |(∑ i ∈ range n, X i ω) / n - ∫ x, X 0 x ∂μ|}) atTop (nhds 0) := by
  have h := (tendstoInMeasure_iff_norm.mp
    (tendstoInMeasure_sum_range_div hℒp hindep hident)) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
  exact hω.le

end ProbabilityTheory
