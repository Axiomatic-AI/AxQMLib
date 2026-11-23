/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.TwoValued
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Concrete: standard deviation of the classical sampling counting estimator (N&C Exercise 6.13)

Nielsen & Chuang, Exercise 6.13 (p. 261) studies the *classical* algorithm for the counting
problem: to estimate the number `M` of solutions among `N` items, sample `k` items uniformly and
independently, let `Xⱼ = 1` if the `j`-th sample is a solution and `Xⱼ = 0` otherwise, and return

  `S ≡ N · (∑ⱼ Xⱼ) / k`.

For classical sampling counting estimator, show std dev sqrt(M(N-M)/k) and need k=Omega(N).

This file formalises the **first** claim (the standard deviation). The `k = Ω(N)` lower bound is a
separate development (`AxQM/Concrete/ClassicalCountingLowerBound.lean`).

## Model

Each sample is a solution independently with probability `p = M/N`, so the `Xⱼ` are i.i.d.
`Bernoulli(M/N)` indicators. We realise them concretely on the finite product space
`Ω = Fin k → Bool` with the product Bernoulli measure `μ`:

* `samplingProb N M = min (M/N) 1` — the success probability `p` (the `min` keeps `p ≤ 1`
  unconditionally so the definitions need no hypothesis; `samplingProb_coe` gives `p = M/N` once
  `M ≤ N`).
* `sampleMeasure N M` — the `Bernoulli(p)` measure on `Bool`.
* `sampleSpaceMeasure N M k` — the product `μ` of `k` copies of it on `Fin k → Bool`.
* `sampleIndicator k i ω = (if ω i then 1 else 0)` — the indicator `Xᵢ`.
* `samplingEstimator N k = (N/k) • ∑ᵢ Xᵢ` — the estimator `S`.

## Results

* `variance_eq_mean_mul_one_sub_mean` — a general fact: for a `{0,1}`-valued random variable on a
  probability space, `Var X = E[X](1 − E[X])` (a thin wrapper over Mathlib's
  `ProbabilityTheory.variance_of_ae_eq_zero_or_one`).
* `boolIndicator_mean` (`E[Xᵢ] = M/N`), `boolIndicator_variance` (`Var Xᵢ = (M/N)(1 − M/N)`) — the
  per-sample facts on the single-coordinate Bernoulli factor.
* `samplingEstimator_variance` — **the variance of the estimator**: `Var S = M(N−M)/k` (obtained
  from `ProbabilityTheory.variance_sum_pi`, the variance of a sum over a product measure).
* `samplingEstimatorStddev` and `samplingEstimatorStddev_eq` — **Exercise 6.13 (standard
  deviation)**: `ΔS = √(M(N−M)/k)`.

The statement of Exercise 6.13 is in `AxQM/NC/Ch6/Exercise6_13.lean`. Compare the other
Chapter 6 mathematics exercises (6.1–6.3, 6.8).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal unitInterval

namespace AxQM.Concrete

/-- The variance of a `{0,1}`-valued random variable on a probability space is `E[X]·(1 − E[X])`
(the Bernoulli variance). A thin wrapper over `ProbabilityTheory.variance_of_ae_eq_zero_or_one`
(which gives the `μ.real {X=0} * μ.real {X=1}` form) rephrased via the expectation, using
`integral_of_ae_eq_zero_or_one` (`E[X] = μ.real {X=1}`) and `integral_one_sub_of_ae_eq_zero_or_one`
(`1 − E[X] = μ.real {X=0}`). -/
theorem variance_eq_mean_mul_one_sub_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hmeas : AEStronglyMeasurable X μ)
    (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    variance X μ = (∫ ω, X ω ∂μ) * (1 - ∫ ω, X ω ∂μ) := by
  have h1 : ∫ ω, X ω ∂μ = μ.real {ω | X ω = 1} :=
    integral_of_ae_eq_zero_or_one hmeas.aemeasurable h01
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [h01] with ω h; rcases h with h | h <;> simp [h]
  have hint : Integrable X μ := (memLp_of_bounded hIcc hmeas 1).integrable (by norm_num)
  have h0 : 1 - ∫ ω, X ω ∂μ = μ.real {ω | X ω = 0} := by
    rw [← integral_one_sub_of_ae_eq_zero_or_one hmeas.aemeasurable h01,
      integral_sub (integrable_const 1) hint]
    simp
  rw [variance_of_ae_eq_zero_or_one hmeas.aemeasurable h01, ← h0, ← h1]
  ring

/-- The Bernoulli success probability `p = M/N`, clamped to `[0,1]` so the definitions require no
hypothesis. Under `M ≤ N` the clamp is inactive (`samplingProb_coe`). -/
noncomputable def samplingProb (N M : ℕ) : ℝ≥0 := min ((M : ℝ≥0) / (N : ℝ≥0)) 1

/-- `samplingProb` is at most `1` (it is a probability). -/
lemma samplingProb_le_one (N M : ℕ) : samplingProb N M ≤ 1 := min_le_right _ _

/-- With at most `N` solutions, `samplingProb N M = M/N` as a real number. -/
lemma samplingProb_coe {N M : ℕ} (hM : M ≤ N) :
    ((samplingProb N M : ℝ≥0) : ℝ) = (M : ℝ) / N := by
  have hp_le : (M : ℝ≥0) / (N : ℝ≥0) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with hN0 | hN0
    · simp [hN0]
    · rw [div_le_one (by exact_mod_cast hN0)]; exact_mod_cast hM
  unfold samplingProb
  rw [min_eq_left hp_le, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]

/-- The single-sample `Bernoulli(p)` measure on `Bool`, giving mass `p` to `true` and `1-p` to
`false`. -/
noncomputable def sampleMeasure (N M : ℕ) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false
    (⟨(samplingProb N M : ℝ), by positivity, by exact_mod_cast samplingProb_le_one N M⟩ : I)

instance (N M : ℕ) : IsProbabilityMeasure (sampleMeasure N M) := by
  unfold sampleMeasure; infer_instance

/-- The product measure of `k` i.i.d. `Bernoulli(M/N)` samples on `Fin k → Bool`. -/
noncomputable def sampleSpaceMeasure (N M k : ℕ) : Measure (Fin k → Bool) :=
  Measure.pi (fun _ : Fin k => sampleMeasure N M)

instance (N M k : ℕ) : IsProbabilityMeasure (sampleSpaceMeasure N M k) := by
  unfold sampleSpaceMeasure; infer_instance

/-- The indicator random variable `Xᵢ` : `1` if the `i`-th sample is a solution, else `0`. -/
def sampleIndicator (k : ℕ) (i : Fin k) : (Fin k → Bool) → ℝ := fun ω => bif ω i then 1 else 0

/-- The single-coordinate `{0,1}`-indicator `b ↦ (if b then 1 else 0)` is measurable. -/
lemma measurable_boolIndicator : Measurable (fun b : Bool => bif b then (1 : ℝ) else 0) :=
  measurable_of_countable _

/-- Each indicator `Xᵢ` takes only the values `0` and `1`. -/
lemma sampleIndicator_mem_zero_one (k : ℕ) (i : Fin k) (ω : Fin k → Bool) :
    sampleIndicator k i ω = 0 ∨ sampleIndicator k i ω = 1 := by
  unfold sampleIndicator; cases ω i <;> simp

/-- The estimator `S = (N/k) · ∑ᵢ Xᵢ` (N&C's `S ≡ N ∑ⱼ Xⱼ / k`). -/
noncomputable def samplingEstimator (N k : ℕ) : (Fin k → Bool) → ℝ :=
  ((N : ℝ) / (k : ℝ)) • ∑ i : Fin k, sampleIndicator k i

/-- Unfolding lemma: the estimator is the rescaled sum of the indicators. -/
lemma samplingEstimator_eq_smul (N k : ℕ) :
    samplingEstimator N k = ((N : ℝ) / (k : ℝ)) • ∑ i : Fin k, sampleIndicator k i := rfl

/-- Each single-coordinate indicator is (bounded, hence) square-integrable. -/
lemma boolIndicator_memLp (N M : ℕ) :
    MemLp (fun b : Bool => bif b then (1 : ℝ) else 0) 2 (sampleMeasure N M) :=
  memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ fun b => by cases b <;> simp)
    measurable_boolIndicator.aestronglyMeasurable 2

/-- The mean of the single-coordinate Bernoulli indicator is the success probability `M/N`. -/
lemma boolIndicator_mean {N M : ℕ} (hM : M ≤ N) :
    ∫ b, (bif b then (1 : ℝ) else 0) ∂(sampleMeasure N M) = (M : ℝ) / N := by
  unfold sampleMeasure
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  simp [samplingProb_coe hM]

/-- The variance of the single-coordinate Bernoulli indicator is `(M/N)(1 − M/N)`. -/
lemma boolIndicator_variance {N M : ℕ} (hM : M ≤ N) :
    variance (fun b : Bool => bif b then (1 : ℝ) else 0) (sampleMeasure N M)
      = ((M : ℝ) / N) * (1 - (M : ℝ) / N) := by
  rw [variance_eq_mean_mul_one_sub_mean measurable_boolIndicator.aestronglyMeasurable
      (ae_of_all _ fun b => by cases b <;> simp), boolIndicator_mean hM]

/-- **Exercise 6.13 (variance of the estimator).** For `M ≤ N`, `0 < N`, `0 < k`, the sampling
estimator has variance `M(N−M)/k`. -/
theorem samplingEstimator_variance {N M k : ℕ} (hM : M ≤ N) (hN : 0 < N) (hk : 0 < k) :
    variance (samplingEstimator N k) (sampleSpaceMeasure N M k)
      = (M : ℝ) * ((N : ℝ) - M) / k := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hsum : variance (∑ i : Fin k, sampleIndicator k i) (sampleSpaceMeasure N M k)
      = (k : ℝ) * (((M : ℝ) / N) * (1 - (M : ℝ) / N)) := by
    calc variance (∑ i : Fin k, sampleIndicator k i) (sampleSpaceMeasure N M k)
        = ∑ _i : Fin k, variance (fun b : Bool => bif b then (1 : ℝ) else 0)
            (sampleMeasure N M) :=
          variance_sum_pi (μ := fun _ : Fin k => sampleMeasure N M)
            (X := fun _ : Fin k => (fun b : Bool => bif b then (1 : ℝ) else 0))
            (fun _ => boolIndicator_memLp N M)
      _ = (k : ℝ) * (((M : ℝ) / N) * (1 - (M : ℝ) / N)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            boolIndicator_variance hM]
  rw [samplingEstimator_eq_smul, variance_smul, hsum, div_pow]
  field_simp

/-- The standard deviation `ΔS` of the sampling estimator. -/
noncomputable def samplingEstimatorStddev (N M k : ℕ) : ℝ :=
  Real.sqrt (variance (samplingEstimator N k) (sampleSpaceMeasure N M k))

/-- **Exercise 6.13 (standard deviation).** The standard deviation of the classical sampling
counting estimator is `ΔS = √(M(N−M)/k)`. -/
theorem samplingEstimatorStddev_eq {N M k : ℕ} (hM : M ≤ N) (hN : 0 < N) (hk : 0 < k) :
    samplingEstimatorStddev N M k = Real.sqrt ((M : ℝ) * ((N : ℝ) - M) / k) := by
  unfold samplingEstimatorStddev
  rw [samplingEstimator_variance hM hN hk]

end AxQM.Concrete
