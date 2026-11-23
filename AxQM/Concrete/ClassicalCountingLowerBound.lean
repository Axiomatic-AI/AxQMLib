/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalCountingEstimator
import Mathlib.MeasureTheory.Measure.Real

/-!
# Concrete: the classical counting estimator needs `k = Ω(N)` samples (N&C Exercise 6.13)

Nielsen & Chuang, Exercise 6.13 (p. 261) asks, for the classical sampling counting estimator
`S ≡ N · (∑ⱼ Xⱼ) / k` of `AxQM/Concrete/ClassicalCountingEstimator.lean`, to
Lower bound: estimating the solution count M to accuracy √M with probability ≥ 3/4 for all M
requires Ω(N) classical oracle calls.

This file formalises that **second** claim (the first, `ΔS = √(M(N−M)/k)`, is
`samplingEstimatorStddev_eq`).

## The argument: grid resolution at small `M`

The estimator can only take the `k + 1` *grid values* `(N/k)·m`, `m ∈ {0, …, k}` (`m` = the number
of sampled solutions). Its accuracy at a given `M` is therefore limited by how finely this grid,
of spacing `N/k`, resolves the point `M`. The requirement is *hardest at small `M`*, where the
allowed error `√M` is small: take `M* = ⌊N/(2k)⌋`. If `N ≥ 4k` then `M* ≥ 2`, and the grid
spacing satisfies `N/k ≥ 2·M*`, so **every**
grid point lies at distance `≥ M*` from `M*` (the grid point `0` at distance `M*`, and every
positive grid point `(N/k)·m ≥ N/k ≥ 2M*` at distance `≥ M*`). As `M* ≥ 2` gives `√M* < M*`, the
accuracy event `{ω | |S(ω) − M*| ≤ √M*}` is **empty**, hence has measure `0 < 3/4` — contradicting
the hypothesis at `M*`. Therefore `N < 4k`, i.e. `k > N/4 = Ω(N)`.

The bound uses only that the accuracy event has positive measure (which `≥ 3/4` supplies); it does
not use the measure's specific Bernoulli form. This makes it a clean *resolution* obstruction: no
sampling law whatsoever, however favourable, can beat the grid.

## Results

* `resolution_gap` — the arithmetic core: if `2·M ≤ N/k`, then every grid value `(N/k)·m`
  (`m : ℕ`) satisfies `M ≤ |(N/k)·m − M|`.
* `samplingEstimator_needs_linear_samples` — **Exercise 6.13 (`k = Ω(N)`)**: if for every
  `M ∈ [1, N−1]` the estimator is within `√M` of `M` with probability at least `3/4`, then
  `N < 4·k`.

The statement of Exercise 6.13 is in `AxQM/NC/Ch6/Exercise6_13.lean`.
-/

open MeasureTheory
open scoped BigOperators

namespace AxQM.Concrete

/-- The estimator evaluated at a sample outcome `ω` is `(N/k)` times the sum of the indicators. -/
lemma samplingEstimator_apply (N k : ℕ) (ω : Fin k → Bool) :
    samplingEstimator N k ω = (N : ℝ) / k * ∑ i : Fin k, sampleIndicator k i ω := by
  rw [samplingEstimator_eq_smul]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

/-- The sum of the indicators at `ω` is the (real cast of the) number of sampled solutions; in
particular it equals `↑m` for a natural number `m`. -/
lemma sampleIndicator_sum_eq_cast (k : ℕ) (ω : Fin k → Bool) :
    ∑ i : Fin k, sampleIndicator k i ω
      = ((∑ i : Fin k, if ω i = true then 1 else 0 : ℕ) : ℝ) := by
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [sampleIndicator]
  cases ω i <;> simp

/-- **Grid-resolution gap.** If the grid spacing dominates twice the target (`2·M ≤ N/k`), then
every grid value `(N/k)·m` (`m : ℕ`) is at distance at least `M` from `M`: the grid point `m = 0`
is at distance `M`, and every positive grid point overshoots to `≥ 2M`. -/
lemma resolution_gap {N k : ℕ} (M m : ℕ) (h2M : 2 * (M : ℝ) ≤ (N : ℝ) / k) :
    (M : ℝ) ≤ |(N : ℝ) / k * m - (M : ℝ)| := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp only [Nat.cast_zero, mul_zero, zero_sub, abs_neg]
    exact le_of_eq (abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ))).symm
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hNk : (0 : ℝ) ≤ (N : ℝ) / k := by positivity
    have h1 : (N : ℝ) / k ≤ (N : ℝ) / k * m := le_mul_of_one_le_right hNk hm1
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **Exercise 6.13 (`k = Ω(N)`).** If the classical sampling counting estimator estimates every
`M ∈ [1, N−1]` to within `√M` with probability at least `3/4`, then `N < 4·k` — i.e. the number of
samples must be `k > N/4 = Ω(N)`.

The `3/4` is used only through positivity of the accuracy event's probability: at
`M* = ⌊N/(2k)⌋`, the assumption `N ≥ 4k` makes the event empty (the grid cannot resolve `M*`), so
its probability is `0`, contradicting `3/4 ≤ 0`. -/
theorem samplingEstimator_needs_linear_samples {N k : ℕ} (hk : 0 < k)
    (hacc : ∀ M : ℕ, 1 ≤ M → M ≤ N - 1 →
      3 / 4 ≤ (sampleSpaceMeasure N M k).real
        {ω | |samplingEstimator N k ω - (M : ℝ)| ≤ Real.sqrt (M : ℝ)}) :
    N < 4 * k := by
  by_contra hcon
  rw [not_lt] at hcon
  -- `hcon : 4 * k ≤ N`.  The binding target is `M = ⌊N/(2k)⌋`.
  set M : ℕ := N / (2 * k) with hMdef
  have hM2 : 2 ≤ M := by
    rw [hMdef, Nat.le_div_iff_mul_le (by positivity)]; omega
  have hN0 : 0 < N := by omega
  have hMlt : M < N := by rw [hMdef]; exact Nat.div_lt_self hN0 (by omega)
  -- `2·M ≤ N/k` as reals, from `M·(2k) ≤ N`.
  have h2M : 2 * (M : ℝ) ≤ (N : ℝ) / k := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < k)]
    have hnat : M * (2 * k) ≤ N := Nat.div_mul_le_self N (2 * k)
    have : (M : ℝ) * (2 * k) ≤ N := by exact_mod_cast hnat
    nlinarith [this]
  -- `√M < M`, since `M ≥ 2 > 1`.
  have hsqrt : Real.sqrt (M : ℝ) < (M : ℝ) := by
    have hM2R : (2 : ℝ) ≤ M := by exact_mod_cast hM2
    calc Real.sqrt (M : ℝ) < Real.sqrt ((M : ℝ) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
      _ = (M : ℝ) := Real.sqrt_sq (by positivity)
  -- The accuracy event at `M` is empty: no grid value is within `√M` of `M`.
  have hempty : {ω | |samplingEstimator N k ω - (M : ℝ)| ≤ Real.sqrt (M : ℝ)}
      = (∅ : Set (Fin k → Bool)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have hS : samplingEstimator N k ω
        = (N : ℝ) / k * ((∑ i : Fin k, if ω i = true then 1 else 0 : ℕ) : ℝ) := by
      rw [samplingEstimator_apply, sampleIndicator_sum_eq_cast]
    have hgap : (M : ℝ) ≤ |samplingEstimator N k ω - (M : ℝ)| := by
      rw [hS]; exact resolution_gap M _ h2M
    linarith
  -- Contradiction: `3/4 ≤ μ(∅) = 0`.
  have hcontra := hacc M (by omega) (by omega)
  rw [hempty, measureReal_empty] at hcontra
  linarith

end AxQM.Concrete
