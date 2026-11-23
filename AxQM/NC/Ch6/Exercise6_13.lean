/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalCountingLowerBound

/-!
# Nielsen & Chuang, Exercise 6.13 (classical counting: `ΔS = √(M(N−M)/k)` and `k = Ω(N)`)

*(N&C p. 261.)*

For classical sampling counting estimator, show std dev sqrt(M(N-M)/k) and need k=Omega(N).

The exercise is pure probability/arithmetic about the real-valued estimator `S` and its sampling
law. Compare the other Chapter 6 mathematics exercises, 6.8 and 6.1.

## The formalisation

The `k` samples are modelled as i.i.d. `Bernoulli(M/N)` indicators on `Ω = Fin k → Bool` with the
product measure `sampleSpaceMeasure N M k`; `sampleIndicator k i` is `Xᵢ` and
`samplingEstimator N k = (N/k) • ∑ᵢ Xᵢ` is `S`.

**Standard deviation** — `AxQM/Concrete/ClassicalCountingEstimator.lean` (namespace
`AxQM.Concrete`):

* `samplingEstimator_variance` — `Var S = M(N−M)/k` (from `variance_sum_pi` + `variance_smul`),
  with the per-sample facts `boolIndicator_mean`, `boolIndicator_variance` and the reusable
  `variance_eq_mean_mul_one_sub_mean`.
* `samplingEstimatorStddev_eq` — **the standard deviation**: `ΔS = √(M(N−M)/k)`.

**`k = Ω(N)`** — `AxQM/Concrete/ClassicalCountingLowerBound.lean` (same namespace):

* `resolution_gap` — the arithmetic core: when `2·M ≤ N/k`, every grid value `(N/k)·m` is at
  distance `≥ M` from `M`.
* `samplingEstimator_needs_linear_samples` — **the `Ω(N)` bound**: if `S` estimates every
  `M ∈ [1, N−1]` to within `√M` with probability at least `3/4`, then `N < 4·k`, i.e. `k > N/4`.
  The obstruction is that the estimator's `k + 1` grid values `(N/k)·m` cannot resolve the small
  target `M* = ⌊N/(2k)⌋` once `N ≥ 4k`, so the accuracy event there is empty.
-/
