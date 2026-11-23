/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Probability.WeakLaw

/-!
# Nielsen & Chuang, Theorem 12.3 (the law of large numbers)

*(N&C p. 541, Box 12.3.)*

Law of large numbers: p(|S_n - E(X)| > eps) -> 0.

Theorem 12.3 is the classical (`L²`) weak law of large numbers: a purely probabilistic
statement about a sequence of independent, identically distributed real random variables with
finite variance. It is a probability-theory prerequisite for the *classical* data-compression
results of N&C Chapter 12 (the theorem of typical sequences, Theorem 12.2).

## The formalisation

The formalisation is in `ToMathlib/Probability/WeakLaw.lean`, in the measure-theoretic setting: a
sequence `X : ℕ → Ω → ℝ` of pairwise independent, identically distributed random variables with
finite second moment (`MemLp (X 0) 2 μ`) on a probability space `(Ω, μ)`, and the sample average
`Sₙ = (∑ i ∈ Finset.range n, X i) / n`. This is the full generality N&C states (an arbitrary
real random variable `X` with `E(X²) < ∞`, not a finite alphabet); requiring only *pairwise*
independence and *square-integrability* matches N&C's hypotheses (`X` has finite first and second
moments) while being no weaker than mutual independence.

* `ProbabilityTheory.variance_sum_range_div` — N&C Eq. 12.34: the variance of the sample average is
  `Var[X 0] / n`.
* `ProbabilityTheory.meas_abs_sum_range_div_sub_ge_le` — N&C Eq. 12.38: the quantitative Chebyshev
  bound `p(|Sₙ − E(X)| ≥ ε) ≤ Var[X 0] / (n ε²)`.
* `ProbabilityTheory.tendstoInMeasure_sum_range_div` — Theorem 12.3, in the idiomatic form:
  the sample averages `Sₙ` converge *in measure* (in probability) to `E(X) = 𝔼[X 0]`.
* `ProbabilityTheory.tendsto_meas_abs_sum_range_div_sub_gt` — Theorem 12.3 in N&C's literal form:
  for every `ε > 0`, `p(|Sₙ − E(X)| > ε) → 0` as `n → ∞`.

Together these are the formalisation of Theorem 12.3 — a faithful, unweakened rendering. The proof
is exactly N&C's Chebyshev argument (Box 12.3): the variance of `Sₙ` is `Var[X 0] / n`, so
Chebyshev's inequality bounds the deviation probability by `Var[X 0] / (n ε²) → 0`. This is distinct
from and complementary to the elementary finite-alphabet concentration bound
`Real.iid_average_deviation_le` (`ToMathlib/InformationTheory/IIDConcentration.lean`) used for
Theorem 12.2, and to `ProbabilityTheory.strong_law_ae` (the strong law).
-/
