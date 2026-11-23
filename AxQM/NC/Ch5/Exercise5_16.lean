/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.SumInvSqBound

/-!
# Nielsen & Chuang, Exercise 5.16 (`∑ 1/q² ≤ 3/4` via an integral bound)

For x>=2 prove int_x^{x+1} 1/y^2 dy >= 2/(3x^2), and sum_q 1/q^2 <= 3/2 int_2^inf 1/y^2 dy = 3/4.

## The declarations

All in `ToMathlib/Analysis/SpecialFunctions/SumInvSqBound.lean`:

* `two_div_three_mul_sq_le_integral_one_div_sq` — the exercise's **first claim**: for `x ≥ 2`,
  `2/(3x²) ≤ ∫_x^{x+1} 1/y² dy`. The exact value of the integral is `1/x - 1/(x+1) = 1/(x(x+1))`
  (`integral_one_div_sq`), and `2/(3x²) ≤ 1/(x(x+1)) ⇔ 2x ≤ x²`, which holds for `x ≥ 2` with
  equality at `x = 2`.
* `integral_Ioi_one_div_sq_two` — `∫_2^∞ 1/y² dy = 1/2`, so that `(3/2) ∫_2^∞ 1/y² dy = 3/4`, the
  middle expression in the exercise.
* `tsum_one_div_sq_two_le` — the exercise's **second claim** (integer form):
  `∑_{n ≥ 2} 1/n² ≤ 3/4`.
* `Nat.Primes.tsum_one_div_sq_le` — the second claim in the **prime form** actually used by N&C:
  `∑_{p prime} 1/p² ≤ 3/4`.

Supporting reusable lemmas in the same file: `integral_one_div_sq` (`∫_a^b 1/y² = 1/a - 1/b`),
`intervalIntegrable_one_div_sq`, `sum_Ico_one_div_sq_le` (the uniform partial-sum bound
`∑_{2 ≤ n < N} 1/n² ≤ 3/4`), and `sum_one_div_sq_le_of_two_le` (any finite set of integers `≥ 2`).

## Proof method (faithful to N&C's technique)

N&C's "simple technique" is exactly the integral comparison: from the first claim,
`1/n² ≤ (3/2) ∫_n^{n+1} 1/y² dy` for each integer `n ≥ 2`. Summing the interval integrals over
`n = 2, …, N-1` telescopes (`intervalIntegral.sum_integral_adjacent_intervals_Ico`) to
`∫_2^N 1/y² dy = 1/2 - 1/N`, giving `∑_{2 ≤ n < N} 1/n² ≤ (3/2)(1/2 - 1/N) ≤ 3/4` uniformly in `N`.
Passing to the infinite sum (`Real.tsum_le_of_sum_le`) yields `∑_{n ≥ 2} 1/n² ≤ 3/4`, and the prime
version follows because every prime is `≥ 2`.

## On "and thus that (5.58) holds"

Equation (5.58) of N&C, `1 - ∑_q p(q ∣ s'₁) p(q ∣ s'₂) ≥ 1/4` (sum over primes `q`), is obtained
by combining the prime bound `∑_{p prime} 1/p² ≤ 3/4` proved here with the probabilistic estimate
`p(q ∣ s) ≤ 1/q` established in the surrounding text (a property of the near-uniform distribution
of the measured phase, not part of this exercise). The mathematical content of Exercise 5.16 is the
sum bound; `Nat.Primes.tsum_one_div_sq_le` supplies precisely the `≤ 3/4` that closes (5.58).
-/
