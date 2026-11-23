/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit

/-!
# N&C Exercise 11.3 — the binary entropy attains its maximum value of one at p = 1/2

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.3, p. 504.

The exercise asks to prove that the binary entropy `H_bin(p)` attains its maximum value of **one**
at `p = 1/2`. Here `H_bin(p) = -p log p - (1 - p) log (1 - p)` with the logarithm taken to base
`2` — Nielsen & Chuang's standing convention, under which entropy is measured in *bits* and a fair
coin carries exactly one bit. The maximum value being *one* is a feature of this base-`2`
convention: in nats (natural logarithm) the same maximum is `log 2`.

## Where the formalisation lives

The exercise is a statement about a real-valued function `ℝ → ℝ` and `Real.logb 2`.

The declarations (all in `ToMathlib/Analysis/SpecialFunctions/BinaryEntropyBit.lean`):

* `Real.binEntropyBit` — the binary entropy measured in bits, `-p * logb 2 p - (1 - p) *
  logb 2 (1 - p)`, i.e. Nielsen & Chuang's `H_bin`. Mathlib's existing `Real.binEntropy` is the
  natural-logarithm (nats) version; the two differ by the positive scalar `Real.log 2`
  (`Real.binEntropyBit_eq_binEntropy_div_log_two`).
* `Real.binEntropyBit_two_inv` — `binEntropyBit (1/2) = 1`: the value at the maximizer is exactly
  one (a fair coin carries one bit).
* `Real.binEntropyBit_le_one` — `binEntropyBit p ≤ 1` for every real `p`: one is an upper bound.
* `Real.binEntropyBit_eq_one_iff` — `binEntropyBit p = 1 ↔ p = 1/2`: the maximum is attained
  *exactly* at `p = 1/2`. This is the precise content of the exercise (the value *and* its unique
  location).
* `Real.isGreatest_range_binEntropyBit` — the statement `IsGreatest (Set.range binEntropyBit) 1`,
  packaging attainment and the upper bound: `1` is genuinely the greatest value of the function.

## Faithfulness note

Nielsen & Chuang's `H_bin` uses base-`2` logarithms, so "maximum value of one" is a literal claim
about the number `1`; `Real.binEntropyBit` is defined with `Real.logb 2` to match this exactly,
rather than reusing the nats-valued `Real.binEntropy` (whose maximum is `Real.log 2`). The bound
and the equality characterization hold for all real `p`, not only on `[0, 1]` — a strictly stronger
statement than the exercise's implicit domain of probabilities, subsuming it.
-/
