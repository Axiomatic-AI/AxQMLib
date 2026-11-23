/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit

/-!
# N&C Exercise 11.4 — concavity of the binary entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.4, p. 504.

The exercise asks to prove that the binary entropy `H_bin(p)` is a **concave** function, that is
```
H_bin(p x₁ + (1 - p) x₂) ≥ p H_bin(x₁) + (1 - p) H_bin(x₂)    (11.11)
```
for `0 ≤ p, x₁, x₂ ≤ 1`, and, in addition, that it is **strictly concave** — the inequality (11.11)
is an equality only in the trivial cases `x₁ = x₂`, or `p = 0`, or `p = 1`. Here `H_bin` uses the
base-`2` logarithm (Nielsen & Chuang's standing bit convention), i.e. `Real.binEntropyBit`.

## Where the formalisation lives

The exercise is a statement about the real-valued function `Real.binEntropyBit : ℝ → ℝ`.

The declarations (both in `ToMathlib/Analysis/SpecialFunctions/BinaryEntropyBit.lean`):

* `Real.strictConcaveOn_binEntropyBit` — `StrictConcaveOn ℝ (Set.Icc 0 1) binEntropyBit`: the binary
  entropy in bits is **strictly** concave on `[0, 1]`. Mathlib's `StrictConcaveOn` predicate builds
  in exactly the trivial-case exclusions Nielsen & Chuang names — it asserts the strict inequality
  only for distinct points (`x₁ ≠ x₂`) and strictly positive weights (`0 < p`, `0 < 1 - p`) — so
  this single statement is precisely "strictly concave except for `x₁ = x₂`, `p = 0`, or `p = 1`".
* `Real.concaveOn_binEntropyBit` — `ConcaveOn ℝ (Set.Icc 0 1) binEntropyBit`: inequality (11.11),
  the non-strict corollary of the above.

## Design notes

Mathlib already proves strict concavity of the nat-valued entropy, `Real.strictConcave_binEntropy :
StrictConcaveOn ℝ (Set.Icc 0 1) binEntropy`. Since `binEntropyBit p = (log 2)⁻¹ • binEntropy p` and
`(log 2)⁻¹ > 0`, the bit version inherits strict concavity by scaling with a positive constant; the
concave version is then `StrictConcaveOn.concaveOn`. No derivative computation is redone.
-/
