/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Data.Nat.GCD.LeastCommonMultiple

/-!
# Nielsen & Chuang, Exercise 5.15 (`lcm(x, y) = xy / gcd(x, y)`)

Show lcm(x,y)=xy/gcd(x,y), computable in O(L^2) operations for L-bit numbers.
*(N&C p. 231, §5.3.2 — extracting the order `r` as `lcm(r₁, r₂)` in Shor's order-finding.)*

## What is formalised, and where

The formalisation is `Nat.isLeast_pos_common_multiple` in
`ToMathlib/Data/Nat/GCD/LeastCommonMultiple.lean` (namespace `Nat`):

* `Nat.isLeast_pos_common_multiple` — for `0 < x` and `0 < y`,
  `IsLeast {m : ℕ | 0 < m ∧ x ∣ m ∧ y ∣ m} (x * y / Nat.gcd x y)`. That is, the formula
  `x * y / gcd(x, y)` — N&C's `xy / gcd(x, y)` verbatim — is the least element, under the order `≤`,
  of the set of *positive common multiples* of `x` and `y`. This is exactly "the least common
  multiple of `x` and `y` equals `xy / gcd(x, y)`".

### Why this shape (fidelity, not circularity)

Mathlib's `Nat.lcm x y` is *defined* as `x * y / Nat.gcd x y`, so the naive statement
`Nat.lcm x y = x * y / Nat.gcd x y` is a definitional `rfl` — it asserts nothing about *why* the
least common multiple has that value, and is not a faithful rendering of the exercise. The
formalisation instead characterises "least common multiple" **from first principles**: the set
`{m | 0 < m ∧ x ∣ m ∧ y ∣ m}` is the positive common multiples, built from divisibility alone, and
`IsLeast` picks the smallest positive integer divisible by both `x` and `y` — precisely the
elementary meaning of "least common multiple". The theorem then proves that this least element *is*
the formula `xy / gcd(x, y)`. No `Nat.lcm` appears in the statement, so the identity is a genuine
theorem. (In the proof, `Nat.lcm`'s own lemmas supply the divisibility facts: `Nat.dvd_lcm_left`
and `Nat.dvd_lcm_right` show it is a common multiple, `Nat.lcm_dvd` that it divides every common
multiple, and `Nat.lcm_ne_zero` gives positivity — so the result also certifies that `Nat.lcm`
deserves its name.)

## Scope and fidelity

* **Positivity is faithful and necessary.** The source restricts to positive integers `x`, `y`; the
  hypotheses `0 < x`, `0 < y` are exactly this and are load-bearing — for `x = 0` or `y = 0` the set
  of positive common multiples is empty and has no least element, so the claim would be false.
* **The `L`-bit / `O(L²)` clause is not formalised.** It is a computational-complexity claim about
  computing `lcm` via Euclid's algorithm for `gcd` followed by a multiplication and a division; the
  library has no cost model in which to count "operations", so — as with Exercises 5.1, 5.3 and 5.17
  — it is deliberately out of scope. The formal content captured is the arithmetic identity.
-/
