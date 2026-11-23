/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Bounds.Basic

/-!
# The least common multiple of two naturals equals `x * y / gcd x y`

For positive naturals `x` and `y`, the number `x * y / Nat.gcd x y` is the *least common multiple*
of `x` and `y`, understood elementarily as the **smallest positive integer that is a multiple of
both** `x` and `y`.

## Main results

* `Nat.isLeast_pos_common_multiple` — for `0 < x` and `0 < y`, the value `x * y / Nat.gcd x y` is
  the least element, in the usual order `≤`, of the set `{m | 0 < m ∧ x ∣ m ∧ y ∣ m}` of positive
  common multiples of `x` and `y`.

The statement characterises "the least common multiple" from first principles — via divisibility
and the order on `ℕ`, with **no reference to `Nat.lcm` in the statement** — so the identity with the
formula `x * y / gcd x y` is a genuine theorem rather than an unfolding of a definition. (As it
happens `Nat.lcm x y` is *defined* to be `x * y / Nat.gcd x y`; the theorem therefore also certifies
that `Nat.lcm` deserves its name, being the least positive common multiple. That naming fact is what
`Nat.lcm` provides in its proof via `Nat.dvd_lcm_left`, `Nat.dvd_lcm_right` and `Nat.lcm_dvd`.)

Positivity of `x` and `y` is genuinely required: if either is `0` the set of positive common
multiples is empty (`0 ∣ m ↔ m = 0`), so it has no least element, matching the hypothesis of the
source.

## Motivation (Nielsen & Chuang, Exercise 5.15)

This is the mathematical content of Nielsen & Chuang's *Quantum Computation and Quantum
Information*, Exercise 5.15 (p. 231, §5.3.2): "the least common multiple of positive integers `x`
and `y` is `xy / gcd(x, y)`". The exercise's further remark that this "may be computed in `O(L²)`
operations if `x` and `y` are `L`-bit numbers" is a computational-complexity claim about a cost
model the library does not have, and is out of scope.
-/

public section

namespace Nat

/-- For positive naturals `x` and `y`, the number `x * y / Nat.gcd x y` is the least common multiple
of `x` and `y`: it is the least element, in the order `≤`, of the set of *positive common multiples*
`{m | 0 < m ∧ x ∣ m ∧ y ∣ m}`.

This is Nielsen & Chuang's Exercise 5.15 — "the least common multiple of positive integers `x` and
`y` is `xy / gcd(x, y)`" — with "least common multiple" characterised elementarily as the smallest
positive integer divisible by both `x` and `y`. The characterisation names no `Nat.lcm`, so the
identification with the formula `x * y / gcd x y` is proved, not definitional. -/
theorem isLeast_pos_common_multiple {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    IsLeast {m : ℕ | 0 < m ∧ x ∣ m ∧ y ∣ m} (x * y / Nat.gcd x y) := by
  -- `x * y / gcd x y` is definitionally `Nat.lcm x y`; work through the standard `Nat.lcm` API.
  change IsLeast {m : ℕ | 0 < m ∧ x ∣ m ∧ y ∣ m} (Nat.lcm x y)
  refine ⟨⟨?_, Nat.dvd_lcm_left x y, Nat.dvd_lcm_right x y⟩, ?_⟩
  · -- Membership: `Nat.lcm x y` is a positive common multiple of `x` and `y`; positivity from
    -- `Nat.lcm_ne_zero`, both factors being nonzero.
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero hx.ne' hy.ne')
  · -- Lower bound: every positive common multiple `m` is `≥ Nat.lcm x y`, since `Nat.lcm x y ∣ m`.
    rintro m ⟨hm, hxm, hym⟩
    exact Nat.le_of_dvd hm (Nat.lcm_dvd hxm hym)

end Nat
