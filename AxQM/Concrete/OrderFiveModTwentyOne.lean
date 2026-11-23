/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Concrete: the order of `5` modulo `21` is `6`

Nielsen & Chuang, Exercise 5.10 (§5.3.1, p. 226): *show that the order of `x = 5` modulo
`N = 21` is `6`*. The **order of `x` modulo `N`** is, by definition, the least positive integer
`r` with `x^r ≡ 1 (mod N)` — equivalently the multiplicative order of the residue `x` in the ring
`ZMod N`, i.e. Mathlib's `orderOf (x : ZMod N)`. Here the residues run

`5¹ = 5, 5² = 4, 5³ = 20, 5⁴ = 16, 5⁵ = 17, 5⁶ = 1 (mod 21)`,

so the order is exactly `6`.

This is an explicit numerical fact about a specific residue. (Chapter 5's order-finding subroutine
and its reduction of factoring to order-finding are what compute such an `r` on a quantum computer;
the arithmetic value itself is pure number theory.)
-/

namespace AxQM.Concrete

/-- **Nielsen & Chuang, Exercise 5.10.** The multiplicative order of `5` modulo `21` is `6`:
`6` is the least positive integer `r` with `5^r ≡ 1 (mod 21)`.

Proved with `orderOf_eq_of_pow_and_pow_div_prime`: `5⁶ = 1 (mod 21)`, while for each prime
`p ∣ 6` (namely `p = 2, 3`) the proper power `5^(6/p)` is `5³ = 20` resp. `5² = 4`, neither of
which is `1`; hence no proper divisor of `6` is a period and the order is exactly `6`. -/
theorem orderOf_five_zmod_twentyOne : orderOf (5 : ZMod 21) = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime
  · decide
  · intro p hp hpd
    have h2 := hp.two_le
    have h6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpd
    interval_cases p <;> revert hpd <;> decide

end AxQM.Concrete
