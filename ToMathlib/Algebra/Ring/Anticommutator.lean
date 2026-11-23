/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.Abel

/-!
# The anticommutator of two ring elements

For two elements `a` and `b` of a ring, this file defines their *anticommutator*
`anticommutator a b = a * b + b * a`, the symmetric counterpart of the commutator
`⁅a, b⁆ = a * b - b * a` (the Lie bracket on a ring, `Ring.lie_def`).

The commutator and the anticommutator sum to twice the product, so — as soon as `2` is invertible —
the product itself is recovered as their half-sum. This is **Nielsen & Chuang, Exercise 2.42**
(*Quantum Computation and Quantum Information*, §2.1.9): `AB = ([A, B] + {A, B}) / 2`, where `[·,·]`
and `{·,·}` are the commutator (eq. (2.66)) and anticommutator (eq. (2.67)) of two operators.

## Main definitions

* `anticommutator a b` : the anticommutator `a * b + b * a`.

## Main results

* `lie_add_anticommutator_eq_two_nsmul_mul` : the division-free heart of the decomposition — the
  commutator and the anticommutator sum to twice the product,
  `⁅a, b⁆ + anticommutator a b = 2 • (a * b)`, in any (non-unital, non-associative) ring.
* `mul_eq_invOf_two_mul_lie_add_anticommutator` : in a ring in which `2` is invertible, the product
  is the half-sum `a * b = ⅟2 * (⁅a, b⁆ + anticommutator a b)`.
* `mul_eq_invOf_two_smul_lie_add_anticommutator` : the same decomposition for an algebra over a
  commutative (semi)ring in which `2` is invertible, with `1 / 2` acting as a scalar,
  `a * b = ⅟(2 : 𝕜) • (⁅a, b⁆ + anticommutator a b)`. This is the form matching Nielsen & Chuang's
  operators over `ℂ`, where the division by `2` is scalar division.
* `mul_eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero` : if two elements of a ring in which `2` is
  invertible both commute and anticommute (`⁅a, b⁆ = 0` and `anticommutator a b = 0`), then their
  product vanishes, `a * b = 0`.
* `eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero` : **Nielsen & Chuang, Exercise 2.44** — if
  moreover `a` is a unit, then `b = 0`.
-/

@[expose] public section

variable {A : Type*}

/-- The **anticommutator** `a * b + b * a` of two elements of a (non-unital, non-associative) ring;
the symmetric counterpart of the commutator (Lie bracket) `⁅a, b⁆ = a * b - b * a`. -/
def anticommutator [Mul A] [Add A] (a b : A) : A := a * b + b * a

/-- Unfolding lemma for `anticommutator`: `anticommutator a b = a * b + b * a`. -/
theorem anticommutator_def [Mul A] [Add A] (a b : A) :
    anticommutator a b = a * b + b * a := rfl

/-- The anticommutator is symmetric in its two arguments. -/
theorem anticommutator_comm [Mul A] [AddCommMagma A] (a b : A) :
    anticommutator a b = anticommutator b a := add_comm _ _

/-- The commutator and the anticommutator of two ring elements sum to twice their product:
`⁅a, b⁆ + anticommutator a b = 2 • (a * b)`. This division-free identity is the heart of the
decomposition of a product into its antisymmetric and symmetric parts. -/
theorem lie_add_anticommutator_eq_two_nsmul_mul [NonUnitalNonAssocRing A] (a b : A) :
    ⁅a, b⁆ + anticommutator a b = 2 • (a * b) := by
  rw [Ring.lie_def, anticommutator]
  abel

/-- In a ring in which `2` is invertible, a product is the half-sum of the commutator and the
anticommutator: `a * b = ⅟2 * (⁅a, b⁆ + anticommutator a b)`. This is the ring form of
**Nielsen & Chuang, Exercise 2.42**. -/
theorem mul_eq_invOf_two_mul_lie_add_anticommutator [Ring A] [Invertible (2 : A)] (a b : A) :
    a * b = ⅟2 * (⁅a, b⁆ + anticommutator a b) := by
  rw [lie_add_anticommutator_eq_two_nsmul_mul, nsmul_eq_mul, Nat.cast_ofNat, invOf_mul_cancel_left]

/-- For an algebra over a commutative (semi)ring in which `2` is invertible, a product is the
half-sum of the commutator and the anticommutator, with `1 / 2` acting as a scalar:
`a * b = ⅟(2 : 𝕜) • (⁅a, b⁆ + anticommutator a b)`. This is the form of
**Nielsen & Chuang, Exercise 2.42** matching their operators over `ℂ`, where the division by `2` is
scalar division. -/
theorem mul_eq_invOf_two_smul_lie_add_anticommutator
    {𝕜 : Type*} [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A] [Invertible (2 : 𝕜)] (a b : A) :
    a * b = ⅟(2 : 𝕜) • (⁅a, b⁆ + anticommutator a b) := by
  rw [lie_add_anticommutator_eq_two_nsmul_mul, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    Nat.cast_ofNat, invOf_mul_self, one_smul]

/-- If two elements of a ring in which `2` is invertible both **commute** (`⁅a, b⁆ = 0`) and
**anticommute** (`anticommutator a b = 0`), then their product is zero, `a * b = 0`. Indeed `a * b`
is the half-sum `⅟2 * (⁅a, b⁆ + anticommutator a b)`
(`mul_eq_invOf_two_mul_lie_add_anticommutator`), which vanishes once both brackets do. -/
theorem mul_eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero [Ring A] [Invertible (2 : A)] {a b : A}
    (hlie : ⁅a, b⁆ = 0) (hanti : anticommutator a b = 0) : a * b = 0 := by
  rw [mul_eq_invOf_two_mul_lie_add_anticommutator, hlie, hanti, add_zero, mul_zero]

/-- **Nielsen & Chuang, Exercise 2.44.** If `a` is a unit in a ring in which `2` is invertible, and
`a` both commutes and anticommutes with `b` (`⁅a, b⁆ = 0` and `anticommutator a b = 0`), then
`b = 0`. Commuting and anticommuting force `a * b = 0` (via
`mul_eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero`), and cancelling the unit `a` leaves `b = 0`.
The hypothesis that `2` is invertible cannot be dropped: in characteristic `2` the commutator and
anticommutator coincide, and `a = b = 1` is a counterexample. -/
theorem eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero [Ring A] [Invertible (2 : A)] {a b : A}
    (hlie : ⁅a, b⁆ = 0) (hanti : anticommutator a b = 0) (ha : IsUnit a) : b = 0 :=
  ha.mul_right_eq_zero.mp (mul_eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero hlie hanti)

end
