/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Algebra.Ring.Anticommutator

/-!
# Nielsen & Chuang, Exercise 2.44 (Commuting + anticommuting with an invertible operator)

If [A,B]=0, {A,B}=0, A invertible, show B=0.

Here `[A, B] = AB − BA` is the commutator (eq. 2.66) and `{A, B} = AB + BA` is the anticommutator
(eq. 2.67) of two operators `A`, `B` (§2.1.9).

This is a pure ring-algebra fact — commuting and anticommuting force the product to vanish, and
cancelling an invertible factor leaves the other factor zero.

## The formalisation

All in `ToMathlib/Algebra/Ring/Anticommutator.lean`, reusing that file's `anticommutator` (eq.
2.67),
Mathlib's ring Lie bracket `⁅·, ·⁆` for the commutator (eq. 2.66), and the half-sum identity
`lie_add_anticommutator_eq_two_nsmul_mul` (`⁅a, b⁆ + anticommutator a b = 2 • (a * b)`, Exercise
2.42):

* `mul_eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero` — the algebraic core: in a ring in which
  `2` is invertible, `⁅a, b⁆ = 0` and `anticommutator a b = 0` together give `a * b = 0` (the
  commutator and anticommutator sum to `2 • (a * b) = 0`, and `2` is invertible).
* `eq_zero_of_lie_eq_zero_of_anticommutator_eq_zero` — the exercise itself: if in addition `a` is a
  unit, then `b = 0` (cancel the unit `a` in `a * b = 0`).

## Design notes (fidelity and generality)

N&C's `A`, `B` are operators on a complex Hilbert space with `A` invertible; concretely these are
`Matrix n n ℂ` (or `End ℂ V`), a ring in which `2` is invertible and "invertible" means a unit. The
statements are given over an arbitrary `Ring A` with `Invertible (2 : A)` and `IsUnit a`, so they
render the exercise faithfully as a strict generalisation, not a weakening.

The hypothesis that `2` is invertible is genuinely necessary, not a convenience: in characteristic
`2` the commutator and anticommutator coincide (both equal `AB + BA`), so `A = B = I` satisfies both
`[A, B] = 0` and `{A, B} = 0` with `A` invertible yet `B = I ≠ 0`. The exercise is therefore false
without it; requiring `Invertible (2 : A)` is faithful to N&C's `ℂ` setting, where it holds.
-/
