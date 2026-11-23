/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Algebra.Ring.Anticommutator

/-!
# Nielsen & Chuang, Exercise 2.42 (Product as half-sum of commutator and anticommutator)

Verify AB = ([A,B]+{A,B})/2.

This is a ring-algebra identity: a product decomposed into its antisymmetric part (the
commutator) and its symmetric part (the anticommutator).

## The declarations

The formalisation is in `ToMathlib/Algebra/Ring/Anticommutator.lean`.

N&C's **commutator** `[A, B] = AB − BA` (eq. 2.66) is already in Mathlib as the Lie bracket of a
ring, `⁅A, B⁆`, with `Ring.lie_def : ⁅x, y⁆ = x * y - y * x`. Its symmetric counterpart, N&C's
**anticommutator** `{A, B} = AB + BA` (eq. 2.67), is introduced here:

* `anticommutator A B` — the anticommutator `A * B + B * A`, with `anticommutator_def` (unfolding)
  and `anticommutator_comm` (symmetry `{A, B} = {B, A}`).

The exercise's identity `AB = ([A, B] + {A, B}) / 2` (eq. 2.77) is proved in three progressively
concrete forms:

* `lie_add_anticommutator_eq_two_nsmul_mul` — the division-free heart,
  `⁅A, B⁆ + anticommutator A B = 2 • (A * B)`, valid in *any* (non-unital, non-associative) ring.
  Since `[A, B] + {A, B} = (AB − BA) + (AB + BA) = 2AB`, no invertibility of `2` is needed for this
  form.
* `mul_eq_invOf_two_mul_lie_add_anticommutator` — the exercise as stated, in a ring in which `2` is
  invertible: `A * B = ⅟2 * (⁅A, B⁆ + anticommutator A B)`.
* `mul_eq_invOf_two_smul_lie_add_anticommutator` — the form matching N&C's operators over `ℂ`, where
  the `/ 2` is scalar division: for an algebra over a commutative (semi)ring in which `2` is
  invertible, `A * B = ⅟(2 : 𝕜) • (⁅A, B⁆ + anticommutator A B)`.

N&C's `A`, `B` are operators on a complex Hilbert space; in the concrete matrix picture these are
`Matrix n n ℂ`, a `ℂ`-algebra with `Invertible (2 : ℂ)`, so the scalar form
`mul_eq_invOf_two_smul_lie_add_anticommutator` applies directly and renders eq. (2.77) faithfully.
The identity is stated over an arbitrary such ring/algebra, so this is a faithful generalisation of
the exercise, not a weakening.
-/
