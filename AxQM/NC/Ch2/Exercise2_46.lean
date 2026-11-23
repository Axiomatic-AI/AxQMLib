/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Nielsen & Chuang, Exercise 2.46 (Antisymmetry of the commutator)

Show [A,B] = -[B,A].

Here `[A, B] ≡ AB − BA` is the commutator (eq. 2.66) of two operators `A`, `B` (§2.1.9). Swapping
the two arguments negates the commutator: `[A, B] = AB − BA = −(BA − AB) = −[B, A]`.

Like Exercises 2.37 and 2.42, this result was already present in Mathlib.

## The declarations

The result already exists in Mathlib, so nothing new needed to be added:

* `lie_skew` (`Mathlib/Algebra/Lie/Basic.lean`) — the **skew-symmetry of the Lie bracket** in any
  `LieRing`: `−⁅y, x⁆ = ⁅x, y⁆`. Its `symm`/orientation is exactly the exercise:
  `⁅A, B⁆ = −⁅B, A⁆`. Applied to an associative ring `A` — whose Lie bracket *is* N&C's commutator
  (see below) — it is precisely "`[A, B] = −[B, A]`".

The bridge that makes the Lie bracket coincide with N&C's commutator (eq. 2.66):

* `Ring.lie_def` (`Mathlib/Algebra/Ring/Commute.lean`) — for two elements of a (non-unital,
  non-associative) ring the Lie bracket is their commutator, `⁅A, B⁆ = A * B − B * A`; and
  `LieRing.of_associative_ring_bracket` (`Mathlib/Algebra/Lie/OfAssociative.lean`) is the same
  identity specialised to an associative ring `A`. This is N&C's defining formula for `[A, B]`,
  so `lie_skew` read through it is the exercise verbatim.

## N&C ↦ Mathlib dictionary and fidelity

* An **operator** `A` on a space is an element of a (non-commutative) ring — concretely
  `Matrix n n ℂ` or `End ℂ V` — with **product** `AB` the ring multiplication. N&C's **commutator**
  `[A, B] = AB − BA` (eq. 2.66) is Mathlib's ring Lie bracket `⁅A, B⁆` (`Ring.lie_def`). The
  exercise's claim `[A, B] = −[B, A]` is `⁅A, B⁆ = −⁅B, A⁆`, delivered by `(lie_skew A B).symm`.
* **Generality, not weakening.** N&C's `A`, `B` are operators on a complex Hilbert space (finite
  complex matrices / endomorphisms); `lie_skew` holds for *any* `LieRing`, and in particular for the
  Lie ring underlying *any* associative ring — of which `Matrix n n ℂ` and `End ℂ V` are instances,
  with no dimension fixed and no hypothesis beyond `A`, `B` living in the same ring. The matrix face
  N&C has in mind is just this same lemma specialised to `Matrix n n ℂ` (a ring), needing no
  separate statement. So the statement is a faithful generalisation of the exercise, never a
  specialisation of it. The skew-symmetry is an algebraic identity requiring no invertibility of `2`
  or any characteristic hypothesis: `−(BA − AB) = AB − BA` holds in every ring.
-/
