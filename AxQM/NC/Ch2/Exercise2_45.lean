/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Algebra.Star.Commutator

/-!
# Nielsen & Chuang, Exercise 2.45 (Adjoint of a commutator)

Show [A,B]^dagger = [B^dagger, A^dagger].

This is a pure `*`-ring identity — the adjoint (an additive, multiplication-reversing
involution) applied to the commutator (the ring Lie bracket).

## The formalisation

In `ToMathlib/Algebra/Star/Commutator.lean`:

* `star_lie` — the adjoint reverses the commutator, `star ⁅a, b⁆ = ⁅star b, star a⁆`, for any
  elements `a`, `b` of a (non-unital, non-associative) star ring, where `⁅·, ·⁆` is the ring Lie
  bracket `a * b - b * a` (`Ring.lie_def`).

## Notes

N&C's operators `A`, `B` act on a complex Hilbert space; in the concrete matrix picture these are
`Matrix n n ℂ`, a star ring whose `star` is the conjugate transpose `ᴴ` (the adjoint). The general
lemma therefore specialises directly to N&C's `[A, B]ᴴ = [Bᴴ, Aᴴ]`, so the statement over an
arbitrary star ring is a faithful generalisation of the exercise, not a weakening. The reversal of
the two operands on the right (`[B†, A†]`, not `[A†, B†]`) is exactly the anti-homomorphism
behaviour of `star` on products (`star_mul`), the same reversal seen in Exercise 2.13's
`(|w⟩⟨v|)† = |v⟩⟨w|`.
-/
