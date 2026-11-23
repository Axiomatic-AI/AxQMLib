/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Star (adjoint) and the commutator

For elements `a` and `b` of a star ring, this file records how the star (adjoint) operation
interacts with the commutator `⁅a, b⁆ = a * b - b * a` (the Lie bracket on a ring, `Ring.lie_def`).

* **The adjoint of a commutator** is the commutator of the adjoints, **with the order reversed**:
  `star ⁅a, b⁆ = ⁅star b, star a⁆`. This is **Nielsen & Chuang, Exercise 2.45**
  (*Quantum Computation and Quantum Information*, §2.1.9): `[A, B]† = [B†, A†]`, where `[·, ·]` is
  the commutator (eq. (2.66)) and `†` is the adjoint of an operator on a Hilbert space. In the
  concrete matrix picture, operators `A, B : Matrix n n ℂ` form a star ring whose star is the
  conjugate transpose (`Matrix.conjTranspose`, i.e. the adjoint `ᴴ`), so this specialises to
  `[A, B]ᴴ = [Bᴴ, Aᴴ]`.
* **The commutator of two self-adjoint elements is skew-adjoint** (`star ⁅A, B⁆ = -⁅A, B⁆`, the
  `star_eq` special case of the above), and scaling it by a skew-adjoint scalar yields a
  self-adjoint element. Instantiated over `ℂ` with the scalar `Complex.I` this is **Nielsen &
  Chuang, Exercise 2.47**: `i[A, B]` is Hermitian whenever `A` and `B` are.

## Main results

* `star_lie` : the adjoint reverses the commutator, `star ⁅a, b⁆ = ⁅star b, star a⁆`, in any
  (non-unital, non-associative) star ring.
* `IsSelfAdjoint.commutator_mem_skewAdjoint` : the commutator of two self-adjoint elements of a star
  ring is skew-adjoint, `⁅A, B⁆ ∈ skewAdjoint R`.
* `isSelfAdjoint_smul_commutator` : scaling the commutator of two self-adjoint elements by a
  skew-adjoint scalar `s` produces a self-adjoint element, `IsSelfAdjoint (s • ⁅A, B⁆)` — the
  scalar-generalised form of Exercise 2.47 (take the scalar ring `ℂ` and `s = Complex.I`).
-/

@[expose] public section

/-- The **adjoint of a commutator** is the commutator of the adjoints, with the order reversed:
`star ⁅a, b⁆ = ⁅star b, star a⁆`. Because `star` is a multiplicative anti-homomorphism
(`star (a * b) = star b * star a`, `star_mul`) that is additive (`star_sub`), applying it to
`⁅a, b⁆ = a * b - b * a` swaps the two products, which is exactly `⁅star b, star a⁆`.

This is **Nielsen & Chuang, Exercise 2.45**, `[A, B]† = [B†, A†]`: `A` and `B` are operators on a
Hilbert space, which form a star ring under the adjoint `†`. -/
theorem star_lie {R : Type*} [NonUnitalNonAssocRing R] [StarRing R] (a b : R) :
    star ⁅a, b⁆ = ⁅star b, star a⁆ := by
  rw [Ring.lie_def, Ring.lie_def, star_sub, star_mul, star_mul]

namespace IsSelfAdjoint

/-- The commutator `⁅A, B⁆ = A * B - B * A` of two self-adjoint elements of a star ring is
skew-adjoint: `star ⁅A, B⁆ = -⁅A, B⁆`. Equivalently, the commutator of two Hermitian operators is
anti-Hermitian. -/
theorem commutator_mem_skewAdjoint {R : Type*} [NonUnitalNonAssocRing R] [StarRing R] {A B : R}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) : ⁅A, B⁆ ∈ skewAdjoint R := by
  rw [skewAdjoint.mem_iff, Ring.lie_def, star_sub, star_mul, star_mul, hA.star_eq, hB.star_eq,
    neg_sub]

end IsSelfAdjoint

/-- Scaling the commutator `⁅A, B⁆` of two self-adjoint elements of a star ring by a skew-adjoint
scalar `s` yields a self-adjoint element: `IsSelfAdjoint (s • ⁅A, B⁆)`. Instantiating the scalar
ring as `ℂ` and `s` as the imaginary unit `Complex.I` (skew-adjoint by `Complex.conj_I`) recovers
**Nielsen & Chuang, Exercise 2.47**: `i[A, B]` is Hermitian whenever `A` and `B` are. -/
theorem isSelfAdjoint_smul_commutator {S R : Type*} [Ring S] [NonUnitalNonAssocRing R]
    [Module S R] [StarAddMonoid S] [StarRing R] [StarModule S R] {s : S}
    (hs : s ∈ skewAdjoint S) {A B : R} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (s • ⁅A, B⁆) :=
  isSelfAdjoint_smul_of_mem_skewAdjoint hs (hA.commutator_mem_skewAdjoint hB)
