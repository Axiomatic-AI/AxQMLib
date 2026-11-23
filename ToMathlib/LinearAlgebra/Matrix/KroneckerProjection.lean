/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.LinearAlgebra.Matrix.Kronecker
public import ToMathlib.LinearAlgebra.Matrix.Hermitian
public import ToMathlib.Algebra.Star.StarProjection

/-!
# The Kronecker product of two star projections is a star projection

A **star projection** (`IsStarProjection`) is a self-adjoint idempotent — exactly Nielsen &
Chuang's notion of a *projector* (*Quantum Computation and Quantum Information*, §2.1.5 / Box 2.2):
an operator `P` with `P† = P` and `P² = P`. In the concrete matrix picture the tensor product of
two operators is the **Kronecker product** `A ⊗ₖ B` (N&C eq. (2.50)), so this file proves that the
Kronecker product of two projectors is again a projector — **Nielsen & Chuang, Exercise 2.32**.

## Main results

* `IsIdempotentElem.kronecker`: the Kronecker product of two idempotent matrices is idempotent,
  `(A ⊗ₖ B)² = A ⊗ₖ B`. This is the `P² = P` half, and holds for any commutative semiring of
  entries.
* `IsStarProjection.kronecker`: **Nielsen & Chuang, Exercise 2.32** — the Kronecker product of two
  star projections is a star projection.

## Implementation notes

The idempotence half uses `Matrix.mul_kronecker_mul` (`(A ⊗ₖ B) * (A ⊗ₖ B) = (A * A) ⊗ₖ (B * B)`)
to reduce to the idempotence of the factors. The self-adjointness half reuses
`Matrix.IsHermitian.kronecker` (Exercise 2.30 — the Kronecker product of two Hermitian matrices is
Hermitian), with `Matrix.isHermitian_iff_isSelfAdjoint` moving between the star-ring predicate
`IsSelfAdjoint` and its matrix spelling `Matrix.IsHermitian` (`Aᴴ = A`).
-/

@[expose] public section

open scoped Kronecker Matrix

variable {α : Type*} {m n : Type*}

/-- The Kronecker product of two idempotent matrices is idempotent: `(A ⊗ₖ B)² = A ⊗ₖ B`.

Since the Kronecker product turns products of matrices into products of Kronecker products
(`Matrix.mul_kronecker_mul`), `(A ⊗ₖ B) * (A ⊗ₖ B) = (A * A) ⊗ₖ (B * B)`, which collapses to
`A ⊗ₖ B` by the idempotence of `A` and `B`. -/
theorem IsIdempotentElem.kronecker [Fintype m] [Fintype n] [CommSemiring α]
    {A : Matrix m m α} {B : Matrix n n α} (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) :
    IsIdempotentElem (A ⊗ₖ B) := by
  rw [IsIdempotentElem, ← Matrix.mul_kronecker_mul, hA.eq, hB.eq]

/-- **Nielsen & Chuang, Exercise 2.32.** The Kronecker product `A ⊗ₖ B` of two star projections
(self-adjoint idempotents) is a star projection.

The idempotence half is `IsIdempotentElem.kronecker`; the self-adjointness half is
`Matrix.IsHermitian.kronecker` (Exercise 2.30), transported across
`Matrix.isHermitian_iff_isSelfAdjoint`. -/
theorem IsStarProjection.kronecker [Fintype m] [Fintype n] [CommSemiring α] [StarRing α]
    {A : Matrix m m α} {B : Matrix n n α} (hA : IsStarProjection A) (hB : IsStarProjection B) :
    IsStarProjection (A ⊗ₖ B) := by
  refine ⟨hA.isIdempotentElem.kronecker hB.isIdempotentElem, ?_⟩
  exact Matrix.isHermitian_iff_isSelfAdjoint.mp
    ((Matrix.isHermitian_iff_isSelfAdjoint.mpr hA.isSelfAdjoint).kronecker
      (Matrix.isHermitian_iff_isSelfAdjoint.mpr hB.isSelfAdjoint))

end
