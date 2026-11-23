/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Kronecker products: subtraction/sum distribution and commutator lifts

This file collects a few general facts about the Kronecker product `A ⊗ₖ B`
(`Matrix.kroneckerMap (· * ·)`) that are missing from `Mathlib/LinearAlgebra/Matrix/Kronecker.lean`
but follow the same pattern as `Matrix.add_kronecker` / `Matrix.kronecker_add`:

* `Matrix.sub_kronecker` / `Matrix.kronecker_sub` — distribution over subtraction (the `sub`
  analogues of `add_kronecker` / `kronecker_add`);
* `Matrix.sum_kronecker` / `Matrix.kronecker_sum` — distribution over a finite sum.

(The scalar analogues `Matrix.smul_kronecker` / `Matrix.kronecker_smul` already exist upstream.)

It also records the interaction of the two commuting *embeddings* `A ↦ A ⊗ I` and `A ↦ I ⊗ A` of a
square matrix algebra into the Kronecker (tensor) product with the ring commutator
`⁅A, B⁆ = A * B - B * A`. Each embedding is a (unital) ring homomorphism, so it carries the
commutator, and the two images commute:

* `Matrix.lie_kronecker_one` — `⁅A ⊗ I, B ⊗ I⁆ = ⁅A, B⁆ ⊗ I`;
* `Matrix.one_kronecker_lie` — `⁅I ⊗ A, I ⊗ B⁆ = I ⊗ ⁅A, B⁆`;
* `Matrix.lie_kronecker_one_one_kronecker` — `⁅A ⊗ I, I ⊗ B⁆ = 0`;
* `Matrix.one_kronecker_lie_kronecker_one` — `⁅I ⊗ A, B ⊗ I⁆ = 0`.

These are exactly the algebraic facts underlying "the sum of two commuting copies of a Lie algebra
(e.g. `𝔰𝔲(2)` angular momenta) is again a Lie algebra of the same type" for the two tensor factors
of a bipartite matrix system.
-/

public section

namespace Matrix

open scoped Kronecker

variable {α : Type*} {ι l m n p : Type*}

/-- The Kronecker product distributes over subtraction in the left factor
(the `sub` analogue of `Matrix.add_kronecker`). -/
theorem sub_kronecker [NonUnitalNonAssocRing α] (A B : Matrix l m α) (N : Matrix n p α) :
    (A - B) ⊗ₖ N = A ⊗ₖ N - B ⊗ₖ N := by
  ext i j; simp [Matrix.kroneckerMap_apply, sub_mul]

/-- The Kronecker product distributes over subtraction in the right factor
(the `sub` analogue of `Matrix.kronecker_add`). -/
theorem kronecker_sub [NonUnitalNonAssocRing α] (N : Matrix l m α) (A B : Matrix n p α) :
    N ⊗ₖ (A - B) = N ⊗ₖ A - N ⊗ₖ B := by
  ext i j; simp [Matrix.kroneckerMap_apply, mul_sub]

/-- The Kronecker product distributes over a finite sum in the left factor. -/
theorem sum_kronecker [NonUnitalNonAssocSemiring α] [Fintype ι]
    (f : ι → Matrix l m α) (N : Matrix n p α) :
    (∑ i, f i) ⊗ₖ N = ∑ i, (f i ⊗ₖ N) := by
  ext i j; simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

/-- The Kronecker product distributes over a finite sum in the right factor. -/
theorem kronecker_sum [NonUnitalNonAssocSemiring α] [Fintype ι]
    (N : Matrix l m α) (f : ι → Matrix n p α) :
    N ⊗ₖ (∑ i, f i) = ∑ i, (N ⊗ₖ f i) := by
  ext i j; simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

variable [CommRing α] [Fintype n] [DecidableEq n]

/-- The left embedding `A ↦ A ⊗ I` of a square matrix algebra into the Kronecker product carries
the ring commutator: `⁅A ⊗ I, B ⊗ I⁆ = ⁅A, B⁆ ⊗ I`. -/
theorem lie_kronecker_one (A B : Matrix n n α) :
    ⁅A ⊗ₖ (1 : Matrix n n α), B ⊗ₖ (1 : Matrix n n α)⁆ = ⁅A, B⁆ ⊗ₖ (1 : Matrix n n α) := by
  simp only [Ring.lie_def, ← Matrix.mul_kronecker_mul, mul_one, sub_kronecker]

/-- The right embedding `A ↦ I ⊗ A` of a square matrix algebra into the Kronecker product carries
the ring commutator: `⁅I ⊗ A, I ⊗ B⁆ = I ⊗ ⁅A, B⁆`. -/
theorem one_kronecker_lie (A B : Matrix n n α) :
    ⁅(1 : Matrix n n α) ⊗ₖ A, (1 : Matrix n n α) ⊗ₖ B⁆ = (1 : Matrix n n α) ⊗ₖ ⁅A, B⁆ := by
  simp only [Ring.lie_def, ← Matrix.mul_kronecker_mul, one_mul, kronecker_sub]

/-- Elements of the two commuting tensor factors commute: `⁅A ⊗ I, I ⊗ B⁆ = 0`. -/
theorem lie_kronecker_one_one_kronecker (A B : Matrix n n α) :
    ⁅A ⊗ₖ (1 : Matrix n n α), (1 : Matrix n n α) ⊗ₖ B⁆ = 0 := by
  simp only [Ring.lie_def, ← Matrix.mul_kronecker_mul, mul_one, one_mul, sub_self]

/-- Elements of the two commuting tensor factors commute: `⁅I ⊗ A, B ⊗ I⁆ = 0`. -/
theorem one_kronecker_lie_kronecker_one (A B : Matrix n n α) :
    ⁅(1 : Matrix n n α) ⊗ₖ A, B ⊗ₖ (1 : Matrix n n α)⁆ = 0 := by
  simp only [Ring.lie_def, ← Matrix.mul_kronecker_mul, mul_one, one_mul, sub_self]

end Matrix
