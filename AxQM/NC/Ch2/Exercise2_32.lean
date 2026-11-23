/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.KroneckerProjection

/-!
# Nielsen & Chuang, Exercise 2.32 (Tensor product of two projectors is a projector)

Show the tensor product of two projectors is a projector.

N&C define a **projector** (§2.1.5, Box 2.2) as a self-adjoint idempotent operator: `P† = P` and
`P² = P`. In the concrete matrix picture the tensor product of two operators is the **Kronecker
product** `A ⊗ₖ B` (eq. (2.50)). The exercise asks to show that if `P` and `Q` are projectors then
`P ⊗ Q` is a projector — i.e. `P ⊗ Q` is self-adjoint and idempotent.

## The declarations

In `ToMathlib/LinearAlgebra/Matrix/KroneckerProjection.lean`:

* `IsIdempotentElem.kronecker` — the `P² = P` half: the Kronecker product of two idempotent matrices
  is idempotent, `(A ⊗ₖ B) * (A ⊗ₖ B) = A ⊗ₖ B`.
* `IsStarProjection.kronecker` — **the exercise**: the Kronecker product of two star projections
  (self-adjoint idempotents) is a star projection.

## N&C ↦ Mathlib dictionary and fidelity

* A **projector** `P` (self-adjoint, `P† = P`, and idempotent, `P² = P`) is `IsStarProjection P`,
  Mathlib's bundling of `IsSelfAdjoint P` (`star P = P`, i.e. `Pᴴ = P` for matrices) with
  `IsIdempotentElem P` (`P * P = P`). This is exactly N&C's definition.
* The **tensor product of operators** `P ⊗ Q` is the Kronecker product `A ⊗ₖ B`
  (`Matrix.kroneckerMap (· * ·)`, N&C eq. (2.50)), the concrete matrix representation N&C uses for
  the operator tensor product.
* The formalisation fixes **no dimension** and holds for matrices over **any** commutative star ring
  (`CommSemiring` + `StarRing` entries, e.g. `ℂ`) indexed by arbitrary finite types, so it is a
  faithful transcription of the exercise rather than a weakening: N&C's finite-dimensional complex
  case is the special case `α = ℂ`, `m`, `n` finite.
* **Self-adjointness** of `A ⊗ₖ B` is `Matrix.IsHermitian.kronecker` (N&C Exercise 2.30 — the
  Kronecker product of two Hermitian matrices is Hermitian), transported across
  `Matrix.isHermitian_iff_isSelfAdjoint`; that lemma is in turn proved via
  `Matrix.conjTranspose_kronecker` (`(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`, the Kronecker case of N&C
  Exercise 2.28's `(A ⊗ B)† = A† ⊗ B†`). **Idempotence** reduces, via `Matrix.mul_kronecker_mul`
  (`(A ⊗ₖ B) * (A ⊗ₖ B) = (A * A) ⊗ₖ (B * B)`), to the idempotence of the factors.
-/
