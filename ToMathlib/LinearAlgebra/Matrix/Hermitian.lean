/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import ToMathlib.LinearAlgebra.Matrix.Kronecker

/-! # Hermitian matrices: the Kronecker product

Extends `Mathlib.LinearAlgebra.Matrix.Hermitian` with the fact that the Kronecker product of two
Hermitian matrices is Hermitian.
-/

@[expose] public section

namespace Matrix

variable {m n α : Type*}

section Kronecker

open scoped Kronecker

variable [CommMagma α] [StarMul α]

/-- The Kronecker product of two Hermitian matrices is Hermitian.

This is Nielsen & Chuang, Exercise 2.30 (*the tensor product of two Hermitian operators is
Hermitian*): using that the conjugate transpose distributes over the Kronecker product
(`Matrix.conjTranspose_kronecker`), `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ = A ⊗ₖ B`. Commutativity of the
entries is needed because `star` is an anti-homomorphism. -/
theorem IsHermitian.kronecker {A : Matrix m m α} {B : Matrix n n α} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_kronecker, hA.eq, hB.eq]

end Kronecker

end Matrix
