/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Kronecker product: distributing `star` over `⊗ₖ`

Entrywise `star` (complex conjugation of each entry) distributes over the Kronecker product.
-/

@[expose] public section

namespace Matrix

variable {R : Type*}
variable {l m n p : Type*}

section Kronecker

open Kronecker

/-- Entrywise `star` (complex conjugation of each entry) distributes over the Kronecker product.
Together with `Matrix.kroneckerMap_transpose` (transpose) and `Matrix.conjTranspose_kronecker`
(conjugate transpose), this records that conjugation, transpose and adjoint all distribute over
`⊗ₖ`. -/
theorem map_star_kronecker [CommMagma R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x ⊗ₖ y).map star = x.map star ⊗ₖ y.map star := by
  ext; simp

end Kronecker

end Matrix
