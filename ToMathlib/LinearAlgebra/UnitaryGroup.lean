/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Additional API for the unitary group of matrices

* `Matrix.reindex_mem_unitaryGroup`: reindexing rows and columns by the same equivalence
  preserves unitarity.
-/

public section

universe u v

namespace Matrix

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {α : Type v} [CommRing α] [StarRing α]

/-- **Reindexing a square matrix by one equivalence on both axes preserves unitarity.** If
`M ∈ unitaryGroup n α` then `Matrix.reindex e e M ∈ unitaryGroup p α` for any equivalence
`e : n ≃ p`: reindexing by the same equivalence on rows and columns is conjugation by a permutation,
a `⋆`-preserving monoid map. -/
theorem reindex_mem_unitaryGroup {p : Type*} [DecidableEq p] [Fintype p] (e : n ≃ p)
    {M : Matrix n n α} (hM : M ∈ Matrix.unitaryGroup n α) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup p α := by
  rw [mem_unitaryGroup_iff] at hM ⊢
  rw [reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix, ← star_eq_conjTranspose,
    submatrix_mul_equiv M (star M) _ e.symm _, hM, submatrix_one _ e.symm.injective]

end Matrix
