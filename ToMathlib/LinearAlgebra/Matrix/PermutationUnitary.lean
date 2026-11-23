/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitarity and diagonal conjugation of permutation matrices

Two general facts about the permutation matrix `Equiv.Perm.permMatrix R σ` over a commutative star
ring `R`, sitting at the `permMatrix` / `unitaryGroup` level (below any analysis) so that the
spectral majorization development (`ToMathlib/Analysis/Matrix/HermitianMajorization.lean`) and
concrete permutation-gate calculations can share a single copy.

## Main statements

* `Matrix.permMatrix_mem_unitaryGroup`: a permutation matrix over a commutative star ring is
  unitary.
* `Matrix.permMatrix_mul_diagonal_mul_conjTranspose`: conjugating a diagonal matrix by a permutation
  matrix permutes the diagonal entries, `Pσ * diagonal v * Pσᴴ = diagonal (v ∘ σ)`.

## Tags

permutation matrix, unitary, diagonal, conjugation
-/

public section

open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] [StarRing R]

/-- A permutation matrix over a commutative star ring is unitary:
`star (permMatrix σ) = permMatrix σ⁻¹` and `permMatrix σ * permMatrix σ⁻¹ = permMatrix 1 = 1`. -/
theorem permMatrix_mem_unitaryGroup (σ : Equiv.Perm n) : σ.permMatrix R ∈ unitaryGroup n R := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul,
    inv_mul_cancel, permMatrix_one]

/-- Conjugating a diagonal matrix by a permutation matrix permutes the diagonal entries:
`Pσ * diagonal v * Pσᴴ = diagonal (v ∘ σ)`, for a permutation `σ` and any commutative star ring. -/
theorem permMatrix_mul_diagonal_mul_conjTranspose (σ : Equiv.Perm n) (v : n → R) :
    σ.permMatrix R * diagonal v * (σ.permMatrix R)ᴴ = diagonal (v ∘ σ) := by
  rw [conjTranspose_permMatrix, mul_assoc]
  simp only [Equiv.Perm.permMatrix]
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul, submatrix_submatrix]
  simp only [Function.comp_id, Function.id_comp, Equiv.Perm.inv_def, Equiv.symm_symm,
    submatrix_diagonal_equiv]

end Matrix
