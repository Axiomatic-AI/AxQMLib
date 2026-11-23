/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import ToMathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Concrete: square root and logarithm of `[[4,3],[3,4]]` (Nielsen & Chuang, Exercise 2.34)

This file formalises **Nielsen & Chuang, Exercise 2.34 (p. 75)**: *find the square root and
logarithm of the matrix*
`A = !![4, 3; 3, 4]`  (N&C (2.57)).

## Method — N&C's operator functions (§2.1.8)

N&C define a function of a normal operator through its spectral decomposition: for
`A = ∑ₐ a |a⟩⟨a|`, one sets `f(A) ≡ ∑ₐ f(a) |a⟩⟨a|`; this "defines the square root of a
positive operator, the logarithm of a positive-definite operator". The matrix `A` here is
real symmetric with eigenvalues

* `7`, with eigenvector `(1, 1)`, and
* `1`, with eigenvector `(1, -1)`,

both positive, so `A` is positive definite and both functions are well-defined. Applying
`√·` and `log ·` to the eigenvalues gives the closed forms

* `√A = !![(1+√7)/2, (√7-1)/2; (√7-1)/2, (1+√7)/2]`  (eigenvalues `√7`, `1`), and
* `log A = (log 7 / 2) • !![1, 1; 1, 1]`  (eigenvalues `log 7`, `log 1 = 0`).

## What is proved

* `matFourThree_isHermitian` — `A` is Hermitian (here, real symmetric).
* `matFourThreeSqrt_mul_self` — `(√A)² = A`, so `√A` is a square root of `A`;
  `matFourThreeSqrt_isHermitian` and `matFourThreeSqrt_posDef` pin it down as *the*
  principal (positive) square root.
* `exp_matFourThreeLog` — `exp(log A) = A`, so `log A` is a logarithm of `A`;
  `matFourThreeLog_isHermitian` records that it is the real-symmetric branch.

The logarithm's defining identity `exp(log A) = A` is proved by diagonalisation: writing
`V = !![1, 1; 1, -1]` for the (unnormalised) eigenvector matrix,
`log A = V · diagonal ![log 7, 0] · V⁻¹`, and `exp` commutes with the conjugation
(`Matrix.exp_conj`) and acts entrywise on the diagonal (`Matrix.exp_diagonal`), collapsing
to `V · diagonal ![7, 1] · V⁻¹ = A`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix

/-- The real symmetric matrix `A = [[4,3],[3,4]]` of Nielsen & Chuang (2.57). -/
noncomputable def matFourThree : Matrix (Fin 2) (Fin 2) ℝ := !![4, 3; 3, 4]

/-- `A` is Hermitian (a real symmetric matrix). -/
theorem matFourThree_isHermitian : matFourThree.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matFourThree, Matrix.conjTranspose_apply]

/-! ## Square root -/

/-- The principal square root `√A = [[(1+√7)/2, (√7-1)/2], [(√7-1)/2, (1+√7)/2]]`,
obtained by applying `√·` to the eigenvalues `7` and `1` of `A`. -/
noncomputable def matFourThreeSqrt : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + Real.sqrt 7) / 2, (Real.sqrt 7 - 1) / 2;
     (Real.sqrt 7 - 1) / 2, (1 + Real.sqrt 7) / 2]

/-- `√A` squares to `A`: it is a square root of `A`. -/
theorem matFourThreeSqrt_mul_self : matFourThreeSqrt * matFourThreeSqrt = matFourThree := by
  have h7 : Real.sqrt 7 * Real.sqrt 7 = 7 := Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matFourThreeSqrt, matFourThree, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h7]

/-- `√A` is Hermitian (real symmetric). -/
theorem matFourThreeSqrt_isHermitian : matFourThreeSqrt.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matFourThreeSqrt, Matrix.conjTranspose_apply]

/-- `√A` is positive definite: together with `matFourThreeSqrt_mul_self` this identifies it
as *the* principal (positive) square root of `A`. The quadratic form evaluates to
`(√7/2)(x₀+x₁)² + (1/2)(x₀-x₁)²`, a sum of squares with strictly positive coefficients. -/
theorem matFourThreeSqrt_posDef : matFourThreeSqrt.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos matFourThreeSqrt_isHermitian
  intro x hx
  have h7 : (1 : ℝ) ≤ Real.sqrt 7 := Real.one_le_sqrt.mpr (by norm_num)
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h
    exact hx (by funext i; fin_cases i <;> simp [h.1, h.2])
  have key : star x ⬝ᵥ matFourThreeSqrt.mulVec x
      = Real.sqrt 7 / 2 * (x 0 + x 1) ^ 2 + 1 / 2 * (x 0 - x 1) ^ 2 := by
    simp only [matFourThreeSqrt, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.star_apply, star_trivial]
    ring
  rw [key]
  have hpos : 0 < (x 0 + x 1) ^ 2 + (x 0 - x 1) ^ 2 := by
    rcases hx' with h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1)]
  nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1), h7, hpos,
    mul_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt 7 - 1) (sq_nonneg (x 0 + x 1))]

/-! ## Logarithm

The logarithm is obtained through the eigen-decomposition `A = V · D · V⁻¹` with
`V = [[1,1],[1,-1]]` and `D = diagonal ![7, 1]`: then `log A = V · diagonal ![log 7, 0] · V⁻¹`,
and `exp` reverses the construction. -/

/-- The (unnormalised) eigenvector matrix `V = [[1,1],[1,-1]]` of `A`; its columns `(1,1)`
and `(1,-1)` are the eigenvectors for the eigenvalues `7` and `1`. -/
noncomputable def matFourThreeEigen : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

/-- The inverse `V⁻¹ = [[1/2,1/2],[1/2,-1/2]]` of the eigenvector matrix. -/
noncomputable def matFourThreeEigenInv : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, -1 / 2]

/-- `V · V⁻¹ = 1`. -/
theorem matFourThreeEigen_mul_inv : matFourThreeEigen * matFourThreeEigenInv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matFourThreeEigen, matFourThreeEigenInv, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The eigenvector matrix `V` is invertible (`det V = -2 ≠ 0`). -/
theorem matFourThreeEigen_isUnit : IsUnit matFourThreeEigen := by
  rw [Matrix.isUnit_iff_isUnit_det, matFourThreeEigen, Matrix.det_fin_two_of, isUnit_iff_ne_zero]
  norm_num

/-- The ring inverse of `V` is the explicit matrix `matFourThreeEigenInv`. -/
theorem matFourThreeEigen_inv_eq : matFourThreeEigen⁻¹ = matFourThreeEigenInv :=
  Matrix.inv_eq_right_inv matFourThreeEigen_mul_inv

/-- Conjugating a diagonal `2×2` matrix by `V`: `V · diagonal ![a,b] · V⁻¹` equals the
symmetric matrix `[[(a+b)/2, (a-b)/2], [(a-b)/2, (a+b)/2]]`. Used for both `log A` and its
exponential. -/
theorem matFourThreeEigen_conj_diagonal (a b : ℝ) :
    matFourThreeEigen * diagonal ![a, b] * matFourThreeEigen⁻¹
      = !![(a + b) / 2, (a - b) / 2; (a - b) / 2, (a + b) / 2] := by
  rw [matFourThreeEigen_inv_eq, Matrix.diagonal_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matFourThreeEigen, matFourThreeEigenInv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The matrix exponential of `diagonal ![log 7, 0]` is `diagonal ![7, 1]`: `exp` acts
entrywise on a diagonal matrix, and `exp (log 7) = 7`, `exp 0 = 1`. -/
theorem exp_diagonal_logSeven :
    NormedSpace.exp (diagonal ![Real.log 7, (0 : ℝ)]) = diagonal ![(7 : ℝ), 1] := by
  rw [Matrix.exp_diagonal]; congr 1; funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.coe_exp, Matrix.cons_val_zero]
    rw [← Real.exp_eq_exp_ℝ]; exact Real.exp_log (by norm_num)
  · simp only [Fin.mk_one, Pi.coe_exp, Matrix.cons_val_one]
    rw [← Real.exp_eq_exp_ℝ]; exact Real.exp_zero

/-- The logarithm `log A = (log 7 / 2) • [[1,1],[1,1]]`, obtained by applying `log ·` to the
eigenvalues `7` and `1` of `A` (with `log 1 = 0`). -/
noncomputable def matFourThreeLog : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.log 7 / 2) • !![1, 1; 1, 1]

/-- `log A` is Hermitian (real symmetric): it is the real-symmetric branch of the logarithm. -/
theorem matFourThreeLog_isHermitian : matFourThreeLog.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matFourThreeLog, Matrix.conjTranspose_apply, Matrix.smul_apply]

/-- `exp(log A) = A`: the matrix `log A` is a logarithm of `A`. -/
theorem exp_matFourThreeLog : NormedSpace.exp matFourThreeLog = matFourThree := by
  have hL : matFourThreeLog
      = matFourThreeEigen * diagonal ![Real.log 7, 0] * matFourThreeEigen⁻¹ := by
    rw [matFourThreeEigen_conj_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matFourThreeLog, Matrix.smul_apply]
  rw [hL, Matrix.exp_conj matFourThreeEigen (diagonal ![Real.log 7, 0]) matFourThreeEigen_isUnit,
    exp_diagonal_logSeven, matFourThreeEigen_conj_diagonal, matFourThree]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

end AxQM.Concrete
