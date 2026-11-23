/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.PolarDecomposition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import ToMathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import ToMathlib.Algebra.BigOperators.Fin

/-!
# Concrete: the polar decompositions of `[[1,0],[1,1]]` (Nielsen & Chuang, Exercise 2.50)

This file formalises **Nielsen & Chuang, Exercise 2.50 (p. 79)**: *find the left and right
polar decompositions of the matrix*
`A = !![1, 0; 1, 1]`  (N&C (2.81)).

It is pure matrix mathematics, stated with `Matrix`, `Real.sqrt`, `Matrix.PosDef`,
`Matrix.unitaryGroup` and `CFC.sqrt`.

## Method — the polar decomposition (N&C Theorem 2.3)

N&C's polar decomposition theorem writes a linear operator `A` as `A = U J = K U` with `U`
unitary and `J ≡ √(A†A)`, `K ≡ √(A A†)` positive. N&C names `A = U J` the *left* polar
decomposition and `A = K U` the *right* one. The operand `A = [[1,0],[1,1]]` is **real**, and
its unique polar factors are therefore real too, so we compute over `ℝ`; "unitary" is the
membership `U ∈ Matrix.unitaryGroup (Fin 2) ℝ` (i.e. `U Uᵀ = 1`), the honest real
specialisation of a complex unitary — a real matrix with `Uᵀ U = 1` is precisely a unitary
matrix that happens to be real, so nothing is weakened.

The Gram matrices are `A†A = [[2,1],[1,1]]` (trace `3`, det `1`) and `A A† = [[1,1],[1,2]]`,
each with eigenvalues `(3 ± √5)/2 = ((1 ± √5)/2)²`. Applying `√·` to the eigenvalues gives the
closed forms

* `J = √(A†A) = (√5)⁻¹ • [[3,1],[1,2]]`  and
* `K = √(A A†) = (√5)⁻¹ • [[2,1],[1,3]]`,

and the shared unitary factor is `U = (√5)⁻¹ • [[2,-1],[1,2]]`.

## What is proved

* `polarExampleUnitary_mem_unitaryGroup` — `U` is unitary.
* `polarExampleLeftFactor_posDef` / `polarExampleRightFactor_posDef` — `J`, `K` are positive
  (definite, hence semidefinite): they are genuine positive operators.
* `polarExampleLeftFactor_mul_self` / `polarExampleRightFactor_mul_self` — `J² = A†A`,
  `K² = A A†`; combined with positivity, `polarExampleLeftFactor_eq_sqrt` /
  `polarExampleRightFactor_eq_sqrt` identify `J = √(A†A)`, `K = √(A A†)` as N&C defines them.
* `polarExampleMat_eq_left_polar` — `A = U J` (the left polar decomposition).
* `polarExampleMat_eq_right_polar` — `A = K U` (the right polar decomposition).
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix MatrixOrder ComplexOrder

/-- The matrix `A = [[1,0],[1,1]]` of Nielsen & Chuang (2.81), whose polar decompositions
are computed in this file. -/
def polarExampleMat : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- The (shared) unitary factor `U = (√5)⁻¹ [[2,-1],[1,2]]` of both polar decompositions. -/
noncomputable def polarExampleUnitary : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • !![2, -1; 1, 2]

/-- The positive factor `J = √(A†A) = (√5)⁻¹ [[3,1],[1,2]]` of the *left* polar decomposition
`A = U J`. -/
noncomputable def polarExampleLeftFactor : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • !![3, 1; 1, 2]

/-- The positive factor `K = √(A A†) = (√5)⁻¹ [[2,1],[1,3]]` of the *right* polar
decomposition `A = K U`. -/
noncomputable def polarExampleRightFactor : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • !![2, 1; 1, 3]

/-- The auxiliary scalar identity `(√5)⁻¹ · (√5)⁻¹ = 5⁻¹`, used to collapse the shared
prefactor of every product below. -/
theorem inv_sqrt_five_mul_self : (Real.sqrt 5)⁻¹ * (Real.sqrt 5)⁻¹ = (5 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

/-- The Gram matrix `A†A = [[2,1],[1,1]]`. -/
theorem polarExampleMat_conjTranspose_mul :
    polarExampleMatᴴ * polarExampleMat = !![2, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polarExampleMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- The Gram matrix `A A† = [[1,1],[1,2]]`. -/
theorem polarExampleMat_mul_conjTranspose :
    polarExampleMat * polarExampleMatᴴ = !![1, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polarExampleMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-! ## The unitary factor -/

/-- The conjugate transpose `Uᴴ = (√5)⁻¹ [[2,1],[-1,2]]`. -/
theorem polarExampleUnitary_conjTranspose :
    polarExampleUnitaryᴴ = (Real.sqrt 5)⁻¹ • !![2, 1; -1, 2] := by
  rw [polarExampleUnitary, Matrix.conjTranspose_smul, star_trivial]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `U` is unitary: `U Uᵀ = 1`. -/
theorem polarExampleUnitary_mem_unitaryGroup :
    polarExampleUnitary ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, polarExampleUnitary_conjTranspose,
    polarExampleUnitary, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_sqrt_five_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply]

/-! ## The left positive factor `J = √(A†A)` -/

/-- `J` is Hermitian (real symmetric). -/
theorem polarExampleLeftFactor_isHermitian : polarExampleLeftFactor.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polarExampleLeftFactor, Matrix.conjTranspose_apply, Matrix.smul_apply]

/-- `J` is positive definite: the quadratic form is `(√5)⁻¹ (2 x₀² + (x₀+x₁)² + x₁²)`, a sum
of squares with strictly positive coefficients. Hence `J` is a genuine positive operator. -/
theorem polarExampleLeftFactor_posDef : polarExampleLeftFactor.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos polarExampleLeftFactor_isHermitian
  intro x hx
  have hinv : 0 < (Real.sqrt 5)⁻¹ := by positivity
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h
    exact hx (by funext i; fin_cases i <;> simp [h.1, h.2])
  have key : star x ⬝ᵥ polarExampleLeftFactor.mulVec x
      = (Real.sqrt 5)⁻¹ * (2 * (x 0) ^ 2 + (x 0 + x 1) ^ 2 + (x 1) ^ 2) := by
    simp only [polarExampleLeftFactor, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Pi.star_apply, star_trivial,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [key]
  have hpos : 0 < 2 * (x 0) ^ 2 + (x 0 + x 1) ^ 2 + (x 1) ^ 2 := by
    rcases hx' with h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
  exact mul_pos hinv hpos

/-- `J² = A†A`: `J` is a square root of the left Gram matrix. -/
theorem polarExampleLeftFactor_mul_self :
    polarExampleLeftFactor * polarExampleLeftFactor = polarExampleMatᴴ * polarExampleMat := by
  rw [polarExampleMat_conjTranspose_mul]
  simp only [polarExampleLeftFactor, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_five_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- `J = √(A†A)`: combining positivity (`polarExampleLeftFactor_posDef`) with `J² = A†A`,
`J` is *the* principal (positive) square root of `A†A`, exactly N&C's `J ≡ √(A†A)`. -/
theorem polarExampleLeftFactor_eq_sqrt :
    CFC.sqrt (polarExampleMatᴴ * polarExampleMat) = polarExampleLeftFactor := by
  have h : polarExampleMatᴴ * polarExampleMat
      = polarExampleLeftFactorᴴ * polarExampleLeftFactor := by
    rw [polarExampleLeftFactor_isHermitian, polarExampleLeftFactor_mul_self]
  rw [h]
  exact polarExampleLeftFactor_posDef.posSemidef.sqrt_conjTranspose_mul_self

/-! ## The right positive factor `K = √(A A†)` -/

/-- `K` is Hermitian (real symmetric). -/
theorem polarExampleRightFactor_isHermitian : polarExampleRightFactor.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polarExampleRightFactor, Matrix.conjTranspose_apply, Matrix.smul_apply]

/-- `K` is positive definite: the quadratic form is `(√5)⁻¹ (x₀² + (x₀+x₁)² + 2 x₁²)`, a sum
of squares with strictly positive coefficients. Hence `K` is a genuine positive operator. -/
theorem polarExampleRightFactor_posDef : polarExampleRightFactor.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos polarExampleRightFactor_isHermitian
  intro x hx
  have hinv : 0 < (Real.sqrt 5)⁻¹ := by positivity
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h
    exact hx (by funext i; fin_cases i <;> simp [h.1, h.2])
  have key : star x ⬝ᵥ polarExampleRightFactor.mulVec x
      = (Real.sqrt 5)⁻¹ * ((x 0) ^ 2 + (x 0 + x 1) ^ 2 + 2 * (x 1) ^ 2) := by
    simp only [polarExampleRightFactor, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Pi.star_apply, star_trivial,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [key]
  have hpos : 0 < (x 0) ^ 2 + (x 0 + x 1) ^ 2 + 2 * (x 1) ^ 2 := by
    rcases hx' with h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
  exact mul_pos hinv hpos

/-- `K² = A A†`: `K` is a square root of the right Gram matrix. -/
theorem polarExampleRightFactor_mul_self :
    polarExampleRightFactor * polarExampleRightFactor = polarExampleMat * polarExampleMatᴴ := by
  rw [polarExampleMat_mul_conjTranspose]
  simp only [polarExampleRightFactor, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_five_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- `K = √(A A†)`: combining positivity (`polarExampleRightFactor_posDef`) with `K² = A A†`,
`K` is *the* principal (positive) square root of `A A†`, exactly N&C's `K ≡ √(A A†)`. -/
theorem polarExampleRightFactor_eq_sqrt :
    CFC.sqrt (polarExampleMat * polarExampleMatᴴ) = polarExampleRightFactor := by
  have h : polarExampleMat * polarExampleMatᴴ
      = polarExampleRightFactorᴴ * polarExampleRightFactor := by
    rw [polarExampleRightFactor_isHermitian, polarExampleRightFactor_mul_self]
  rw [h]
  exact polarExampleRightFactor_posDef.posSemidef.sqrt_conjTranspose_mul_self

/-! ## The two polar decompositions -/

/-- **Left polar decomposition** `A = U J` (N&C, `A = U J`): the matrix `A` factors as the
unitary `U` times the positive `J = √(A†A)`. -/
theorem polarExampleMat_eq_left_polar :
    polarExampleMat = polarExampleUnitary * polarExampleLeftFactor := by
  simp only [polarExampleUnitary, polarExampleLeftFactor, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, inv_sqrt_five_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polarExampleMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- **Right polar decomposition** `A = K U` (N&C, `A = K U`): the matrix `A` factors as the
positive `K = √(A A†)` times the unitary `U`. -/
theorem polarExampleMat_eq_right_polar :
    polarExampleMat = polarExampleRightFactor * polarExampleUnitary := by
  simp only [polarExampleUnitary, polarExampleRightFactor, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, inv_sqrt_five_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polarExampleMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

end AxQM.Concrete
