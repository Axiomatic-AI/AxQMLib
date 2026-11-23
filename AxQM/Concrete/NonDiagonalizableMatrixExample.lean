/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A matrix that is not diagonalizable (Nielsen & Chuang, Exercise 2.12)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.12
(p. 69) asks to prove that the matrix

```
⎡ 1  0 ⎤
⎣ 1  1 ⎦
```

(N&C (2.31)) is *not diagonalizable*.

## What "diagonalizable" means here

N&C's own definition (p. 68) calls an operator diagonalizable when it has a
*diagonal representation* `A = ∑ᵢ λᵢ |i⟩⟨i|` in which the `|i⟩` form an
**orthonormal** eigenbasis. That is the notion of *unitary* (orthonormal)
diagonalizability. We prove something strictly stronger: the matrix is not
similar to a diagonal matrix *at all* — there are no invertible `P` and diagonal
`diagonal d` with `M = P * diagonal d * P⁻¹`. Since an orthonormal eigenbasis is
in particular an eigenbasis, orthonormal diagonalizability implies ordinary
diagonalizability; refuting the latter therefore refutes N&C's notion a fortiori.
This is deliberately non-weakening: we prove more than the exercise asks, and the
exercise's claim follows.

## The argument

The matrix `M := !![1, 0; 1, 1]` is unipotent: `M - 1 = !![0, 0; 1, 0]` is a
nonzero matrix whose square is `0`. If `M` were similar to a diagonal matrix,
`M = P * diagonal d * P⁻¹`, then `M - 1 = P * (diagonal d - 1) * P⁻¹`, so
`(diagonal d - 1)² = P⁻¹ * (M - 1)² * P = 0`. As `diagonal d - 1` is diagonal,
its square is the diagonal of the entrywise squares `(dᵢ - 1)²`, so each
`dᵢ = 1`; hence `diagonal d = 1` and `M = P * 1 * P⁻¹ = 1`, contradicting
`M ≠ 1`.

* `shearMatrix` — the matrix `!![1, 0; 1, 1]` of N&C (2.31), a complex `2 × 2`
  matrix (a shear / unipotent matrix).
* `shearMatrix_ne_one` — `shearMatrix ≠ 1`.
* `shearMatrix_sub_one_sq` — `(shearMatrix - 1) ^ 2 = 0` (nonzero nilpotency).
* `shearMatrix_not_diagonalizable` — the exercise: `shearMatrix` is not similar
  to any diagonal matrix.
-/

namespace AxQM.Concrete

open scoped Matrix

/-- **Nielsen & Chuang, Exercise 2.12**, the matrix `!![1, 0; 1, 1]` of N&C
(2.31): a complex `2 × 2` shear (unipotent) matrix. We show below that it is not
diagonalizable. -/
def shearMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 1, 1]

/-- `shearMatrix` is not the identity matrix: its `(1, 0)` entry is `1`, not `0`. -/
theorem shearMatrix_ne_one : shearMatrix ≠ 1 := by
  intro h
  have h10 := congrFun (congrFun h 1) 0
  simp [shearMatrix] at h10

/-- `shearMatrix` is unipotent with a nonzero nilpotent part: `(shearMatrix - 1)`
squares to `0`. Explicitly `shearMatrix - 1 = !![0, 0; 1, 0]`, whose square is the
zero matrix. -/
theorem shearMatrix_sub_one_sq : (shearMatrix - 1) ^ 2 = 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]

/-- **Nielsen & Chuang, Exercise 2.12.** The matrix `!![1, 0; 1, 1]` is not
diagonalizable: there is no invertible `P` and diagonal matrix `diagonal d` with
`shearMatrix = P * diagonal d * P⁻¹`. (This is stronger than N&C's orthonormal
notion of diagonalizability, which it therefore also refutes; see the module
docstring.)

The proof turns any such similarity into `(diagonal d - 1) ^ 2 = 0` via the
nilpotency `shearMatrix_sub_one_sq`; a diagonal matrix squaring to `0` is `0`, so
`diagonal d = 1` and `shearMatrix = 1`, contradicting `shearMatrix_ne_one`. -/
theorem shearMatrix_not_diagonalizable :
    ¬ ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℂ),
      IsUnit P ∧ shearMatrix = P * Matrix.diagonal d * P⁻¹ := by
  rintro ⟨P, d, hP, hM⟩
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  set D := Matrix.diagonal d with hDdef
  -- `D = P⁻¹ * shearMatrix * P`, the diagonal form solved for `D`.
  have hD : D = P⁻¹ * shearMatrix * P := by
    rw [hM, Matrix.mul_assoc P D, Matrix.nonsing_inv_mul_cancel_left _ _ hdet,
      Matrix.nonsing_inv_mul_cancel_right _ _ hdet]
  -- The nilpotent parts are conjugate: `D - 1 = P⁻¹ * (shearMatrix - 1) * P`.
  have hDsub : D - 1 = P⁻¹ * (shearMatrix - 1) * P := by
    have hexp : P⁻¹ * (shearMatrix - 1) * P = P⁻¹ * shearMatrix * P - P⁻¹ * P := by
      noncomm_ring
    rw [hexp, hPP', hD]
  -- Conjugation is a ring map, so `(D - 1) ^ 2` is conjugate to `(shearMatrix - 1) ^ 2 = 0`.
  have hDsq : (D - 1) ^ 2 = 0 := by
    rw [hDsub, pow_two, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc P,
      Matrix.mul_nonsing_inv_cancel_left _ _ hdet, ← Matrix.mul_assoc (shearMatrix - 1),
      ← pow_two, shearMatrix_sub_one_sq, Matrix.zero_mul, Matrix.mul_zero]
  -- `(D - 1) ^ 2` is diagonal, so each entry `(dᵢ - 1) ^ 2 = 0`, forcing `dᵢ = 1`.
  have hdi : ∀ i, d i = 1 := by
    have hpow : (D - 1) ^ 2 = Matrix.diagonal (fun i => (d i - 1) ^ 2) := by
      rw [hDdef, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_pow]
      rfl
    rw [hpow, Matrix.diagonal_eq_zero] at hDsq
    intro i
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp (congrFun hDsq i))
  -- Hence `D = 1`, so `shearMatrix = P * 1 * P⁻¹ = 1`, contradicting `shearMatrix ≠ 1`.
  have hD1 : D = 1 := by
    rw [hDdef, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdi i
  refine shearMatrix_ne_one ?_
  rw [hM, hD1, Matrix.mul_one, hPP]

end AxQM.Concrete
