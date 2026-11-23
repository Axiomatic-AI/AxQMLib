/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation

/-!
# Concrete: the π/8 (T) gate and its relation to `R_z(π/4)` (Nielsen & Chuang, §4.2)

Nielsen & Chuang's **π/8 gate** (denoted `T`) is the diagonal single-qubit gate
`T = !![1, 0; 0, exp(iπ/4)]`  (eq. 4.2).
It is called the "π/8 gate" because, pulling out a global phase `exp(iπ/8)`, it equals a gate with
`exp(±iπ/8)` on the diagonal (eq. 4.3):
`T = exp(iπ/8) !![exp(-iπ/8), 0; 0, exp(iπ/8)] = exp(iπ/8) R_z(π/4)`,
since `R_z(θ) = !![exp(-iθ/2), 0; 0, exp(iθ/2)]` (eq. 4.6, `Concrete.rotZ_eq`) evaluated at
`θ = π/4` has `θ/2 = π/8`.

This is the pure `2 × 2` complex-matrix content of **Exercise 4.3** (`T = R_z(π/4)` up to a global
phase). The physics reading — that `T` and `R_z(π/4)` are the *same qubit gate* up to the
unobservable global phase — is in `AxQM/Postulates/API/PiEighthGate.lean`.

## What is formalized

* `tMatrix` — the T gate matrix `!![1, 0; 0, exp(iπ/4)]` (eq. 4.2).
* `tMatrix_eq_expPiDivEight_smul_rotZ` — **the identity of Exercise 4.3**:
  `T = exp(iπ/8) • R_z(π/4)` (eq. 4.3).
* `tMatrix_mem_unitaryGroup` — `T` is unitary.
-/

open scoped Matrix

noncomputable section

namespace AxQM.Concrete

/-- The **π/8 (T) gate** `T = !![1, 0; 0, exp(iπ/4)]` (Nielsen & Chuang, eq. 4.2), a diagonal
single-qubit gate. Historically called the "π/8 gate" because of the global-phase form
`T = exp(iπ/8) R_z(π/4)` (`tMatrix_eq_expPiDivEight_smul_rotZ`). -/
def tMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)]

/-- **The identity of Nielsen & Chuang Exercise 4.3** (eq. 4.3): the π/8 gate equals `R_z(π/4)` up
to the global phase `exp(iπ/8)`, i.e. `T = exp(iπ/8) • R_z(π/4)`. Both are diagonal, and pulling the
scalar `exp(iπ/8)` through `R_z(π/4) = diag(exp(-iπ/8), exp(iπ/8))` gives `diag(1, exp(iπ/4)) = T`
via `exp(iπ/8)·exp(-iπ/8) = 1` and `exp(iπ/8)·exp(iπ/8) = exp(iπ/4)`. -/
theorem tMatrix_eq_expPiDivEight_smul_rotZ :
    tMatrix = Complex.exp ((Real.pi / 8 : ℝ) * Complex.I) • rotZ (Real.pi / 4) := by
  rw [rotZ_eq]
  unfold tMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.smul_apply,
      smul_eq_mul, neg_mul, mul_zero, Complex.ofReal_div, Complex.ofReal_ofNat]
  · -- (0,0): `1 = exp(iπ/8) · exp(-i(π/4)/2)`
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  · -- (1,1): `exp(iπ/4) = exp(iπ/8) · exp(i(π/4)/2)`
    rw [← Complex.exp_add]
    congr 1
    ring

/-- The π/8 gate `T` is unitary: it lies in the `2 × 2` unitary group. Immediate from the global
phase identity `T = exp(iπ/8) • R_z(π/4)` (`tMatrix_eq_expPiDivEight_smul_rotZ`), the unitarity of
`R_z(π/4)` (`rotZ_mem_unitaryGroup`), and the fact that scaling a unitary by the unit-modulus phase
`exp(iπ/8)` keeps it unitary (`exp(iπ/8) · conj(exp(iπ/8)) = 1`). -/
theorem tMatrix_mem_unitaryGroup : tMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hc : Complex.exp ((Real.pi / 8 : ℝ) * Complex.I) *
      star (Complex.exp ((Real.pi / 8 : ℝ) * Complex.I)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]; norm_num
  rw [tMatrix_eq_expPiDivEight_smul_rotZ, Matrix.mem_unitaryGroup_iff, star_smul,
    smul_mul_smul_comm, Matrix.mem_unitaryGroup_iff.mp (rotZ_mem_unitaryGroup _), hc, one_smul]

end AxQM.Concrete
