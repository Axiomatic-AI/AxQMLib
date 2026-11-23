/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthGate
import AxQM.Concrete.Pauli
import AxQM.Concrete.NMRPulsePhases

/-!
# Concrete: conjugation of the Pauli matrices by the π/8 (T) gate (Nielsen & Chuang, eq. 10.92)

This file verifies the first of the
identities of Nielsen & Chuang **Exercise 10.41**, namely equation (10.92) describing the action by
conjugation of the **π/8 gate** `T = diag(1, e^{iπ/4})` (`tMatrix`, N&C eq. 4.2) on the Pauli
matrices:

> `T Z T† = Z`;   `T X T† = (X + Y)/√2`.  (eq. 10.92)

Together with the Toffoli identities (10.93)–(10.95) these exhibit the π/8 and Toffoli gates as
lying *outside* the normalizer `N(Gₙ)` of the Pauli group (N&C §10.5.3): unlike Hadamard, phase and
CNOT, conjugating a Pauli operator by `T` does **not** return a Pauli operator — `T X T†` is the
non-Pauli combination `(X + Y)/√2`. This is exactly what makes stabilizer analysis of circuits
containing `T` or Toffoli gates inconvenient.

## What is proved

* `tMatrix_apply_one_one` / `tMatrix_eq` — the diagonal entry `T₁₁ = e^{iπ/4} = (1 + i)/√2` and the
  resulting explicit form `T = !![1, 0; 0, (1 + i)/√2]`, built on the shared numeric bridge
  `Concrete.exp_pi_div_four_mul_I` and the normalization constant `invSqrt2 = 1/√2`.
* `tMatrix_conj_pauliZ` — `T Z T† = Z` (eq. 10.92, first identity). Since `T` is diagonal it
  commutes with `Z`, so `T Z T† = Z (T T†) = Z` by unitarity of `T` (`tMatrix_mem_unitaryGroup`).
* `tMatrix_conj_pauliX` — `T X T† = (X + Y)/√2` (eq. 10.92, second identity), the non-Pauli image,
  a direct `2 × 2` entrywise computation using `e^{±iπ/4} = (1 ± i)/√2`.

The Toffoli-gate half of the exercise, equations (10.93)–(10.95), is formalized separately (it is a
`Fin 8` computation); the statements of Exercise 10.41 are in `AxQM/NC/Ch10/Exercise10_41.lean`.
-/

open Matrix Complex

namespace AxQM.Concrete

/-- The nontrivial diagonal `(1, 1)` entry of the π/8 gate is the `√2`-normalized phase
`T₁₁ = e^{iπ/4} = (1 + i)/√2`. Read off the definition of `tMatrix` and the shared numeric bridge
`Concrete.exp_pi_div_four_mul_I` (its argument rewritten to the `(π/4)·i` form of `tMatrix`). -/
theorem tMatrix_apply_one_one : tMatrix 1 1 = invSqrt2 + invSqrt2 * Complex.I := by
  rw [← exp_pi_div_four_mul_I]
  simp [tMatrix, mul_comm]

/-- The π/8 gate as an explicit `2 × 2` matrix with its diagonal entry evaluated:
`T = !![1, 0; 0, (1 + i)/√2]`, using the entry value `tMatrix_apply_one_one`. -/
theorem tMatrix_eq : tMatrix = !![1, 0; 0, invSqrt2 + invSqrt2 * Complex.I] := by
  rw [← tMatrix_apply_one_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMatrix]

/-- **π/8-gate conjugation fixes `Z`** (Nielsen & Chuang, eq. 10.92, first identity): `T Z T† = Z`.
As `T` is diagonal it commutes with the diagonal `Z`, so `T Z T† = Z (T T†) = Z` by the unitarity of
`T` (`tMatrix_mem_unitaryGroup`). -/
theorem tMatrix_conj_pauliZ : tMatrix * pauliZ * tMatrixᴴ = pauliZ := by
  have hcomm : tMatrix * pauliZ = pauliZ * tMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tMatrix, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  have hunit : tMatrix * tMatrixᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp tMatrix_mem_unitaryGroup
  rw [hcomm, Matrix.mul_assoc, hunit, Matrix.mul_one]

/-- **π/8-gate conjugation sends `X` to the non-Pauli combination `(X + Y)/√2`** (Nielsen & Chuang,
eq. 10.92, second identity): `T X T† = (X + Y)/√2`. A direct `2 × 2` computation: the off-diagonal
entries pick up `e^{±iπ/4} = (1 ± i)/√2`, matching `(X + Y)/√2` whose off-diagonal entries are
`(1 ∓ i)/√2`. This image is *not* a Pauli operator, witnessing that `T ∉ N(Gₙ)`. -/
theorem tMatrix_conj_pauliX :
    tMatrix * pauliX * tMatrixᴴ = invSqrt2 • (pauliX + pauliY) := by
  rw [tMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.smul_apply, invSqrt2, map_inv₀, Complex.conj_ofReal, Complex.conj_I] <;> ring

end AxQM.Concrete
