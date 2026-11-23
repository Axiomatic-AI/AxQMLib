/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthGateCircuit
import AxQM.Concrete.Pauli

/-!
# Concrete: the observable `M = e^{-iπ/4}SX` and its transversal correction `ZSX`

Nielsen & Chuang **Exercise 10.71** ("Fault-tolerant measurement of `M = e^{-iπ/4}SX`", §10.6.3,
p. 491) asks to *verify* that the fault-tolerant measurement procedure of Fig. 10.28 — specialised
to the observable `M = e^{-iπ/4}SX` by the "slight modification" of p. 491 — is a correct method for
measuring `M`. This file formalises the `2 × 2` complex-matrix **algebra** the verification rests
on; the physical statement (`M` as an `Observable`, its `±1` eigenstates, and the standard
measurement circuit) is in `AxQM/NC/Ch10/Exercise10_71.lean`.

## The object measured, and why the procedure is modified

`M = e^{-iπ/4}SX` (with `SX = S·X = !![0,1;i,0]`, `Concrete.sxMatrix` of Exercise 10.66) is a
**genuine `±1` observable**: it is Hermitian (`mMatrix_conjTranspose`) and squares to the identity
(`mMatrix_mul_self`), hence unitary (`mMatrix_mem_unitaryGroup`) with eigenvalues `±1`. It coincides
with the conjugation `T X T†` of Exercise 10.66's main-text relation
(`mMatrix_eq_tMatrix_conj_pauliX`), so its `+1` eigenstate is exactly the ancilla
`|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` produced by the fault-tolerant π/8 gate (`thetaVec`,
`mMatrix_mulVec_thetaVec`); its `-1` eigenstate is `|Θ⁻⟩ = (|0⟩ − e^{iπ/4}|1⟩)/√2`
(`thetaMinusVec`, `mMatrix_mulVec_thetaMinusVec`).

The generic fault-tolerant measurement (Fig. 10.28) applies a controlled-`M̄` between a cat-state
ancilla and the encoded data via a *transversal* (bitwise) implementation of `M`. For the Steane
code the transversal Clifford part of `M` is the **per-qubit gate `ZSX`** (`zsxMatrix`; N&C uses
`M' = ZS` for logical `S̄` because `S^{⊗7}` alone is *not* logical `S̄`, and `X^{⊗7}` for logical
`X̄`). The remaining non-Clifford scalar `e^{-iπ/4}` of `M` cannot be folded into the transversal
gate — in a *controlled* operation it is a **relative** phase between the two cat branches — so N&C
supplies it separately by seven `T` gates on the ancilla qubits: on the all-ones branch these
contribute `(T₁₁)^7 = (e^{iπ/4})^7 = e^{-iπ/4}` (`tMatrix_one_one_pow_seven`), exactly `M`'s phase.

Every statement here is an equality of concrete `2 × 2` complex matrices
or `Fin 2 → ℂ` vectors (or a `Matrix.unitaryGroup` membership). It reuses `sxMatrix`, `tMatrix`,
`tMatrix_apply_one_one`, `tMatrix_apply_one_one_mul_self`, `thetaVec` and
`exp_neg_pi_div_four_mul_I_ofReal` from `PiEighthGateCircuit` (Exercise 10.66), and `pauliZ`,
`invSqrt2`, `invSqrt2_mul_self`.
-/

open Matrix Complex

noncomputable section

namespace AxQM.Concrete

/-- The single-qubit observable `M = e^{-iπ/4}·SX` of Nielsen & Chuang Exercise 10.71, with
`SX = Concrete.sxMatrix = !![0,1;i,0]`. It is the observable whose fault-tolerant measurement
creates the ancilla for the π/8 gate. -/
def mMatrix : Matrix (Fin 2) (Fin 2) ℂ := Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix

/-- `M = !![0, (1−i)/√2; (1+i)/√2, 0]` as an explicit matrix: from `e^{-iπ/4} = (1−i)/√2`
(`invSqrt2 − invSqrt2·i`) and `SX = !![0,1;i,0]`, the top-right entry is `e^{-iπ/4}·1` and the
bottom-left is `e^{-iπ/4}·i = invSqrt2 + invSqrt2·i` (using `i² = −1`). -/
theorem mMatrix_eq :
    mMatrix = !![0, invSqrt2 - invSqrt2 * Complex.I; invSqrt2 + invSqrt2 * Complex.I, 0] := by
  have h2 := Complex.I_mul_I
  rw [mMatrix, exp_neg_pi_div_four_mul_I_ofReal, sxMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  linear_combination (-invSqrt2) * h2

/-- **`M = T X T†`** (Nielsen & Chuang, main-text relation of p. 486, cf. Exercise 10.66): the
observable `M = e^{-iπ/4}SX` is the π/8-conjugate of `X`. Immediate from
`tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix` (`T X T† = e^{-iπ/4}·SX`) since `M` is by definition
`e^{-iπ/4}·SX`. -/
theorem mMatrix_eq_tMatrix_conj_pauliX : mMatrix = tMatrix * pauliX * tMatrixᴴ := by
  rw [mMatrix, ← tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix]

/-- **`M` is Hermitian**: `M† = M`. The diagonal is zero and the off-diagonal entries `(1∓i)/√2`
are complex conjugates of one another (with `invSqrt2` real), so the conjugate transpose returns
`M`. This makes `M` a legitimate observable. -/
theorem mMatrix_conjTranspose : mMatrixᴴ = mMatrix := by
  rw [mMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, invSqrt2, Complex.ext_iff]

/-- `M` is a Hermitian matrix (`Matrix.IsHermitian`), packaging `mMatrix_conjTranspose`. -/
theorem mMatrix_isHermitian : mMatrix.IsHermitian := mMatrix_conjTranspose

/-- **`M` is an involution**: `M² = 1`, so `M` has eigenvalues `±1`. The off-diagonal entries
multiply as `((1−i)/√2)·((1+i)/√2) = (1 − i²)/2 = 1`, giving the identity. Together with
`mMatrix_conjTranspose` this shows `M` is a self-adjoint unitary — a `±1`-valued observable. -/
theorem mMatrix_mul_self : mMatrix * mMatrix = 1 := by
  have h1 := invSqrt2_mul_self
  have h2 := Complex.I_mul_I
  rw [mMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination (1 - Complex.I * Complex.I) * h1 - (2⁻¹ : ℂ) * h2

/-- **`M` is unitary** (`M ∈ U(2)`): from `M† = M` (`mMatrix_conjTranspose`) and `M² = 1`
(`mMatrix_mul_self`), `M† M = M M = 1`. The unitarity witness needed to package `M` as an
`Evolution qubit` in `AxQM/NC/Ch10/Exercise10_71.lean`. -/
theorem mMatrix_mem_unitaryGroup : mMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [Matrix.star_eq_conjTranspose, mMatrix_conjTranspose]; exact mMatrix_mul_self)

/-- **The `+1` eigenvector of `M` is `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2`** (`thetaVec` of
Exercise 10.66): `M |Θ⟩ = |Θ⟩`. The scalar `e^{-iπ/4}` cancels the `e^{iπ/4}` of `|Θ⟩`'s `|1⟩`
amplitude; concretely `(1∓i)/√2` and `T₁₁ = (1+i)/√2` combine via `invSqrt2² = ½` and `i² = −1`.
This is the ancilla the fault-tolerant π/8 gate consumes, now identified as `M`'s `+1`
eigenstate. -/
theorem mMatrix_mulVec_thetaVec : mMatrix *ᵥ thetaVec = thetaVec := by
  have h1 := invSqrt2_mul_self
  have h2 := Complex.I_mul_I
  rw [mMatrix_eq]
  ext i
  fin_cases i
  · simp [thetaVec, tMatrix_apply_one_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (2 * invSqrt2) * h1 - invSqrt2 ^ 3 * h2
  · simp [thetaVec, tMatrix_apply_one_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The `-1` eigenvector `|Θ⁻⟩ = (|0⟩ − e^{iπ/4}|1⟩)/√2` of `M`, as a column vector `Fin 2 → ℂ`;
the `|1⟩` amplitude is the negation of `|Θ⟩`'s (`thetaVec`). `T₁₁ = e^{iπ/4}` is the nontrivial
diagonal entry of the π/8 gate (`tMatrix_apply_one_one`). -/
def thetaMinusVec : Fin 2 → ℂ := ![invSqrt2, -(invSqrt2 * tMatrix 1 1)]

/-- **The `-1` eigenvector of `M`**: `M |Θ⁻⟩ = −|Θ⁻⟩`. Same computation as `mMatrix_mulVec_thetaVec`
with the `|1⟩` amplitude negated; confirms `M` has spectrum `{+1, −1}`. -/
theorem mMatrix_mulVec_thetaMinusVec : mMatrix *ᵥ thetaMinusVec = -thetaMinusVec := by
  have h1 := invSqrt2_mul_self
  have h2 := Complex.I_mul_I
  rw [mMatrix_eq]
  ext i
  fin_cases i
  · simp [thetaMinusVec, tMatrix_apply_one_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (2 * invSqrt2) * h1 - invSqrt2 ^ 3 * h2
  · simp [thetaMinusVec, tMatrix_apply_one_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- **The nontrivial diagonal entry of `T` has unit modulus**: `‖T₁₁‖ = 1` (with
`T₁₁ = e^{iπ/4}`). From `T₁₁² = i` (`tMatrix_apply_one_one_mul_self`), `‖T₁₁‖² = ‖T₁₁²‖ = ‖i‖ = 1`,
so `‖T₁₁‖ = 1`. Used to normalize the eigenstates `|Θ⟩`, `|Θ⁻⟩` of `M` in
`AxQM/NC/Ch10/Exercise10_71.lean`. -/
theorem norm_tMatrix_one_one : ‖tMatrix 1 1‖ = 1 := by
  have h : ‖tMatrix 1 1‖ * ‖tMatrix 1 1‖ = 1 := by
    rw [← norm_mul, tMatrix_apply_one_one_mul_self, Complex.norm_I]
  nlinarith [norm_nonneg (tMatrix 1 1), h]

/-- The **transversal correction gate `ZSX = Z·S·X`** used per qubit in the Exercise 10.71
procedure, defined as `pauliZ · sxMatrix` (with `sxMatrix = S·X`). Applying `ZSX` bitwise to the
seven Steane-code qubits is the Clifford part of the encoded `M`: `X^{⊗7}` is logical `X̄` and
`(ZS)^{⊗7}` is logical `S̄` (N&C p. 490, `M' = ZS` for `M = S`). -/
def zsxMatrix : Matrix (Fin 2) (Fin 2) ℂ := pauliZ * sxMatrix

/-- `ZSX = !![0,1;−i,0]`: from `Z = diag(1,−1)` and `SX = !![0,1;i,0]`, the `Z` flips the sign of
the bottom row of `SX`. It differs from `SX` only in the sign of the `(1,0)` entry — the `Z`
correction that upgrades transversal `S` to logical `S̄` on the Steane code. -/
theorem zsxMatrix_eq : zsxMatrix = !![0, 1; -Complex.I, 0] := by
  rw [zsxMatrix, sxMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **`ZSX` is unitary** (`ZSX ∈ U(2)`): the columns `(0,−i)` and `(1,0)` are orthonormal, so
`(ZSX)† (ZSX) = 1` (the off-diagonal `(1,0)` entry `i·(−i) = 1` in the product). Unlike `M`, `ZSX`
is *not* self-adjoint (`(ZSX)† = !![0,i;1,0] ≠ ZSX`); it is the per-qubit *correction gate* applied
by the transversal controlled-`ZSX`, not an observable. The unitarity witness needed to package
`ZSX` as an `Evolution qubit` in `AxQM/NC/Ch10/Exercise10_71.lean`. -/
theorem zsxMatrix_mem_unitaryGroup : zsxMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, zsxMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- **The seven ancilla `T` gates supply `M`'s phase**: `(T₁₁)^7 = e^{-iπ/4}`, where
`T₁₁ = e^{iπ/4}` is the nontrivial diagonal entry of the π/8 gate. On the all-ones branch of the
cat state each of the seven ancilla `T` gates contributes `T₁₁`, so their product is
`(e^{iπ/4})^7 = e^{i7π/4} = e^{-iπ/4}` — exactly the scalar of `M = e^{-iπ/4}SX`. This is the
"slight modification" of N&C p. 491: the non-Clifford phase is applied *once, to the ancilla* (a
controlled
relative phase), not folded into the per-qubit correction. Proved from `T₁₁² = i`
(`tMatrix_apply_one_one_mul_self`): `T₁₁^7 = (T₁₁²)³ · T₁₁ = i³ · T₁₁ = −i·(1+i)/√2 = (1−i)/√2`. -/
theorem tMatrix_one_one_pow_seven :
    (tMatrix 1 1) ^ 7 = Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) := by
  have hrw : (tMatrix 1 1) ^ 7 = (tMatrix 1 1 * tMatrix 1 1) ^ 3 * tMatrix 1 1 := by ring
  rw [exp_neg_pi_div_four_mul_I_ofReal, hrw, tMatrix_apply_one_one_mul_self, tMatrix_apply_one_one]
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, pow_two, Complex.I_mul_I]; ring
  rw [hI3]
  linear_combination (-invSqrt2) * Complex.I_mul_I

/-- **`M`'s scalar is the seven-`T` product**: `M = (T₁₁)^7 • SX`. Rewriting `M = e^{-iπ/4}·SX` with
`(T₁₁)^7 = e^{-iπ/4}` (`tMatrix_one_one_pow_seven`), the scalar `e^{-iπ/4}` of `M` is exactly the
phase the seven ancilla `T` gates contribute on the all-ones cat branch. Together with `zsxMatrix`
(the transversal Clifford part) this records both halves of the "slight modification" of N&C p. 491
at the matrix level: the per-qubit correction is `ZSX`, and the seven `T`s supply `M`'s scalar. -/
theorem mMatrix_eq_tMatrix_one_one_pow_seven_smul_sxMatrix :
    mMatrix = (tMatrix 1 1) ^ 7 • sxMatrix := by
  rw [mMatrix, tMatrix_one_one_pow_seven]

end AxQM.Concrete
