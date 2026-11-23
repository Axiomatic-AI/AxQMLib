/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthConjugation
import AxQM.Concrete.AxisAngleGateValues
import AxQM.Concrete.Hadamard
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.PauliOuterProduct

/-!
# Concrete: the algebra behind the fault-tolerant π/8-gate circuit (Nielsen & Chuang, Ex. 10.66)

Nielsen & Chuang **Exercise 10.66** ("Fault-tolerant π/8 gate construction", p. 487) asks to
*derive* the circuit of Figure 10.25 — a measurement-based gadget implementing the `T = π/8` gate —
starting from the trivial "swap `|ψ⟩` into a known `|0⟩`, then apply `T`" circuit and pushing the
final `T` leftward through the swap gadget using two commutation relations. This file formalises the
`2 × 2` / `4 × 4` complex-matrix **algebra** those two relations encode, together with the resulting
circuit's correctness.

## The two relations, read critically

The exercise instructs the reader to "use the relations `TX = exp(−iπ/4) SX` and `TU = UT`".

* The **printed relation `TX = exp(−iπ/4) SX`** (a bare matrix product) is *false*: `TX` has
  top-right entry `1`, while `exp(−iπ/4) SX` has top-right entry `exp(−iπ/4) = (1−i)/√2 ≠ 1`
  (`tMatrix_mul_pauliX_ne_expNeg_smul_sxMatrix`). What is true — and what the main text states
  correctly on p. 486 (`THZHT† = TXT† = e^{−iπ/4}SX`) — is the **conjugation**
  `T X T† = exp(−iπ/4) SX` (`tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix`). In circuit terms this is
  the leftward-move rule `T X = exp(−iπ/4) SX · T`
  (`tMatrix_mul_pauliX_eq_expNeg_smul_sxMatrix_mul`): pushing `T` to the *left* of the
  classically-controlled `X` turns the correction into `SX` (the scalar `exp(−iπ/4)` is an
  irrelevant global phase) and leaves a `T` behind.
* The **relation `TU = UT`** (`U` the CNOT, `T` on the *control* qubit) is true: `T ⊗ I` and the
  CNOT are both diagonal in the control's computational basis, hence commute
  (`tCtrl_mul_cnotMatrix_comm`). This pushes `T` further left, through the CNOT.

Once `T` has moved all the way left it lands on the ancilla-preparation `H|0⟩`, and
`T H |0⟩ = |Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` (`tMatrix_mulVec_hadamardC_mulVec_ket_zero`, eq. 10.118) —
exactly the ancilla in the dotted box of Fig. 10.25. This *is* the derivation.

## Correctness of the derived circuit

`piEighthCircuitOut` is the two-qubit state after the Fig. 10.25 CNOT (control = ancilla `|Θ⟩`,
target = data `|ψ⟩ = a|0⟩ + b|1⟩`), eq. 10.119. Measuring the data qubit leaves the ancilla wire
holding `T|ψ⟩` up to a nonzero scalar in *either* outcome:

* outcome `0` — directly, `∝ T|ψ⟩` (`piEighthCircuitOut_measure_zero`);
* outcome `1` — after the classically-controlled correction `SX`, `∝ T|ψ⟩`
  (`piEighthCircuitOut_measure_one`; here `SX = e^{−iπ/4} T X T†` of eq. 10.120).

So the derived gadget implements the π/8 gate, as N&C claims.

Every statement is an equality (or disequality) of concrete complex matrices / column vectors.
The statement of the exercise is in `AxQM/NC/Ch10/Exercise10_66_FTpi8.lean`. The file builds on the
π/8 gate `tMatrix`
and its conjugation lemma
`tMatrix_conj_pauliX` (`AxQM/Concrete/PiEighthConjugation.lean`), the phase gate `sMatrix`, Hadamard
`hadamardC`, CNOT `cnotMatrix`, the kets `ket`, and the `1/√2` bridges `invSqrt2`,
`exp_(neg_)pi_div_four_mul_I`.
-/

open Matrix Complex

noncomputable section

namespace AxQM.Concrete

/-- `e^{-iπ/4} = (1 - i)/√2`, in the `-(π/4 : ℝ) * I` argument form used throughout the π/8-gate
circuit relations below; bridges the shared numeric fact `exp_neg_pi_div_four_mul_I` (stated with
argument `-(I * (π/4))`) to this file's convention. -/
theorem exp_neg_pi_div_four_mul_I_ofReal :
    Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) = invSqrt2 - invSqrt2 * Complex.I := by
  rw [← exp_neg_pi_div_four_mul_I]; congr 1; push_cast; ring

/-- The single-qubit gate `SX = S · X = !![0, 1; i, 0]` (Nielsen & Chuang, eq. 10.120): the phase
gate `S = diag(1, i)` composed with the bit-flip `X`. It is the classically-controlled correction
applied in Fig. 10.25 when the measurement yields `1`, and equals `e^{iπ/4} T X T†` (`M` of
Exercise 10.71). -/
def sxMatrix : Matrix (Fin 2) (Fin 2) ℂ := sMatrix * pauliX

/-- `SX = !![0, 1; i, 0]` as an explicit matrix (from `S = diag(1, i)`, `X = !![0,1;1,0]`). -/
theorem sxMatrix_eq : sxMatrix = !![0, 1; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sxMatrix, sMatrix, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The π/8 gate conjugates `X` to `exp(−iπ/4) SX`** (Nielsen & Chuang, main text p. 486,
`TXT† = e^{−iπ/4}SX`): `T X T† = exp(−iπ/4) • SX`. This is the *correct* form of the relation
Exercise 10.66 prints as "`TX = exp(−iπ/4)SX`". Proved from `tMatrix_conj_pauliX`
(`T X T† = (X + Y)/√2`) by matching `(X + Y)/√2` with `exp(−iπ/4) • SX` entrywise, using
`exp(−iπ/4) = (1 − i)/√2`. -/
theorem tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix :
    tMatrix * pauliX * tMatrixᴴ = Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix := by
  rw [tMatrix_conj_pauliX, exp_neg_pi_div_four_mul_I_ofReal, sxMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, Matrix.smul_apply, Complex.ext_iff]
  ring

/-- **The leftward-move rule** used in the circuit derivation: `T X = exp(−iπ/4) • (SX · T)`.
Pushing `T` to the *left* of the classically-controlled `X` (of the swap gadget) turns the `X`
correction
into `SX`, up to the global phase `exp(−iπ/4)`, and leaves a `T`. Obtained from the conjugation form
`tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix` by right-multiplying by `T` and using `T† T = 1`. -/
theorem tMatrix_mul_pauliX_eq_expNeg_smul_sxMatrix_mul :
    tMatrix * pauliX
      = Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • (sxMatrix * tMatrix) := by
  have hunit : tMatrixᴴ * tMatrix = 1 := Matrix.mem_unitaryGroup_iff'.mp tMatrix_mem_unitaryGroup
  calc tMatrix * pauliX
      = tMatrix * pauliX * (tMatrixᴴ * tMatrix) := by rw [hunit, Matrix.mul_one]
    _ = (tMatrix * pauliX * tMatrixᴴ) * tMatrix := by rw [← Matrix.mul_assoc]
    _ = (Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix) * tMatrix := by
          rw [tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix]
    _ = Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • (sxMatrix * tMatrix) := by
          rw [Matrix.smul_mul]

/-- **The printed relation of Exercise 10.66 is false.** As a bare matrix product,
`T X ≠ exp(−iπ/4) SX`: the `(0,1)` entries are `1` and `exp(−iπ/4) = (1 − i)/√2 ≠ 1` respectively.
The exercise's `TX = exp(−iπ/4)SX` must be read as the conjugation `T X T† = exp(−iπ/4) SX`
(`tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix`), the form used in the main-text derivation. -/
theorem tMatrix_mul_pauliX_ne_expNeg_smul_sxMatrix :
    tMatrix * pauliX ≠ Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix := by
  -- The `(0,1)` entries are `1` and `(1 − i)/√2`, whose imaginary parts `0` and `−1/√2` differ.
  have hlhs : (tMatrix * pauliX) 0 1 = 1 := by
    simp [tMatrix, pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  have hrhs : (Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • sxMatrix) 0 1
      = invSqrt2 - invSqrt2 * Complex.I := by
    rw [exp_neg_pi_div_four_mul_I_ofReal, sxMatrix_eq]; simp
  intro h
  have key : (1 : ℂ) = invSqrt2 - invSqrt2 * Complex.I := by rw [← hlhs, h, hrhs]
  have him : (Real.sqrt 2)⁻¹ = 0 := by
    have h := congrArg Complex.im key
    simpa [invSqrt2] using h.symm
  exact (Real.sqrt_pos.mpr (by norm_num)).ne' (inv_eq_zero.mp him)

/-- `T` acting on the **control** qubit of a two-qubit register: the `4 × 4` matrix `T ⊗ I` in the
big-endian order `|q₀q₁⟩ ↔ 2q₀ + q₁` matching `cnotMatrix` (control = first/high qubit `q₀`). Since
`I` acts trivially and `T = diag(1, e^{iπ/4})`, this is the diagonal matrix
`diag(1, 1, e^{iπ/4}, e^{iπ/4})` — the diagonal entry on index `k` is `T` evaluated on the control
bit of `k`. -/
def tCtrl : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, 1, tMatrix 1 1, tMatrix 1 1]

/-- **The relation `TU = UT`** of Exercise 10.66 (`U` = CNOT, `T` on the control): `T ⊗ I` commutes
with the CNOT, `tCtrl · CNOT = CNOT · tCtrl`. Both are functions of the control bit only in the
control's basis — `tCtrl` is diagonal and the CNOT permutes only the two indices `2, 3` (control =
`1`), on which `tCtrl` has the *equal* diagonal entries `e^{iπ/4}` — so they commute. This is the
move that pushes `T` through the CNOT of the swap gadget onto the ancilla wire. -/
theorem tCtrl_mul_cnotMatrix_comm : tCtrl * cnotMatrix = cnotMatrix * tCtrl := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tCtrl, cnotMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
      Matrix.of_apply, Equiv.swap_apply_def]

/-- The nontrivial diagonal entry `T₁₁ = e^{iπ/4}` **squares to `i`**: `T₁₁ · T₁₁ = i`. Since
`T₁₁ = (1 + i)/√2` (`tMatrix_apply_one_one`), `T₁₁² = (1 + i)²/2 = 2i/2 = i`. This is precisely the
fact that lets the classically-controlled `SX` correction of Fig. 10.25 recover the π/8 phase in the
`−1` measurement branch (`piEighthCircuitOut_measure_one`). -/
theorem tMatrix_apply_one_one_mul_self : tMatrix 1 1 * tMatrix 1 1 = Complex.I := by
  rw [tMatrix_apply_one_one]
  have hexpand : (invSqrt2 + invSqrt2 * Complex.I) * (invSqrt2 + invSqrt2 * Complex.I)
      = invSqrt2 * invSqrt2 * (1 + Complex.I * Complex.I)
        + invSqrt2 * invSqrt2 * 2 * Complex.I := by ring
  rw [hexpand, invSqrt2_mul_self, Complex.I_mul_I]; ring

/-- The π/8 gate acting on a general qubit column vector: `T (a|0⟩ + b|1⟩) = a|0⟩ + e^{iπ/4} b|1⟩`,
i.e. `T *ᵥ ![a, b] = ![a, T₁₁ * b]` with `T₁₁ = e^{iπ/4}` (`tMatrix_apply_one_one`) — the `|0⟩`
amplitude is fixed and the `|1⟩` amplitude picks up the diagonal phase. -/
theorem tMatrix_mulVec_pair (a b : ℂ) : tMatrix *ᵥ ![a, b] = ![a, tMatrix 1 1 * b] := by
  ext i
  fin_cases i <;> simp [tMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The ancilla state `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` of Fig. 10.25 (Nielsen & Chuang, eq. 10.118),
as a column vector `Fin 2 → ℂ`; here `T₁₁ = e^{iπ/4}` is the nontrivial diagonal entry of `T`
(`tMatrix_apply_one_one`). It is the `+1` eigenstate of `e^{−iπ/4}SX` that the fault-tolerant π/8
gate consumes. -/
def thetaVec : Fin 2 → ℂ := ![invSqrt2, invSqrt2 * tMatrix 1 1]

/-- **The moved-left `T` reconstructs the Fig. 10.25 ancilla**: applying a Hadamard then a `T` to
`|0⟩` gives `|Θ⟩`, i.e. `T (H |0⟩) = |Θ⟩` (Nielsen & Chuang, p. 486: "`|Θ⟩` may be produced by
applying a Hadamard gate and then a π/8 gate to the state `|0⟩`"). `H|0⟩ = (|0⟩+|1⟩)/√2` and `T`
multiplies the `|1⟩` amplitude by `e^{iπ/4} = T₁₁`. -/
theorem tMatrix_mulVec_hadamardC_mulVec_ket_zero :
    tMatrix *ᵥ (hadamardC *ᵥ ket 0) = thetaVec := by
  have hH : hadamardC *ᵥ ket 0 = ![invSqrt2, invSqrt2] := by
    ext i
    fin_cases i <;>
      simp [hadamardC, ket, Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.single_apply, invSqrt2]
  rw [hH, tMatrix_mulVec_pair]
  ext i
  fin_cases i <;> simp [thetaVec, mul_comm]

/-- The big-endian tensor product `u ⊗ v` of two single-qubit column vectors, as a `Fin 4 → ℂ`
vector with index `2i + j ↦ uᵢ vⱼ` (order `00, 01, 10, 11`) — the convention under which
`cnotMatrix` has its first qubit as control. -/
def kron2 (u v : Fin 2 → ℂ) : Fin 4 → ℂ := ![u 0 * v 0, u 0 * v 1, u 1 * v 0, u 1 * v 1]

/-- The two-qubit state **after the Fig. 10.25 controlled-NOT** (Nielsen & Chuang, eq. 10.119),
`CNOT (|Θ⟩ ⊗ |ψ⟩)`, with the ancilla `|Θ⟩` as control (first qubit) and the data
`|ψ⟩ = a|0⟩ + b|1⟩` as target (second qubit). Measuring the *data* qubit next leaves the ancilla
wire holding the π/8-rotated state (`piEighthCircuitOut_measure_zero` / `_measure_one`). -/
def piEighthCircuitOut (a b : ℂ) : Fin 4 → ℂ := cnotMatrix *ᵥ kron2 thetaVec ![a, b]

/-- **Fig. 10.25, measurement outcome `0`.** When the data qubit is measured `0`, the (unnormalised)
ancilla-wire component is `(1/√2) • T|ψ⟩` — already the π/8-rotated state, so no correction is
needed. The ancilla amplitudes for data `= 0` sit at indices `0, 2` of `piEighthCircuitOut`. -/
theorem piEighthCircuitOut_measure_zero (a b : ℂ) :
    ![piEighthCircuitOut a b 0, piEighthCircuitOut a b 2] = invSqrt2 • (tMatrix *ᵥ ![a, b]) := by
  rw [tMatrix_mulVec_pair]
  ext i
  fin_cases i <;>
    simp [piEighthCircuitOut, kron2, thetaVec, cnotMatrix, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Equiv.swap_apply_def, Pi.smul_apply]
  ring

/-- **Fig. 10.25, measurement outcome `1`.** When the data qubit is measured `1`, applying the
classically-controlled correction `SX` to the ancilla-wire component gives `(e^{iπ/4}/√2) • T|ψ⟩` —
the π/8-rotated state up to the nonzero scalar `e^{iπ/4}/√2`, which differs from outcome `0`'s
scalar `1/√2` only by the physically-irrelevant global phase `e^{iπ/4}` (so both branches leave the
ancilla wire in the *same physical state* `T|ψ⟩`). The ancilla amplitudes for data `= 1` sit at
indices `1, 3` of `piEighthCircuitOut`. -/
theorem piEighthCircuitOut_measure_one (a b : ℂ) :
    sxMatrix *ᵥ ![piEighthCircuitOut a b 1, piEighthCircuitOut a b 3]
      = (invSqrt2 * tMatrix 1 1) • (tMatrix *ᵥ ![a, b]) := by
  rw [tMatrix_mulVec_pair]
  have ht : tMatrix 1 1 * tMatrix 1 1 = Complex.I := tMatrix_apply_one_one_mul_self
  ext i
  fin_cases i
  · simp [sxMatrix, sMatrix, pauliX, piEighthCircuitOut, kron2, thetaVec, cnotMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Equiv.swap_apply_def,
      Pi.smul_apply]
  · simp [sxMatrix, sMatrix, pauliX, piEighthCircuitOut, kron2, thetaVec, cnotMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Equiv.swap_apply_def,
      Pi.smul_apply]
    linear_combination (-(invSqrt2 * b)) * ht

end AxQM.Concrete
