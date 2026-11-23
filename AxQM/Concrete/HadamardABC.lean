/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ABCDecomposition
import AxQM.Concrete.HadamardRotation

/-!
# Concrete: the ABC decomposition of the Hadamard gate (Nielsen & Chuang, Exercise 4.12)

Nielsen & Chuang, Exercise 4.12 asks to **give `A`, `B`, `C` and `α` for the Hadamard gate** in the
ABC decomposition of Corollary 4.2 (`U = e^{iα} A X B X C` with `A B C = I`). This file supplies the
explicit witnesses and verifies both defining relations at the matrix level.

The Z–Y decomposition of the Hadamard matrix (N&C eq. 4.12 with `cos(γ/2) = sin(γ/2) = (√2)⁻¹` and
the phases forcing `β = 0`, `γ = π/2`, `δ = π`, `α = π/2`) is `H = e^{iπ/2} R_z(0) R_y(π/2) R_z(π)`.
Feeding these angles into Corollary 4.2's witnesses `A = R_z(β) R_y(γ/2)`, `B = R_y(-γ/2)
R_z(-(δ+β)/2)`, `C = R_z((δ-β)/2)` and simplifying `R_z(0) = I` gives

`α = π/2`,  `A = R_y(π/4)`,  `B = R_y(-π/4) R_z(-π/2)`,  `C = R_z(π/2)`.

## What is formalised

* `hadamardWitnessA`, `hadamardWitnessB`, `hadamardWitnessC` — the explicit witnesses (the answer to
  "give `A`, `B`, `C`"), each a product of `§4.2` rotation matrices.
* `hadamardWitnessA_mul_B_mul_C_eq_one` — `A B C = I` (Corollary 4.2's first relation).
* `hadamardC_eq_expPiDivTwo_smul_rotY_mul_rotZ` — the Hadamard Z–Y decomposition
  `H = e^{iπ/2} • (R_y(π/2) R_z(π))` (the `β = 0` case).
* `hadamardABC_reassembly` — `A X B X C = R_y(π/2) R_z(π)` (Corollary 4.2's `X`-conjugation step,
  specialised).
* `hadamardC_eq_expPiDivTwo_smul_hadamardABC` — **Exercise 4.12 as a matrix identity**:
  `H = e^{iπ/2} • (A X B X C)`, the answer to "give `α`" (`α = π/2`) assembled with the witnesses.

## Design notes

* **These are the standard witnesses, not asserted.** Both relations are *proved*: `A B C = I` by
  the same `R_y`/`R_z` telescope as Corollary 4.2 (`rotY_mul_rotY`/`rotZ_mul_rotZ` and the zero
  angles collapse), and `A X B X C = R_y(π/2) R_z(π)` by the `X`-conjugation identities
  `pauliX_mul_rotY_mul_pauliX`/`pauliX_mul_rotZ_mul_pauliX` (Exercise 4.7) with `pauliX_mul_self`
  (`X² = I`). The exercise permits any correct answer; these are N&C's own witnesses (Corollary 4.2)
  for the Hadamard's Z–Y parameters.
* **The Z–Y decomposition of `H` is routed through Exercise 4.4.** Rather than recomputing an
  entrywise angle extraction, `hadamardC_eq_expPiDivTwo_smul_rotY_mul_rotZ` uses the already-proved
  `hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX` (`H = e^{iπ/2} R_x(π/2) R_z(π/2) R_x(π/2)`,
  Exercise 4.4) together with the shared closed form `(√2)⁻¹ • !![-i,-i;-i,i]`, which
  `R_y(π/2) R_z(π)` also realises (`rotY_mul_rotZ_piHalf_pi`).
* **Gate-level statement.** The operator identity for gates is in
  `AxQM/Postulates/API/HadamardABC.lean`, and the physics reading — that the Hadamard *gate* and
  the ABC gate product induce the same state channel — is in `AxQM/NC/Ch4/Exercise4_12.lean`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The Hadamard ABC witness `A = R_y(π/4)` (Nielsen & Chuang, Exercise 4.12). Corollary 4.2's
`A = R_z(β) R_y(γ/2)` with the Hadamard's Z–Y angles `β = 0`, `γ = π/2` (so `R_z(0) = I`). -/
noncomputable def hadamardWitnessA : Matrix (Fin 2) (Fin 2) ℂ := rotY (Real.pi / 4)

/-- The Hadamard ABC witness `B = R_y(-π/4) R_z(-π/2)` (Nielsen & Chuang, Exercise 4.12).
Corollary 4.2's `B = R_y(-γ/2) R_z(-(δ+β)/2)` with `β = 0`, `γ = π/2`, `δ = π`. -/
noncomputable def hadamardWitnessB : Matrix (Fin 2) (Fin 2) ℂ :=
  rotY (-(Real.pi / 4)) * rotZ (-(Real.pi / 2))

/-- The Hadamard ABC witness `C = R_z(π/2)` (Nielsen & Chuang, Exercise 4.12). Corollary 4.2's
`C = R_z((δ-β)/2)` with `β = 0`, `δ = π`. -/
noncomputable def hadamardWitnessC : Matrix (Fin 2) (Fin 2) ℂ := rotZ (Real.pi / 2)

/-- **Corollary 4.2's first relation for the Hadamard witnesses:** `A B C = I`. The inner `R_y`
collapse (`R_y(π/4) R_y(-π/4) = R_y(0) = I`) and the outer `R_z` telescope
(`R_z(-π/2) R_z(π/2) = R_z(0) = I`). -/
theorem hadamardWitnessA_mul_B_mul_C_eq_one :
    hadamardWitnessA * hadamardWitnessB * hadamardWitnessC = 1 := by
  unfold hadamardWitnessA hadamardWitnessB hadamardWitnessC
  calc rotY (Real.pi / 4) * (rotY (-(Real.pi / 4)) * rotZ (-(Real.pi / 2))) * rotZ (Real.pi / 2)
      = (rotY (Real.pi / 4) * rotY (-(Real.pi / 4)))
          * (rotZ (-(Real.pi / 2)) * rotZ (Real.pi / 2)) := by noncomm_ring
    _ = 1 := by
        rw [rotY_mul_rotY, rotZ_mul_rotZ, show Real.pi / 4 + -(Real.pi / 4) = 0 by ring,
          show -(Real.pi / 2) + Real.pi / 2 = 0 by ring, rotY_zero, rotZ_zero, mul_one]

/-- The closed form of the product `R_y(π/2) R_z(π) = (√2)⁻¹ • !![-i, -i; -i, i]` (` = -i H`), the
same matrix realised by the `X`–`Z`–`X` product of Exercise 4.4. Computed entrywise from
`rotY_eq`/`rotZ_eq` (`cos(π/4) = sin(π/4) = (√2)⁻¹`, `e^{∓iπ/2} = ∓i`). -/
theorem rotY_mul_rotZ_piHalf_pi :
    rotY (Real.pi / 2) * rotZ Real.pi
      = (Real.sqrt 2 : ℂ)⁻¹ • !![-Complex.I, -Complex.I; -Complex.I, Complex.I] := by
  have hs : (Real.sqrt 2 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [div_eq_iff (by positivity), inv_mul_eq_div, eq_div_iff (by positivity),
      Real.mul_self_sqrt (by norm_num)]
  have hc : Real.cos (Real.pi / 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four, hs]
  have hsin : Real.sin (Real.pi / 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four, hs]
  have hz1 : Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I) = -Complex.I := by
    rw [show -((Real.pi : ℂ) / 2) * Complex.I = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  have hz2 : Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) = Complex.I := by
    rw [show ((Real.pi : ℂ) / 2) * Complex.I = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  rw [rotY_eq, rotZ_eq]
  simp only [Matrix.mul_fin_two, hc, hsin, hz1, hz2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one,
      smul_eq_mul, Complex.ofReal_inv] <;> ring

/-- The **Z–Y decomposition of the Hadamard matrix** (the `β = 0` case, N&C eq. 4.12):
`H = e^{iπ/2} • (R_y(π/2) R_z(π))`. Both `R_y(π/2) R_z(π)` (`rotY_mul_rotZ_piHalf_pi`) and the
`X`–`Z`–`X` product of Exercise 4.4 equal the shared closed form `(√2)⁻¹ • !![-i,-i;-i,i]`, so this
reduces to `hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX`. -/
theorem hadamardC_eq_expPiDivTwo_smul_rotY_mul_rotZ :
    hadamardC = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I)
      • (rotY (Real.pi / 2) * rotZ Real.pi) := by
  rw [hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX, rotX_mul_rotZ_mul_rotX_pi_div_two,
    rotY_mul_rotZ_piHalf_pi]

/-- **Corollary 4.2's `X`-conjugation step for the Hadamard witnesses:**
`A X B X C = R_y(π/2) R_z(π)`.
Inserting `X X = I` inside `B` and applying `X R_a(θ) X = R_a(-θ)` (Exercise 4.7) turns `X B X` into
`R_y(π/4) R_z(π/2)`, after which the `R_y` and `R_z` factors combine via the group law. -/
theorem hadamardABC_reassembly :
    hadamardWitnessA * pauliX * hadamardWitnessB * pauliX * hadamardWitnessC
      = rotY (Real.pi / 2) * rotZ Real.pi := by
  have hXBX : pauliX * (rotY (-(Real.pi / 4)) * rotZ (-(Real.pi / 2))) * pauliX
      = rotY (Real.pi / 4) * rotZ (Real.pi / 2) := by
    calc pauliX * (rotY (-(Real.pi / 4)) * rotZ (-(Real.pi / 2))) * pauliX
        = pauliX * rotY (-(Real.pi / 4)) * (pauliX * pauliX)
            * rotZ (-(Real.pi / 2)) * pauliX := by rw [pauliX_mul_self]; noncomm_ring
      _ = (pauliX * rotY (-(Real.pi / 4)) * pauliX)
            * (pauliX * rotZ (-(Real.pi / 2)) * pauliX) := by noncomm_ring
      _ = rotY (Real.pi / 4) * rotZ (Real.pi / 2) := by
          rw [pauliX_mul_rotY_mul_pauliX, pauliX_mul_rotZ_mul_pauliX, neg_neg, neg_neg]
  unfold hadamardWitnessA hadamardWitnessB hadamardWitnessC
  calc rotY (Real.pi / 4) * pauliX * (rotY (-(Real.pi / 4)) * rotZ (-(Real.pi / 2)))
          * pauliX * rotZ (Real.pi / 2)
      = rotY (Real.pi / 4)
          * (pauliX * (rotY (-(Real.pi / 4)) * rotZ (-(Real.pi / 2))) * pauliX)
          * rotZ (Real.pi / 2) := by noncomm_ring
    _ = rotY (Real.pi / 4) * (rotY (Real.pi / 4) * rotZ (Real.pi / 2)) * rotZ (Real.pi / 2) := by
        rw [hXBX]
    _ = (rotY (Real.pi / 4) * rotY (Real.pi / 4)) * (rotZ (Real.pi / 2) * rotZ (Real.pi / 2)) := by
        noncomm_ring
    _ = rotY (Real.pi / 2) * rotZ Real.pi := by
        rw [rotY_mul_rotY, rotZ_mul_rotZ, show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring,
          show Real.pi / 2 + Real.pi / 2 = Real.pi by ring]

/-- **Nielsen & Chuang, Exercise 4.12 (matrix form).** The ABC decomposition of the Hadamard gate:
with `α = π/2`, `A = R_y(π/4)`, `B = R_y(-π/4) R_z(-π/2)`, `C = R_z(π/2)`,
`H = e^{iπ/2} • (A X B X C)` (and `A B C = I`, `hadamardWitnessA_mul_B_mul_C_eq_one`). Assembled
from
the Hadamard Z–Y decomposition `hadamardC_eq_expPiDivTwo_smul_rotY_mul_rotZ` and the reassembly
`hadamardABC_reassembly` (`A X B X C = R_y(π/2) R_z(π)`). -/
theorem hadamardC_eq_expPiDivTwo_smul_hadamardABC :
    hadamardC = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I)
      • (hadamardWitnessA * pauliX * hadamardWitnessB * pauliX * hadamardWitnessC) := by
  rw [hadamardABC_reassembly, hadamardC_eq_expPiDivTwo_smul_rotY_mul_rotZ]

end AxQM.Concrete
