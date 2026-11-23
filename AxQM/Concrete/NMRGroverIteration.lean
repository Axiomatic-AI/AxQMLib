/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ABCDecomposition
import ToMathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: simplifying the NMR Grover iteration (Nielsen & Chuang, Exercise 7.51)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §7.7.4 (p. 339–340) describe the
two-qubit (`N = 4`) Grover search realised on an NMR quantum computer. Each of the three ingredients
of the **Grover iteration** `G = H^{⊗2} · P · H^{⊗2} · O` is expressed as single-qubit rotation
pulses `R_x, R_y` (`R = R(π/2)`, `R̄ = R(−π/2)`, `R² = R(π)`) plus one free-`J`-coupling period
`τ = e^{−iH/2ℏJ}`:

* `H^{⊗2} = R²_{x1} R̄_{y1} R²_{x2} R̄_{y2}` (`= (R²_x R̄_y) ⊗ (R²_x R̄_y)`, `nmrHadamardPair`);
* `P = R_{y1} R_{x1} R̄_{y1} R_{y2} R_{x2} R̄_{y2} τ`
  (`= (R_y R_x R̄_y)^{⊗2} τ`, `nmrPhaseShiftPulse`);
* `O` — the oracle for the marked item `x₀` — has the same `R_y R_x(·) R̄_y` shape on each qubit,
  with the **middle** `x`-rotation `R̄_x` (angle `−π/2`) on a qubit whose `x₀`-bit is `1` and `R_x`
  (angle `+π/2`) on a qubit whose bit is `0` (`nmrOraclePulse`). For `x₀ = 3 = |11⟩` this is N&C's
  `O = R_{y1} R̄_{x1} R̄_{y1} R_{y2} R̄_{x2} R̄_{y2} τ`; the other three cases (Exercise 7.50)
  flip the `x`-rotation direction on the unmarked qubit(s).

**Exercise 7.51** asks to show that `G` *simplifies* — the adjacent single-qubit rotations at the
`O`–`H^{⊗2}` and `H^{⊗2}`–`P` junctions cancel — to the four cases of (7.172).

## What is proved

`nmrGroverIteration_collapse` is the heart: multiplying out `G` and cancelling the adjacent
rotations (the `R̄_y R_y = 1` at each junction, then `R²_x R_x(±·) = R_x(π ±·)`) collapses `G`
to the two-block form `(R̄_x R̄_y)^{⊗2} τ · (R_x(π+s₁) R̄_y ⊗ R_x(π+s₂) R̄_y) τ`, where `sₖ` is the
oracle's `x`-angle on qubit `k`. From it the four cases of (7.172) follow by evaluating `R_x(π+s)`:

* `nmrGroverIteration_markedThree` (`x₀ = 3`) and `nmrGroverIteration_markedZero` (`x₀ = 0`) are
  **exact** matrix identities `G = nmrGroverIterationSimplified …`;
* `nmrGroverIteration_markedTwo` (`x₀ = 2`) and `nmrGroverIteration_markedOne` (`x₀ = 1`) are
  `G = −(nmrGroverIterationSimplified …)`.

The global `−1` in the one-marked-qubit cases is the honest accounting of N&C's *"up to an
irrelevant overall phase factor"*: on a qubit whose bit is `0` the collapse produces `R_x(3π/2) =
−R_x(−π/2) = −R̄_x` (the spinor `2π`-rotation sign), so an odd number of such qubits leaves one
factor of `−1`. It cancels in the induced channel `ρ ↦ G ρ G†` (physically unobservable), exactly
as the residual global phase does in Exercise 7.50. Rather than hide it, we surface it.

`nmrGroverIterationSimplified a₁ a₂ τ` is the literal right-hand side of (7.172): the fixed left
block `(R̄_x R̄_y)^{⊗2} τ` followed by `(R_x(a₁) R̄_y ⊗ R_x(a₂) R̄_y) τ`, with `aₖ = +π/2`
(`R_x`, unmarked bit `1`) or `−π/2` (`R̄_x`, bit `0`).

## Generality and scope

The free-evolution period `τ` is left an **arbitrary** `4×4` matrix: the cancellation is entirely in
the single-qubit rotations and never touches `τ`, so the identity holds for every `τ` — in
particular for the physical `e^{−iH/2ℏJ}`. This is a faithful generalisation (strictly stronger),
not a weakening. Every statement names only the concrete rotation matrices `rotX`/`rotY` and
Mathlib's Kronecker product. That the pulse products are the genuine Grover operators is the physics
content of Exercises 7.41 and 7.50 (`Postulates/API/NMRGroverOracle.lean`,
`NC/Ch7/Exercise7_50.lean`); this file supplies only the algebraic simplification `G ↦ (7.172)` that
Exercise 7.51 asks for.
-/

noncomputable section

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-! ### General `R_x` rotation identities -/

/-- **A full `2π` `x`-rotation is `−I`:** `R_x(2π) = −1`, the spinor double-cover sign
(`cos(π) = −1`, `sin(π) = 0` in the closed form `rotAxis_eq_of_unit`). -/
theorem rotX_two_pi : rotX (2 * Real.pi) = -1 := by
  have hunit : (![1, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + ![1, 0, 0] 1 ^ 2 + ![1, 0, 0] 2 ^ 2 = 1 := by
    simp
  simp only [rotX]
  rw [rotAxis_eq_of_unit hunit, show (2 * Real.pi) / 2 = Real.pi from by ring, Real.cos_pi,
    Real.sin_pi]
  simp

/-- **Shifting an `x`-rotation by `2π` flips the sign:** `R_x(a + 2π) = −R_x(a)` — the source of the
"irrelevant overall phase" `−1` when an oracle's unmarked qubit contributes `R_x(3π/2)`. -/
theorem rotX_add_two_pi (a : ℝ) : rotX (a + 2 * Real.pi) = -rotX a := by
  rw [← rotX_mul_rotX, rotX_two_pi, mul_neg_one]

/-- `R_x(3π/2) = −R̄_x`: a full-plus-quarter turn `R_x(π+π/2)` picks up the spinor `2π`-sign — the
`−1` a bit-`0` qubit contributes to the collapse. -/
theorem rotX_pi_add_pi_div_two : rotX (Real.pi + Real.pi / 2) = -rotX (-(Real.pi / 2)) := by
  rw [show Real.pi + Real.pi / 2 = -(Real.pi / 2) + 2 * Real.pi from by ring, rotX_add_two_pi]

/-- `R_x(π + (−π/2)) = R_x(π/2)`: the marked-qubit `x`-angle after the collapse. -/
theorem rotX_pi_sub_pi_div_two : rotX (Real.pi + -(Real.pi / 2)) = rotX (Real.pi / 2) := by
  rw [show Real.pi + -(Real.pi / 2) = Real.pi / 2 from by ring]

/-! ### Kronecker sign lemmas -/

/-- `(−A) ⊗ₖ B = −(A ⊗ₖ B)`: the Kronecker product is linear in its left factor. -/
private theorem neg_kron (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  rw [← neg_one_smul ℂ A, Matrix.smul_kronecker, neg_one_smul]

/-- `A ⊗ₖ (−B) = −(A ⊗ₖ B)`: the Kronecker product is linear in its right factor. -/
private theorem kron_neg (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  rw [← neg_one_smul ℂ B, Matrix.kronecker_smul, neg_one_smul]

/-- `(−A) ⊗ₖ (−B) = A ⊗ₖ B`: the two sign changes cancel (`(−1)(−1) = 1`). Proved through the scalar
action to sidestep matrix `neg_neg`. -/
private theorem neg_kron_neg (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (-A) ⊗ₖ (-B) = A ⊗ₖ B := by
  rw [← neg_one_smul ℂ A, ← neg_one_smul ℂ B, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul, show ((-1 : ℂ) * (-1 : ℂ)) = 1 from by norm_num, one_smul]

/-! ### The single-qubit pulses -/

/-- The per-qubit **Hadamard pulse** `H = R²_x R̄_y = R_x(π) R_y(−π/2)` (N&C p. 339). -/
def nmrHadamardPulse : Matrix (Fin 2) (Fin 2) ℂ := rotX Real.pi * rotY (-(Real.pi / 2))

/-- The per-qubit **`R_y R_x(s) R̄_y` sandwich** `= R_y(π/2) R_x(s) R_y(−π/2)`. The phase-shift
pulse `P` uses `s = π/2` on each qubit; the oracle `O` uses `s = −π/2` on a marked qubit (`R̄_x`)
and `s = +π/2` on an unmarked qubit (`R_x`). -/
def nmrRotYXY (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotY (Real.pi / 2) * rotX s * rotY (-(Real.pi / 2))

/-- **The junction cancellation, per qubit:** `H · (R_y R_x(s) R̄_y) = R_x(π+s) R̄_y`. The adjacent
`R̄_y R_y = 1` cancels and the two `x`-rotations `R_x(π) R_x(s)` combine into `R_x(π+s)` — the
whole content of "cancelling adjacent single-qubit rotations". -/
theorem nmrHadamardPulse_mul_nmrRotYXY (s : ℝ) :
    nmrHadamardPulse * nmrRotYXY s = rotX (Real.pi + s) * rotY (-(Real.pi / 2)) := by
  simp only [nmrHadamardPulse, nmrRotYXY, mul_assoc]
  rw [← mul_assoc (rotY (-(Real.pi / 2))) (rotY (Real.pi / 2)), rotY_mul_rotY,
    show -(Real.pi / 2) + Real.pi / 2 = 0 from by ring, rotY_zero, one_mul, ← mul_assoc,
    rotX_mul_rotX]

/-! ### The two-qubit Grover iteration -/

/-- `H^{⊗2} = H ⊗ H`, the two-qubit Hadamard as a Kronecker product of the per-qubit pulse. -/
def nmrHadamardPair : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  nmrHadamardPulse ⊗ₖ nmrHadamardPulse

/-- The **conditional phase-shift** `P = (R_y R_x R̄_y)^{⊗2} τ` (Nielsen & Chuang eq. 7.171 in pulse
form), with the free-`J`-evolution period `τ` a parameter. -/
def nmrPhaseShiftPulse (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (nmrRotYXY (Real.pi / 2) ⊗ₖ nmrRotYXY (Real.pi / 2)) * τ

/-- The **oracle** `O = (R_y R_x(s₁) R̄_y ⊗ R_y R_x(s₂) R̄_y) τ` for the marked item with per-qubit
`x`-rotation angles `s₁, s₂` (each `−π/2` on a marked bit, `+π/2` on an unmarked bit). -/
def nmrOraclePulse (s₁ s₂ : ℝ) (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (nmrRotYXY s₁ ⊗ₖ nmrRotYXY s₂) * τ

/-- The **Grover iteration** `G = H^{⊗2} P H^{⊗2} O`, in NMR pulse form, for the oracle whose
per-qubit `x`-rotation angles are `s₁, s₂`. -/
def nmrGroverIteration (s₁ s₂ : ℝ) (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  nmrHadamardPair * nmrPhaseShiftPulse τ * nmrHadamardPair * nmrOraclePulse s₁ s₂ τ

/-- The **simplified Grover iteration** — the right-hand side of Nielsen & Chuang (7.172): the fixed
left block `(R̄_x R̄_y)^{⊗2} τ` followed by `(R_x(a₁) R̄_y ⊗ R_x(a₂) R̄_y) τ`, with `aₖ = +π/2`
(unmarked bit `1`, `R_x`) or `−π/2` (bit `0`, `R̄_x`). -/
def nmrGroverIterationSimplified (a₁ a₂ : ℝ) (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2)))
        ⊗ₖ (rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2)))) * τ
    * ((rotX a₁ * rotY (-(Real.pi / 2))) ⊗ₖ (rotX a₂ * rotY (-(Real.pi / 2)))) * τ

/-- **Cancelling the adjacent rotations collapses the Grover iteration.** For every free-evolution
`τ` and oracle angles `s₁, s₂`,
`G = (R̄_x R̄_y)^{⊗2} · τ · (R_x(π+s₁) R̄_y ⊗ R_x(π+s₂) R̄_y) · τ`.
The `H^{⊗2}·P` junction collapses to the sign-free left block `(R̄_x R̄_y)^{⊗2}` (the two
`R_x(3π/2) = −R̄_x` factors' signs cancel across the Kronecker product), and the `H^{⊗2}·O`
junction to `R_x(π+s₁) R̄_y ⊗ R_x(π+s₂) R̄_y`. -/
theorem nmrGroverIteration_collapse (s₁ s₂ : ℝ)
    (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration s₁ s₂ τ =
      ((rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2)))
          ⊗ₖ (rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2)))) * τ
        * ((rotX (Real.pi + s₁) * rotY (-(Real.pi / 2)))
            ⊗ₖ (rotX (Real.pi + s₂) * rotY (-(Real.pi / 2)))) * τ := by
  have hL : nmrHadamardPair * nmrPhaseShiftPulse τ =
      ((rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2))) ⊗ₖ
        (rotX (-(Real.pi / 2)) * rotY (-(Real.pi / 2)))) * τ := by
    rw [nmrPhaseShiftPulse, ← mul_assoc, nmrHadamardPair, ← Matrix.mul_kronecker_mul,
      nmrHadamardPulse_mul_nmrRotYXY, rotX_pi_add_pi_div_two, neg_mul, neg_kron_neg]
  have hR : nmrHadamardPair * nmrOraclePulse s₁ s₂ τ =
      ((rotX (Real.pi + s₁) * rotY (-(Real.pi / 2))) ⊗ₖ
        (rotX (Real.pi + s₂) * rotY (-(Real.pi / 2)))) * τ := by
    rw [nmrOraclePulse, ← mul_assoc, nmrHadamardPair, ← Matrix.mul_kronecker_mul]
    simp only [nmrHadamardPulse_mul_nmrRotYXY]
  rw [nmrGroverIteration, hL, mul_assoc, hR, ← mul_assoc]

/-! ### The four cases of (7.172) -/

/-- **Exercise 7.51, `x₀ = 3 = |11⟩`.** With both qubits marked (`s₁ = s₂ = −π/2`) the Grover
iteration equals its simplified form *exactly* (no residual phase):
`G = (R̄_x R̄_y)^{⊗2} τ · (R_x R̄_y)^{⊗2} τ`. -/
theorem nmrGroverIteration_markedThree (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (-(Real.pi / 2)) (-(Real.pi / 2)) τ
      = nmrGroverIterationSimplified (Real.pi / 2) (Real.pi / 2) τ := by
  rw [nmrGroverIteration_collapse, nmrGroverIterationSimplified, rotX_pi_sub_pi_div_two]

/-- **Exercise 7.51, `x₀ = 0 = |00⟩`.** With neither qubit marked (`s₁ = s₂ = +π/2`) the two
`R_x(3π/2) = −R̄_x` signs cancel, so again *exactly*
`G = (R̄_x R̄_y)^{⊗2} τ · (R̄_x R̄_y)^{⊗2} τ`. -/
theorem nmrGroverIteration_markedZero (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (Real.pi / 2) (Real.pi / 2) τ
      = nmrGroverIterationSimplified (-(Real.pi / 2)) (-(Real.pi / 2)) τ := by
  rw [nmrGroverIteration_collapse, nmrGroverIterationSimplified, rotX_pi_add_pi_div_two,
    neg_mul, neg_kron_neg]

/-- **Exercise 7.51, `x₀ = 2 = |10⟩`.** Qubit 1 marked (`s₁ = −π/2`), qubit 2 unmarked
(`s₂ = +π/2`): the single unmarked qubit contributes `R_x(3π/2) = −R̄_x`, leaving the overall
"irrelevant" phase `−1`:
`G = −((R̄_x R̄_y)^{⊗2} τ · (R_x R̄_y ⊗ R̄_x R̄_y) τ)`. -/
theorem nmrGroverIteration_markedTwo (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (-(Real.pi / 2)) (Real.pi / 2) τ
      = -nmrGroverIterationSimplified (Real.pi / 2) (-(Real.pi / 2)) τ := by
  rw [nmrGroverIteration_collapse, rotX_pi_sub_pi_div_two, rotX_pi_add_pi_div_two, neg_mul,
    kron_neg, nmrGroverIterationSimplified]
  simp only [mul_neg, neg_mul]

/-- **Exercise 7.51, `x₀ = 1 = |01⟩`.** Qubit 1 unmarked (`s₁ = +π/2`), qubit 2 marked
(`s₂ = −π/2`): symmetric to the `x₀ = 2` case, leaving the overall phase `−1`:
`G = −((R̄_x R̄_y)^{⊗2} τ · (R̄_x R̄_y ⊗ R_x R̄_y) τ)`. -/
theorem nmrGroverIteration_markedOne (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    nmrGroverIteration (Real.pi / 2) (-(Real.pi / 2)) τ
      = -nmrGroverIterationSimplified (-(Real.pi / 2)) (Real.pi / 2) τ := by
  rw [nmrGroverIteration_collapse, rotX_pi_add_pi_div_two, neg_mul, rotX_pi_sub_pi_div_two,
    neg_kron, nmrGroverIterationSimplified]
  simp only [mul_neg, neg_mul]

end AxQM.Concrete
