/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardGate
import AxQM.Postulates.API.PiEighthGate
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Concrete.HadamardABC

/-!
# AxQM.Postulates.API — the ABC decomposition of the Hadamard gate (operator level)

The operator-level content of Nielsen & Chuang, Exercise 4.12: the Hadamard gate `H` equals the ABC
product `A X B X C` (of `y`/`z`-rotation gates and the Pauli-`X` gate) up to the global phase
`e^{iπ/2}`, where the witnesses are those of Corollary 4.2 for the Hadamard's Z–Y parameters
(`Concrete/HadamardABC.lean`):

`α = π/2`,  `A = R_y(π/4)`,  `B = R_y(-π/4) R_z(-π/2)`,  `C = R_z(π/2)`.

This is the operator-level statement; the statement that `H` and the ABC gate product induce the
*same state evolution* is in `AxQM/NC/Ch4/Exercise4_12.lean`.

## What is formalised

* `rotYGate θ` — the **`y`-axis rotation gate** `R_y(θ) = exp(-iθY/2)` as an `Evolution qubit` (the
  `y`-axis analogue of `rotXGate`/`rotZGate`), with the `simp` bridge `rotYGate_op`. It completes
  the `R_x`/`R_y`/`R_z` gate family and is reusable infrastructure.
* `hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate` — **Exercise 4.12 at the operator level**:
  `H = e^{iπ/2} • (A X B X C)` as operators on the qubit state space, the image under the
  `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (`ℂ`-linear, so it preserves the phase, and
  multiplicative, so it carries the matrix product to the `Evolution.comp` composite) of the
  concrete matrix identity `Concrete.hadamardC_eq_expPiDivTwo_smul_hadamardABC`.

## Design notes

* **Related results.** Compare `rotXGate`/`rotZGate` and
  `hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate` (Exercise 4.4).
* **Composition order.** The `Evolution` composite is nested to match the left-associated matrix
  product `A X B X C = ((((A · X) · B) · X) · C)`, with `B = R_y(-π/4) R_z(-π/2)` a composite too;
  `Evolution.comp_op` and the `_op` bridges then identify the composite's operator with the image of
  the matrix product under `Matrix.toEuclideanCLM` (`map_mul`), closed by `rfl` at the `*`/`.comp`
  definitional equality.
-/

noncomputable section

namespace AxQM

/-- The **`y`-axis rotation gate** `R_y(θ) = exp(-iθY/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.5), the `y`-axis analogue of `rotXGate`/`rotZGate`. Its operator is
the concrete rotation matrix `Concrete.rotY θ` promoted through the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM`; unitarity — the `Evolution` proof obligation — is transported from
`Concrete.rotY_mem_unitaryGroup`. -/
def rotYGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) (Concrete.rotY_mem_unitaryGroup θ)

@[simp]
theorem rotYGate_op (θ : ℝ) :
    (rotYGate θ).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY θ) := rfl

/-- **Nielsen & Chuang, Exercise 4.12 at the operator level.** The Hadamard gate equals its ABC
product up to the global phase `e^{iπ/2}`: `H = e^{iπ/2} • (A X B X C)`, with `A = R_y(π/4)`,
`B = R_y(-π/4) R_z(-π/2)`, `C = R_z(π/2)` (Corollary 4.2's witnesses for the Hadamard's Z–Y
parameters), as operators on the qubit state space. This is the image under the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM` (`ℂ`-linear and multiplicative) of the concrete matrix identity
`Concrete.hadamardC_eq_expPiDivTwo_smul_hadamardABC`. -/
theorem hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate :
    hadamardGate.op = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (((((rotYGate (Real.pi / 4)).comp pauliXGate).comp
          ((rotYGate (-(Real.pi / 4))).comp (rotZGate (-(Real.pi / 2))))).comp pauliXGate).comp
          (rotZGate (Real.pi / 2))).op := by
  rw [hadamardGate_op, Concrete.hadamardC_eq_expPiDivTwo_smul_hadamardABC, map_smul]
  refine congrArg (_ • ·) ?_
  simp only [Concrete.hadamardWitnessA, Concrete.hadamardWitnessB, Concrete.hadamardWitnessC,
      map_mul,
    Evolution.comp_op, rotYGate_op, rotZGate_op, pauliXGate_op]
  rfl

end AxQM
