/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardGate
import AxQM.Postulates.API.PiEighthGate
import AxQM.Concrete.HadamardRotation

/-!
# AxQM.Postulates.API — the Hadamard gate as a product of `R_x`, `R_z` rotation gates

The operator-level content of Nielsen & Chuang, Exercise 4.4: the Hadamard gate `H` equals the
product `R_x(π/2) R_z(π/2) R_x(π/2)` of `x`- and `z`-rotation gates, up to the global phase
`e^{iπ/2}`. This is the operator-level statement; the statement that `H` and the rotation
product induce the *same state evolution* is in `AxQM/NC/Ch4/Exercise4_4.lean`.

## What is formalised

* `rotXGate θ` — the **`x`-axis rotation gate** `R_x(θ) = exp(-iθX/2)` as an `Evolution qubit`
  (the `x`-axis analogue of `rotZGate` from `Postulates/API/PiEighthGate.lean`), with the `simp`
  bridge `rotXGate_op`.
* `hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate` — **Exercise 4.4 at the operator
  level** (eq. of eq. 4.4-flavoured decomposition): `H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))`
  as operators on the qubit state space. The image, under the `⋆`-algebra isomorphism
  `Matrix.toEuclideanCLM` (which is `ℂ`-linear, so it preserves the scalar, and multiplicative, so
  it carries matrix products to composition), of the concrete matrix identity
  `Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX`.

## Design notes

* **Related results.** Compare `rotZGate` and `tGate_op_eq_expPiDivEight_smul_rotZGate`.
* **Composition order.** The Evolution composite
  `((rotXGate (π/2)).comp (rotZGate (π/2))).comp (rotXGate (π/2))` has operator
  `R_x(π/2) ∘ R_z(π/2) ∘ R_x(π/2)`, which `Matrix.toEuclideanCLM` identifies with the matrix
  product `R_x(π/2) R_z(π/2) R_x(π/2)` (`map_mul`): applying the composite is "first `R_x`, then
  `R_z`, then `R_x`", matching the right-to-left reading of the matrix product.
-/

noncomputable section

namespace AxQM

/-- The **`x`-axis rotation gate** `R_x(θ) = exp(-iθX/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.4). Its operator is the concrete rotation matrix `Concrete.rotX θ`
promoted through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; unitarity — the `Evolution`
proof obligation — is transported from `Concrete.rotX_mem_unitaryGroup`. -/
def rotXGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotX θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) (Concrete.rotX_mem_unitaryGroup θ)

@[simp]
theorem rotXGate_op (θ : ℝ) :
    (rotXGate θ).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotX θ) := rfl

/-- **Nielsen & Chuang, Exercise 4.4 at the operator level.** The Hadamard gate equals the
`X`–`Z`–`X` rotation product up to the global phase `e^{iπ/2}`:
`H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))`, as operators on the qubit state space. This is the
image under the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (`ℂ`-linear and multiplicative) of
the concrete matrix identity `Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX`. -/
theorem hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate :
    hadamardGate.op = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (((rotXGate (Real.pi / 2)).comp (rotZGate (Real.pi / 2))).comp
        (rotXGate (Real.pi / 2))).op := by
  rw [hadamardGate_op, Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX, map_smul]
  congr 1
  rw [map_mul, map_mul]
  simp only [Evolution.comp_op, rotXGate_op, rotZGate_op]
  rfl

end AxQM
