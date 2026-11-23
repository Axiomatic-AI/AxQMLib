/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.AxisAngleRotation
import AxQM.Postulates.API.HadamardGate
import AxQM.Concrete.AxisAngleGateValues

/-!
# AxQM.Postulates.API — Exercise 4.8(2,3): the axis-angle values for `H` and `S`

The content of parts 2 and 3 of Nielsen & Chuang, Exercise 4.8: the operator-level
identities pinning the axis-angle parameters `α, θ, n̂` in `U = e^{iα} R_n̂(θ)` (eq. 4.9) for the
Hadamard gate `H` and the phase gate `S = diag(1, i)`.

* `sGate` — the **phase gate** `S = diag(1, i)` as an `Evolution qubit`, promoting the concrete
  matrix `Concrete.sMatrix` through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; unitarity
  (the `Evolution` obligation) is transported from `Concrete.sMatrix_mem_unitaryGroup`, exactly as
  for `hadamardGate`/`tGate`. `sGate_op` is its `simp` bridge to the underlying operator.
* `hadamardGate_op_eq_expPiDivTwo_smul_rotAxisGate` — **Exercise 4.8(2)** at the operator level:
  `H = e^{iπ/2} • R_{(1/√2, 0, 1/√2)}(π)` (`α = π/2`, `θ = π`, `n̂ = (1/√2, 0, 1/√2)`).
* `sGate_op_eq_expPiDivFour_smul_rotZGate` — **Exercise 4.8(3)** at the operator level:
  `S = e^{iπ/4} • R_z(π/2)` (`α = π/4`, `θ = π/2`, `n̂ = ẑ`).

Each identity is the image, under the `ℂ`-linear `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`
(which preserves the scalar), of the concrete matrix identity in
`AxQM/Concrete/AxisAngleGateValues.lean`.
The gates used are `rotAxisGate` (`AxQM/Postulates/API/BlochRotationGate.lean`) for the general
axis of `H` and `rotZGate` (`AxQM/Postulates/API/PiEighthGate.lean`) for the `ẑ` axis of `S`.

The operator statements keep the explicit phase; the physically observable channel reading — that
`H` and `S` *are* these rotations, the phase being unobservable — is in
`AxQM/NC/Ch4/Exercise4_8.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **phase gate** `S = diag(1, i)` as a closed-system evolution of the `qubit` (Nielsen &
Chuang, §4.2). Its operator is the concrete matrix `Concrete.sMatrix` promoted through the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; unitarity — the `Evolution` proof obligation — is
transported from `Concrete.sMatrix_mem_unitaryGroup`, exactly as for `hadamardGate`/`tGate`. -/
def sGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.sMatrix_mem_unitaryGroup

@[simp]
theorem sGate_op : sGate.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix := rfl

/-- **Nielsen & Chuang, Exercise 4.8(2) at the operator level.** The Hadamard gate is `e^{iπ/2}`
times the axis rotation by `θ = π` about `n̂ = (1/√2, 0, 1/√2)`:
`H = e^{iπ/2} • R_{(1/√2, 0, 1/√2)}(π)` (`α = π/2`, `θ = π`). The image under the `ℂ`-linear
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM` of the matrix identity
`Concrete.hadamardC_eq_expPiDivTwo_smul_rotAxis`. -/
theorem hadamardGate_op_eq_expPiDivTwo_smul_rotAxisGate :
    hadamardGate.op = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (rotAxisGate ![(Real.sqrt 2)⁻¹, 0, (Real.sqrt 2)⁻¹] Real.pi).op := by
  rw [hadamardGate_op, rotAxisGate_op, Concrete.hadamardC_eq_expPiDivTwo_smul_rotAxis]
  exact map_smul _ _ _

/-- **Nielsen & Chuang, Exercise 4.8(3) at the operator level.** The phase gate `S = diag(1, i)` is
`e^{iπ/4}` times the `ẑ`-axis rotation by `θ = π/2`: `S = e^{iπ/4} • R_z(π/2)` (`α = π/4`,
`θ = π/2`, `n̂ = ẑ`). The image under the `ℂ`-linear `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`
of the matrix identity `Concrete.sMatrix_eq_expPiDivFour_smul_rotZ`. -/
theorem sGate_op_eq_expPiDivFour_smul_rotZGate :
    sGate.op = Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) • (rotZGate (Real.pi / 2)).op := by
  rw [sGate_op, rotZGate_op, Concrete.sMatrix_eq_expPiDivFour_smul_rotZ]
  exact map_smul _ _ _

end AxQM
