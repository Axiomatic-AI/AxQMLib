/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.Evolution
import AxQM.Concrete.PiEighthGate

/-!
# AxQM.Postulates.API — the π/8 (T) gate and `R_z` as qubit evolutions

The single-qubit gates of Nielsen & Chuang's Exercise 4.3: the π/8 gate `T` and the `z`-axis
rotation `R_z(θ)`, each promoted from its concrete `2 × 2` unitary matrix (`Concrete.tMatrix`,
`Concrete.rotZ`) to an `Evolution` of the `qubit`, alongside `hadamardGate`.

* `tGate`, `rotZGate θ` — the gates as `Evolution qubit`. An `Evolution` bundles the
  unitarity obligation, discharged from the matrix-level unitarity
  (`Concrete.tMatrix_mem_unitaryGroup`, `Concrete.rotZ_mem_unitaryGroup`) transported through the
  `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`, exactly as for `hadamardGate`.
* `tGate_op_eq_expPiDivEight_smul_rotZGate` — the **operator-level statement of Exercise 4.3**:
  `T = exp(iπ/8) • R_z(π/4)` at the operator level (`Evolution.op`), the image under
  `Matrix.toEuclideanCLM` of the matrix identity `Concrete.tMatrix_eq_expPiDivEight_smul_rotZ`.

The physical consequence — that `T` and `R_z(π/4)` induce the *same* state channel — follows from
the general **global-phase-invariance of the channel** lemma
`Evolution.evolve_eq_of_op_eq_phase_smul` (in `AxQM/Postulates/API/Evolution.lean`,
since it does not depend on the π/8 gate): two evolutions whose operators
differ by a unit-modulus scalar induce the same `evolve`.

The physical statement that `T` and `R_z(π/4)` act identically on all states, in terms of
`Evolution.evolve`, is in `AxQM/NC/Ch4/Exercise4_3.lean`. `rotZGate` is a general `z`-rotation gate.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **π/8 (T) gate** `T` as a closed-system evolution of the `qubit` (Nielsen & Chuang,
eq. 4.2). Its operator is the concrete matrix `Concrete.tMatrix` promoted through the `⋆`-algebra
`Matrix.toEuclideanCLM`; unitarity — the `Evolution` proof obligation — is transported from
`Concrete.tMatrix_mem_unitaryGroup`. -/
def tGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.tMatrix
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.tMatrix_mem_unitaryGroup

@[simp]
theorem tGate_op : tGate.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.tMatrix := rfl

/-- The **`z`-axis rotation gate** `R_z(θ) = exp(-iθZ/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.6). Its operator is the concrete rotation matrix `Concrete.rotZ θ`
promoted through `Matrix.toEuclideanCLM`; unitarity is from `Concrete.rotZ_mem_unitaryGroup`. -/
def rotZGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotZ θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) (Concrete.rotZ_mem_unitaryGroup θ)

@[simp]
theorem rotZGate_op (θ : ℝ) :
    (rotZGate θ).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotZ θ) := rfl

/-- **Nielsen & Chuang Exercise 4.3 at the operator level** (eq. 4.3): the π/8 gate equals
`R_z(π/4)` up to the global phase `exp(iπ/8)`, `T = exp(iπ/8) • R_z(π/4)`. The image under the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (which is `ℂ`-linear, so it preserves the scalar)
of the matrix identity `Concrete.tMatrix_eq_expPiDivEight_smul_rotZ`. -/
theorem tGate_op_eq_expPiDivEight_smul_rotZGate :
    tGate.op = Complex.exp ((Real.pi / 8 : ℝ) * Complex.I) • (rotZGate (Real.pi / 4)).op := by
  rw [tGate_op, rotZGate_op, Concrete.tMatrix_eq_expPiDivEight_smul_rotZ]
  exact map_smul _ _ _

end AxQM
