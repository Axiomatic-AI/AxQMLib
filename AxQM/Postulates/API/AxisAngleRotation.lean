/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochRotationGate
import AxQM.Concrete.AxisAngleDecomposition

/-!
# AxQM.Postulates.API — Exercise 4.8(1): every single-qubit gate is a phase × `R_n̂(θ)`

The content of the first part of Nielsen & Chuang, Exercise 4.8: the operator-level
statement that *every* single-qubit gate is a phase times an axis-rotation gate.

The axis-rotation gate `rotAxisGate n θ` (`R_n̂(θ) = exp(-iθ n̂·σ/2)` as an `Evolution qubit`) and
its `simp` bridge `rotAxisGate_op` are **reused** from `AxQM/Postulates/API/BlochRotationGate.lean`
(Exercise 4.6's Bloch-sphere-rotation development).

* `Evolution.exists_op_eq_phase_smul_rotAxisGate` — **Exercise 4.8(1) at the operator level**: for
  every gate `U : Evolution qubit` there are real `α, θ` and a unit vector `n̂` with
  `U.op = e^{iα} • (rotAxisGate n̂ θ).op` (eq. 4.9). Proof: `M := toEuclideanCLM⁻¹ U.op`
  is unitary (`toEuclideanCLM` is a `⋆`-isomorphism), so `Concrete.exists_axis_angle_decomposition`
  gives `M = e^{iα} rotAxis n̂ θ`, and applying `toEuclideanCLM` (`ℂ`-linear) lifts it to operators.

The operator statement keeps the explicit phase `e^{iα}`; the physically observable channel
reading — that the phase is unobservable, so `U` *is* the rotation — is in
`AxQM/NC/Ch4/Exercise4_8.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.8(1) at the operator level.** Every single-qubit gate
`U : Evolution qubit` equals a phase times an axis-rotation gate: there exist real numbers `α, θ`
and a real *unit* three-vector `n̂` (`n₀² + n₁² + n₂² = 1`) with
`U.op = e^{iα} • (rotAxisGate n̂ θ).op`, i.e. `U = e^{iα} R_n̂(θ)` (eq. 4.9) as operators. The
image, under the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (`ℂ`-linear, so it preserves it),
of the concrete matrix decomposition `Concrete.exists_axis_angle_decomposition` applied to the
matrix `toEuclideanCLM⁻¹ U.op` of `U` (unitary, as `toEuclideanCLM` is a `⋆`-isomorphism). -/
theorem Evolution.exists_op_eq_phase_smul_rotAxisGate (U : Evolution qubit) :
    ∃ (α θ : ℝ) (n : Fin 3 → ℝ), (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) ∧
      U.op = Complex.exp ((α : ℂ) * Complex.I) • (rotAxisGate n θ).op := by
  obtain ⟨α, θ, n, hn, hMeq⟩ :=
    Concrete.exists_axis_angle_decomposition
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).symm U.op)
      (Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).symm U.unitary)
  refine ⟨α, θ, n, hn, ?_⟩
  have hUM : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).symm U.op) = U.op :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).apply_symm_apply U.op
  rw [rotAxisGate_op, ← hUM, hMeq]
  exact map_smul _ _ _

end AxQM
