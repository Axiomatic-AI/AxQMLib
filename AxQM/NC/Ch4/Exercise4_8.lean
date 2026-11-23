/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.AxisAngleGateValues

/-!
# Nielsen & Chuang, Exercise 4.8 — every single-qubit gate is a rotation up to a global phase

*(N&C p. 175.)*

Prove any single-qubit unitary U=e^{i alpha}R_n(theta); find params for H and S.

## The statements

N&C's `U = exp(iα) R_n̂(θ)` carries an overall phase `exp(iα)`, physically unobservable because it
cancels in the induced state map `ρ ↦ U ρ U†` (`|e^{iα}|² = 1`). So *as a quantum operation*, every
single-qubit gate is exactly some Bloch-sphere rotation — the grounded reading of the
exercise. Each theorem is stated for `Evolution.evolve`, states, and a rotation gate.

* **Part 1** — `Evolution.exists_evolve_eq_rotAxisGate_evolve`: for *every* gate `U : Evolution
  qubit` there is a real *unit* axis `n̂` and angle `θ` with `U` and `R_n̂(θ)` inducing the **same**
  evolution for every `ρ`.
* **Part 2 (Hadamard)** — `hadamardGate_evolve_eq_rotAxisGate_evolve`: the explicit values
  `α = π/2`, `θ = π`, `n̂ = (1/√2, 0, 1/√2)` — `H` induces the same channel as
  `R_{(1/√2, 0, 1/√2)}(π)`.
* **Part 3 (phase gate)** — `sGate_evolve_eq_rotZGate_evolve`: the explicit values `α = π/4`,
  `θ = π/2`, `n̂ = ẑ` — `S = diag(1, i)` induces the same channel as `R_z(π/2)` (the `ẑ`-axis
  rotation).

## Related results, and fidelity

* **`Concrete.exists_axis_angle_decomposition`** (`Concrete/AxisAngleDecomposition.lean`) — the pure
  `2 × 2` matrix statement of Part 1 **with the explicit phase**: `U = e^{iα} • rotAxis n̂ θ` for
  `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` (the `SU(2) = unit quaternions` fact, `α = arg(det U)/2`).
* **`Concrete.hadamardC_eq_expPiDivTwo_smul_rotAxis`** and
  **`Concrete.sMatrix_eq_expPiDivFour_smul_rotZ`** (`Concrete/AxisAngleGateValues.lean`) — the
  explicit matrix identities of Parts 2/3 (`H = e^{iπ/2} • R_{(1/√2,0,1/√2)}(π)`,
  `S = e^{iπ/4} • R_z(π/2)`).
* **`rotAxisGate`**, **`sGate`**, and the operator-level identities
  (`Evolution.exists_op_eq_phase_smul_rotAxisGate`,
  `hadamardGate_op_eq_expPiDivTwo_smul_rotAxisGate`,
  `sGate_op_eq_expPiDivFour_smul_rotZGate` in `Postulates/API`) give the full `α`-bearing operator
  forms `U = e^{iα} R_n̂(θ)`. Each theorem below feeds its
  operator identity to the shared global-phase-invariance lemma
  `Evolution.evolve_eq_of_op_eq_phase_smul` (`‖e^{iα}‖ = 1`), collapsing the phase to the channel
  equality.

This is not a weakening of eq. 4.9: the full α-bearing operator forms are proved outright upstream
and cited; this file adds the honest physical content — the phase-free channel identities — with
`n̂` a genuine unit vector and `θ` real, exactly as N&C states, and with the explicit answer values
for `H` and `S`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.8(1).** Every single-qubit gate is, as a quantum operation, a
Bloch-sphere rotation: for each `U : Evolution qubit` there are a real *unit* axis `n̂`
(`n₀² + n₁² + n₂² = 1`) and an angle `θ` such that `U` and the rotation gate `R_n̂(θ)` induce the
identical state evolution `ρ ↦ U ρ U†` for every state `ρ`. The operator decomposition
`U = e^{iα} R_n̂(θ)` (eq. 4.9, `Evolution.exists_op_eq_phase_smul_rotAxisGate`) holds up to the
global phase `e^{iα}`; that phase has unit modulus, so it cancels in the conjugation defining
`Evolution.evolve` (`Evolution.evolve_eq_of_op_eq_phase_smul`), which is the precise sense in which
it is physically unobservable and every gate *is* a rotation. -/
theorem Evolution.exists_evolve_eq_rotAxisGate_evolve (U : Evolution qubit) :
    ∃ (θ : ℝ) (n : Fin 3 → ℝ), (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) ∧
      ∀ ρ : State qubit, U.evolve ρ = (rotAxisGate n θ).evolve ρ := by
  obtain ⟨α, θ, n, hn, hop⟩ := U.exists_op_eq_phase_smul_rotAxisGate
  exact ⟨θ, n, hn, fun ρ => Evolution.evolve_eq_of_op_eq_phase_smul U (rotAxisGate n θ)
    (Complex.norm_exp_ofReal_mul_I α) hop ρ⟩

/-- **Nielsen & Chuang, Exercise 4.8(2): the Hadamard gate `H`.** With `α = π/2`, `θ = π`, and the
`x̂ + ẑ` axis `n̂ = (1/√2, 0, 1/√2)`, the Hadamard gate and the rotation `R_n̂(π)` induce the
identical state evolution `ρ ↦ U ρ U†` for every `ρ`. The operator identity
`H = e^{iπ/2} • R_{(1/√2, 0, 1/√2)}(π)` (`hadamardGate_op_eq_expPiDivTwo_smul_rotAxisGate`) holds up
to the unit-modulus phase `e^{iπ/2}`, which cancels in the channel via
`Evolution.evolve_eq_of_op_eq_phase_smul`. -/
theorem hadamardGate_evolve_eq_rotAxisGate_evolve (ρ : State qubit) :
    hadamardGate.evolve ρ
      = (rotAxisGate ![(Real.sqrt 2)⁻¹, 0, (Real.sqrt 2)⁻¹] Real.pi).evolve ρ :=
  Evolution.evolve_eq_of_op_eq_phase_smul hadamardGate _
    (Complex.norm_exp_ofReal_mul_I _) hadamardGate_op_eq_expPiDivTwo_smul_rotAxisGate ρ

/-- **Nielsen & Chuang, Exercise 4.8(3): the phase gate `S = diag(1, i)`.** With `α = π/4`,
`θ = π/2`, and the `ẑ` axis `n̂ = (0, 0, 1)`, the phase gate `sGate` and the `ẑ`-axis rotation
`R_z(π/2)` induce the identical state evolution `ρ ↦ U ρ U†` for every `ρ`. The operator identity
`S = e^{iπ/4} • R_z(π/2)` (`sGate_op_eq_expPiDivFour_smul_rotZGate`) holds up to the unit-modulus
phase `e^{iπ/4}`, which cancels in the channel via `Evolution.evolve_eq_of_op_eq_phase_smul`. -/
theorem sGate_evolve_eq_rotZGate_evolve (ρ : State qubit) :
    sGate.evolve ρ = (rotZGate (Real.pi / 2)).evolve ρ :=
  Evolution.evolve_eq_of_op_eq_phase_smul sGate _
    (Complex.norm_exp_ofReal_mul_I _) sGate_op_eq_expPiDivFour_smul_rotZGate ρ

end AxQM
