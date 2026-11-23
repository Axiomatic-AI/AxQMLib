/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardRotation

/-!
# Nielsen & Chuang, Exercise 4.4 — the Hadamard gate as a product of `R_x`, `R_z` rotations

*(N&C p. 175.)*

Express Hadamard H as a product of R_x, R_z rotations and a phase e^{i phi}.

The closed-form answer is `H = e^{iπ/2} R_x(π/2) R_z(π/2) R_x(π/2)` (with `ϕ = π/2`, i.e.
`e^{iϕ} = i`): the Hadamard operator is the `X`–`Z`–`X` rotation sandwich, up to the global phase
`e^{iπ/2}`. The reflection `H` exchanges the `x̂` and `ẑ` axes, so — like every single-qubit gate
(Theorem 4.1) — it is a product of coordinate rotations and a phase.

## What "up to a global phase" means

A global phase is physically unobservable precisely because it cancels in the map a gate induces on
*states* (density operators), `ρ ↦ U ρ U†`: for `U = e^{iπ/2} R_x(π/2) R_z(π/2) R_x(π/2)`, the unit
scalar `e^{iπ/2}` and its conjugate multiply to `|e^{iπ/2}|² = 1`, so `U ρ U†` equals the
conjugation by the bare rotation product. Thus `H` and `R_x(π/2) R_z(π/2) R_x(π/2)`, *as quantum
operations*, are the **same gate**, even though as operators on vectors they differ by the phase.

The theorem of this file is exactly that physical statement:

* `hadamardGate_evolve_eq_rotXGate_rotZGate_rotXGate_evolve` — for every state `ρ` of the qubit,
  `H.evolve ρ = (R_x(π/2) R_z(π/2) R_x(π/2)).evolve ρ`, i.e. the Hadamard gate and the `X`–`Z`–`X`
  rotation product induce the *same* state evolution.

## Where the pieces live

The exercise's underlying matrix identity and the gates are cited here:

* **`AxQM.Concrete.rotX_mul_rotZ_mul_rotX_pi_div_two`** and
  **`Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX`**
  (`AxQM/Concrete/HadamardRotation.lean`)
  — the pure `2 × 2` matrix identity `H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))`, using the §4.2
  rotation matrices (`AxQM/Concrete/Rotation.lean`) and the complex Hadamard matrix
  (`AxQM/Concrete/Hadamard.lean`).
* **`AxQM.rotXGate`, `rotZGate`, `hadamardGate`** and
  **`hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate`**
  (`AxQM/Postulates/API/HadamardRotation.lean`, `AxQM/Postulates/API/PiEighthGate.lean`,
  `AxQM/Postulates/API/HadamardGate.lean`) — the gates as `Evolution qubit`, and the operator-level
  form `H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))`.
* **`Evolution.evolve_eq_of_op_eq_phase_smul`** (`AxQM/Postulates/API/Evolution.lean`, shared with
  Exercise 4.3) — the lemma that a unit-modulus global phase leaves the induced channel unchanged;
  the theorem below is that lemma applied to the operator identity with `c = e^{iπ/2}`
  (`‖e^{iπ/2}‖ = 1`).
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.4.** Up to a global phase, the Hadamard gate `H` equals the
`X`–`Z`–`X` rotation product `R_x(π/2) R_z(π/2) R_x(π/2)`: as quantum operations they are the *same*
gate — for every state `ρ` of the qubit, `H` and the rotation product induce the identical state
evolution `ρ ↦ U ρ U†`. The global phase `e^{iπ/2}` relating the two operators
(`hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate`) has unit modulus, so it cancels
in the conjugation defining `Evolution.evolve` (`Evolution.evolve_eq_of_op_eq_phase_smul`); this is
the precise sense in which the global phase `e^{iϕ}` of Exercise 4.4 is physically unobservable. -/
theorem hadamardGate_evolve_eq_rotXGate_rotZGate_rotXGate_evolve (ρ : State qubit) :
    hadamardGate.evolve ρ
      = (((rotXGate (Real.pi / 2)).comp (rotZGate (Real.pi / 2))).comp
          (rotXGate (Real.pi / 2))).evolve ρ :=
  Evolution.evolve_eq_of_op_eq_phase_smul hadamardGate _
    (Complex.norm_exp_ofReal_mul_I _)
    hadamardGate_op_eq_expPiDivTwo_smul_rotXGate_rotZGate_rotXGate ρ

end AxQM
