/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledPhaseShift
import AxQM.Postulates.API.ControlledRotation
import AxQM.Postulates.API.CnotRotationCommutation

/-!
# Nielsen & Chuang, Exercise 5.4 — decomposing the controlled-`R_k` gate

*(N&C p. 221.)*

Give a decomposition of the controlled-R_k gate into single-qubit and CNOT gates.

The `R_k` gate of the quantum-Fourier-transform circuit (N&C eq. 5.11) is the single-qubit phase
gate `R_k = P(2π/2ᵏ) = diag(1, exp(2πi/2ᵏ))`, i.e. the instance `φ = 2π/2ᵏ` of the general
phase-shift gate `P(φ) = phaseShiftGate φ`. Its controlled version `C(R_k) = controlledPhaseShift
(2π/2ᵏ)` is the *only* two-qubit gate in the QFT circuit, so decomposing it into one-qubit gates and
`CNOT`s is what lets the whole QFT be built from single-qubit gates and `CNOT`s.

## The decomposition

For an arbitrary phase angle `φ` the controlled phase-shift gate factors as

```
C(P(φ)) = (P(φ/2) ⊗ 1) · (1 ⊗ R_z(φ/2)) · CNOT · (1 ⊗ R_z(-φ/2)) · CNOT ,
```

a **phase gate `P(φ/2)` on the control**, the two `z`-rotations `R_z(±φ/2)` on the target, and two
`CNOT`s — all single-qubit gates and `CNOT`s. Reading the composition from the right (first gate
applied last in `·`): apply `CNOT`, `R_z(-φ/2)`, `CNOT`, `R_z(φ/2)` to the target and `P(φ/2)` to
the control.

`controlledPhaseShift_eq_cnot_circuit` states this for a general `φ`; `controlledRk_eq_cnot_circuit`
is the `R_k` instance `φ = 2π/2ᵏ` the exercise asks about (`R_k = P(2π/2ᵏ)`), the QFT's controlled
phase gate.

## Why a phase on the control is needed

The bare two-`CNOT` construction `(1 ⊗ R_z(φ/2)) · CNOT · (1 ⊗ R_z(-φ/2)) · CNOT` already equals the
controlled `z`-rotation `C(R_z(φ))` (the library's `controlledUnitary_rotZGate`, the N&C §4.3 /
Exercise 4.23 reduction, valid because `R_z`'s axis is perpendicular to `X`). But `R_k = P(φ)` is
**not** `R_z(φ)`: they differ by the global phase `P(φ) = e^{iφ/2} R_z(φ)` (`P(φ) = diag(1, e^{iφ})`
vs. `R_z(φ) = diag(e^{-iφ/2}, e^{iφ/2})`). For a controlled gate that global phase is *not*
invisible — it becomes a **relative** phase between the control's `|0⟩` and `|1⟩` branches
(`C(P(φ))` and `C(R_z(φ))` differ on the `|1⟩⟨1|` block by `e^{iφ/2}`), so it must be supplied by a
genuine phase gate on the control. This is the same phenomenon that forces the control phase `P(α)`
in the general Figure 4.6 construction (`controlledUnitary_eq_abc_cnot_circuit`): a controlled
*diagonal* gate cannot be built from single-qubit gates on the target and `CNOT`s alone.

## Proof

`twoQubit_evolution_ext` reduces the equality to the four computational-basis inputs `|q₁⟩ ⊗ |q₂⟩`
(after collapsing the target `CNOT`-sandwich to `C(R_z(φ))` via `controlledUnitary_rotZGate`).
Control `|0⟩`: both sides are the identity on the target (`CNOT`s idle, `C(R_z(φ))|0,·⟩` untouched,
and `P(φ/2)|0⟩ = |0⟩`). Control `|1⟩`: the target sees `R_z(φ)` and the control picks up the phase
`P(φ/2)|1⟩ = e^{iφ/2}|1⟩`, whose product with the `R_z(φ)` eigenvalues `e^{∓iφ/2}` reproduces the
`P(φ)` eigenvalues `[1, e^{iφ}]` (`Concrete.rotZ_apply_zero_zero` / `_one_one` + `Complex.exp_add`).

The proof uses the controlled phase-shift gate `controlledPhaseShift`
(`AxQM/Postulates/API/ControlledPhaseShift.lean`) and the controlled-rotation results
`controlledUnitary_rotZGate` and `rotZGate_op_apply_qubitBasis`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 5.4 (general angle): decomposition of the controlled phase-shift
gate into single-qubit gates and two `CNOT`s.** For every phase angle `φ`,

`C(P(φ)) = (P(φ/2) ⊗ 1) · (1 ⊗ R_z(φ/2)) · CNOT · (1 ⊗ R_z(-φ/2)) · CNOT`,

with the phase gate `P(φ/2) = phaseShiftGate (φ/2)` on the control, the two `z`-rotations
`R_z(±φ/2) = rotZGate (±φ/2)` on the target, and two `CNOT`s. The `R_k` gate of the quantum Fourier
transform is `R_k = P(2π/2ᵏ)`, so this gives its controlled-gate decomposition (see
`controlledRk_eq_cnot_circuit`).

The target `CNOT`-sandwich `(1 ⊗ R_z(φ/2)) · CNOT · (1 ⊗ R_z(-φ/2)) · CNOT` is the controlled
`z`-rotation `C(R_z(φ))` (`controlledUnitary_rotZGate`); the phase gate on the control supplies the
relative phase `P(φ) = e^{iφ/2} R_z(φ)` that distinguishes the diagonal gate `R_k = P(φ)` from
`R_z(φ)`, and cannot be produced by target gates and `CNOT`s alone. Proved by
`twoQubit_evolution_ext` with casework on the control qubit. -/
theorem controlledPhaseShift_eq_cnot_circuit (φ : ℝ) :
    controlledPhaseShift φ =
      ((phaseShiftGate (φ / 2)).onLeft qubit).comp
        ((((rotZGate (φ / 2)).onRight qubit).comp cnotGate).comp
          (((rotZGate (-(φ / 2))).onRight qubit).comp cnotGate)) := by
  -- The `k`-th diagonal entry of `R_k = P(φ)` equals `e^{iφ/2}` times that of `R_z(φ)`.
  have hscalar : ∀ q : Fin 2,
      (![(1 : ℂ), Complex.exp (↑φ * Complex.I)] q)
        = Concrete.rotZ φ q q * Complex.exp (↑(φ / 2) * Complex.I) := by
    intro q
    fin_cases q
    · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, Concrete.rotZ_apply_zero_zero,
        ← Complex.exp_add]
      norm_num
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Concrete.rotZ_apply_one_one]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  -- Collapse the target `CNOT`-sandwich to the controlled `z`-rotation `C(R_z(φ))`.
  rw [← controlledUnitary_rotZGate]
  apply twoQubit_evolution_ext
  intro q1 q2
  fin_cases q1
  · -- control `|0⟩`: identity on the target, `P(φ/2)|0⟩ = |0⟩`.
    simp only [Fin.isValue, Fin.mk_zero, controlledPhaseShift_eq, Evolution.evolvePure_comp,
      controlledUnitary_evolvePure_ketZero, Evolution.onLeft_evolvePure,
      phaseShiftGate_evolvePure_qubitBasis_zero]
  · -- control `|1⟩`: target sees `R_z(φ)`, control picks up `e^{iφ/2}`; recombine to `P(φ)`.
    simp only [Fin.isValue, Fin.mk_one, controlledPhaseShift_eq, Evolution.evolvePure_comp,
      controlledUnitary_evolvePure_ketOne, Evolution.onLeft_evolvePure]
    apply PureState.ext
    rw [PureState.tmul_vec, PureState.tmul_vec, Evolution.evolvePure_vec, Evolution.evolvePure_vec,
      Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis,
      phaseShiftGate_op_apply_qubitBasis, rotZGate_op_apply_qubitBasis, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [hscalar q2]

/-- **Nielsen & Chuang, Exercise 5.4: decomposition of the controlled-`R_k` gate.** The quantum
Fourier transform's phase gate `R_k = P(2π/2ᵏ) = diag(1, exp(2πi/2ᵏ))` (N&C eq. 5.11) has its
controlled version decomposed into single-qubit gates and two `CNOT`s,

`C(R_k) = (P(π/2ᵏ) ⊗ 1) · (1 ⊗ R_z(π/2ᵏ)) · CNOT · (1 ⊗ R_z(-π/2ᵏ)) · CNOT`,

the `φ = 2π/2ᵏ` instance of `controlledPhaseShift_eq_cnot_circuit` (`φ/2 = π/2ᵏ = 2π/2ᵏ / 2`). This
is the exact two-qubit gate of the QFT circuit expressed with only one-qubit gates and `CNOT`s. -/
theorem controlledRk_eq_cnot_circuit (k : ℕ) :
    controlledPhaseShift (2 * Real.pi / 2 ^ k) =
      ((phaseShiftGate (2 * Real.pi / 2 ^ k / 2)).onLeft qubit).comp
        ((((rotZGate (2 * Real.pi / 2 ^ k / 2)).onRight qubit).comp cnotGate).comp
          (((rotZGate (-(2 * Real.pi / 2 ^ k / 2))).onRight qubit).comp cnotGate)) :=
  controlledPhaseShift_eq_cnot_circuit _

end AxQM
