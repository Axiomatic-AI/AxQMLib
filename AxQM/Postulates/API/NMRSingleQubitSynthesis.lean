/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRControlledZ
import AxQM.Postulates.API.ControlledRotation
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.HadamardGate
import AxQM.Concrete.HadamardRyRx

/-!
# AxQM.Postulates.API — single-qubit gate synthesis from the NMR pulses `R_x`, `R_y`

Gate synthesis for **Nielsen & Chuang Exercise 7.49** (the NMR `SWAP` gate). The two-spin NMR
apparatus offers exactly three building blocks: the `Z₁Z₂`-coupling evolution `e^{-iH/2ℏJ}` and the
single-qubit `90°` rotations `R_x`, `R_y` (there are **no** direct `z`-rotations — that is the whole
point of the "only `R_x`, `R_y`" restriction, which distinguishes Exercise 7.49 from Exercise 7.41
where `R_z` pulses were allowed). This file reduces the two non-NMR single-qubit gates that the
`SWAP` construction needs — the Hadamard `H` and the `z`-rotation `R_z` — to the NMR pulses,
tracking the physically-unobservable global phase these reductions produce.

## What is here

* `globalPhaseGate_comp_globalPhaseGate` / `globalPhaseGate_comp_comm` — the **algebra of the
  global-phase gate**: two global phases compose additively (`e^{iα}·e^{iβ} = e^{i(α+β)}`) and a
  global phase is central (commutes with every gate). These let the accumulated `√i`-type phases of
  the NMR reductions be collected into a single unobservable factor.
* `hadamardGate_eq_globalPhaseGate_comp_rotXGate_comp_rotYGate` — the **Hadamard as an `R_x`/`R_y`
  pulse sequence** at the gate level: `H = e^{iπ/2} · R_x(π) · R_y(π/2)` (Exercise 7.31, lifted from
  the matrix identity `Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotY` to an `Evolution`
  equality).
* `hadamardGate_evolve_eq_rotXGate_comp_rotYGate` — the **channel reading**: as a physical operation
  (`ρ ↦ UρU†`) the Hadamard *is* the pulse sequence `R_x(π) · R_y(π/2)`; the `e^{iπ/2}` phase is
  unobservable and drops out of the conjugation.
* `rotZGate_eq_hadamardGate_comp_rotXGate_comp_hadamardGate` — the **`z`-rotation from an
  `x`-rotation**: `R_z(θ) = H · R_x(θ) · H` (conjugation by the Hadamard swaps the `X` and `Z`
  axes). Composed with the Hadamard reduction above, this expresses every `R_z` used by the NMR
  controlled-`Z`/`SWAP` sequences purely through `R_x`, `R_y` (and unobservable phase).

## Proofs

The statements involve `hadamardGate`, `rotXGate`, `rotYGate`, `rotZGate`, `globalPhaseGate`,
`Evolution.comp` and `.evolve`. The proofs reach through `.op` to the concrete rotation matrices
and the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`, as do those of
`hadamardGate_comp_rotZGate_comp_hadamardGate` and `nmrControlledZSequence`.
-/

open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### Algebra of the global-phase gate -/

/-- **Global phases compose additively:** `(e^{iα}·1) · (e^{iβ}·1) = e^{i(α+β)}·1`, i.e.
`globalPhaseGate α · globalPhaseGate β = globalPhaseGate (α + β)`. The scalar phases multiply,
`e^{iα}·e^{iβ} = e^{i(α+β)}`. -/
theorem globalPhaseGate_comp_globalPhaseGate (α β : ℝ) :
    (globalPhaseGate (S := S) α).comp (globalPhaseGate β) = globalPhaseGate (α + β) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, globalPhaseGate_op, ← ContinuousLinearMap.mul_def]
  rw [smul_mul_smul_comm, mul_one, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **A global phase is central:** the global-phase gate commutes with every evolution `E`,
`globalPhaseGate α · E = E · globalPhaseGate α`. Both sides scale `E`'s operator by the same scalar
`e^{iα}`. -/
theorem globalPhaseGate_comp_comm (α : ℝ) (E : Evolution S) :
    (globalPhaseGate α).comp E = E.comp (globalPhaseGate α) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, globalPhaseGate_op, ← ContinuousLinearMap.mul_def]
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-! ### The Hadamard gate from `R_x`, `R_y` -/

/-- **Nielsen & Chuang, Exercise 7.31 as a gate identity.** The Hadamard gate is the `R_x(π)`,
`R_y(π/2)` pulse sequence up to the global phase `e^{iπ/2} = i`:
`H = e^{iπ/2} · R_x(π) · R_y(π/2)`,
as an equality of qubit `Evolution`s. This lifts the concrete matrix identity
`Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotY` through the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM` (`ℂ`-linear, so it commutes with the `e^{iπ/2}` scalar, and multiplicative,
so a matrix product of rotations becomes a composition of rotation gates). -/
theorem hadamardGate_eq_globalPhaseGate_comp_rotXGate_comp_rotYGate :
    hadamardGate = (globalPhaseGate (Real.pi / 2)).comp
      ((rotXGate Real.pi).comp (rotYGate (Real.pi / 2))) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, hadamardGate_op, rotXGate_op, rotYGate_op, globalPhaseGate_op,
    ← ContinuousLinearMap.mul_def]
  rw [Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotY, map_smul, map_mul, smul_mul_assoc, one_mul]
  rfl

/-- **The Hadamard gate is the `R_x(π) · R_y(π/2)` pulse sequence as a physical operation.** For
every state `ρ`, the Hadamard channel `ρ ↦ HρH†` equals the channel of the pulse sequence
`R_x(π) · R_y(π/2)`: the `e^{iπ/2}` global phase of
`hadamardGate_eq_globalPhaseGate_comp_rotXGate_comp_rotYGate` is unobservable and cancels in the
conjugation. This is the sense in which the Hadamard *is* realised by two NMR rotation pulses. -/
theorem hadamardGate_evolve_eq_rotXGate_comp_rotYGate (ρ : State qubit) :
    hadamardGate.evolve ρ = ((rotXGate Real.pi).comp (rotYGate (Real.pi / 2))).evolve ρ := by
  rw [hadamardGate_eq_globalPhaseGate_comp_rotXGate_comp_rotYGate, globalPhaseGate_comp_evolve]

/-! ### The `z`-rotation from an `x`-rotation -/

/-- **The `z`-rotation as a Hadamard-conjugated `x`-rotation:** `R_z(θ) = H · R_x(θ) · H`. Since the
Hadamard exchanges the `X` and `Z` axes (`H X H = Z`, so `H R_x(θ) H = R_z(θ)`), conjugating an
`x`-rotation by the Hadamard gives the `z`-rotation of the same angle. Obtained by conjugating the
existing identity `hadamardGate_comp_rotZGate_comp_hadamardGate` (`H R_z(θ) H = R_x(θ)`) with a
second pair of Hadamards and collapsing `H · H = 1` (`hadamardGate_comp_self`). Composed with
`hadamardGate_eq_globalPhaseGate_comp_rotXGate_comp_rotYGate`, this expresses `R_z(θ)` — used by the
NMR controlled-`Z`/`SWAP` pulse sequences — through only `R_x`, `R_y` and an unobservable phase. -/
theorem rotZGate_eq_hadamardGate_comp_rotXGate_comp_hadamardGate (θ : ℝ) :
    rotZGate θ = hadamardGate.comp ((rotXGate θ).comp hadamardGate) := by
  rw [← hadamardGate_comp_rotZGate_comp_hadamardGate θ, ← Evolution.comp_assoc,
    ← Evolution.comp_assoc, hadamardGate_comp_self, Evolution.id_comp,
    Evolution.comp_assoc, hadamardGate_comp_self, Evolution.comp_id]

end AxQM
