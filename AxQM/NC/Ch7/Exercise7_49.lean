/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRSwap
import AxQM.Postulates.API.SwapCircuit
import AxQM.NC.Ch4.Exercise4_17
import AxQM.NC.Ch7.Exercise7_41

/-!
# Nielsen & Chuang, Exercise 7.49 (NMR swap gate)

*(N&C §7.7.3, p. 338–339.)*

NMR swap gate: construct a quantum circuit using e^{-iH/2ℏJ}, R_x, R_y to implement a swap
operation.

## The construction

The three building blocks are the `Z₁Z₂`-coupling evolution `e^{-iH/2ℏJ}` (one "free evolution
period", the coupled propagator `e^{-i c Z₁Z₂ t}` at `c·t = π/4`) and the `90°` rotations `R_x`,
`R_y`. Crucially there are **no** direct `z`-rotations — that "using only `R_x`, `R_y`" is what
separates this from Exercise 7.41, where `R_z` pulses were permitted. Starting from Figure 1.7,
`SWAP = CNOT · reversedCNOT · CNOT`, every gate reduces to the three building blocks:

* **`SWAP → 3 CNOT`** (Figure 1.7): `swapGate_eq_cnot_reversedCnot_cnot`.
* **`CNOT → CZ + H`**: `CNOT = (1⊗H)·CZ·(1⊗H)` (Exercise 4.17,
  `cnotGate_eq_hadamard_conj_controlledZGate`) and, mirrored, `reversedCNOT = (H⊗1)·CZ·(H⊗1)`
  (`reversedCnotGate_eq_hadamard_conj_controlledZGate`).
* **`CZ → coupling + R_z`**: `CZ = √(-i) · e^{-iZ₁Z₂π/4} · R_z(-π/2)₁ · R_z(-π/2)₂` (Exercise 7.41,
  `nmrControlledZ_globalPhase_eq_controlledZGate`).
* **`H → R_x, R_y`** and **`R_z → R_x, R_y`**: `H = e^{iπ/2}·R_x(π)·R_y(π/2)` (Exercise 7.31) and
  `R_z(θ) = H·R_x(θ)·H` (`AxQM/Postulates/API/NMRSingleQubitSynthesis.lean`), so the
  `z`-rotations of the controlled-`Z` sequence also become `R_x`/`R_y` pulses.

Each reduction holds only *up to a physically-irrelevant overall phase factor* (N&C's own wording),
so they are threaded through the congruence `GlobalPhaseEquiv` (`E ≈ F ⟺ E = e^{iα}·F`,
`AxQM/Postulates/API/NMRSwap.lean`), which lets the phases accumulate silently and cancel in one
final step. The assembled `NMRSwap.swapCircuit`, built from `R_x`, `R_y`, and the coupling alone,
is the answer.

## What is proved

* `nmrSwapCircuit_evolve_eq_swap` — the **physics reading** (the channel): for `c·t = π/4`, the pure
  `R_x`/`R_y`/coupling circuit `NMRSwap.swapCircuit c t` induces the *same state channel*
  `ρ ↦ U ρ U†` as the `SWAP` gate, on every state.
* `nmrSwapCircuit_eq_swap_up_to_globalPhase` — the stronger **gate identity up to phase**: `SWAP =
  e^{iα}·NMRSwap.swapCircuit c t` for some real `α`, reifying "not quite in the perfect form ... up
  to an irrelevant overall phase factor"; the channel reading is its unobservable-phase corollary.

The intermediate block reductions `controlledZGate`/`cnotGate`/`reversedCnotGate`/`swapGate`
`_globalPhaseEquiv` (each gate `≈` its pure circuit) are proved here using the Exercise 7.41/4.17
identities; the phase machinery and circuits are in `AxQM/Postulates/API/NMRSwap.lean`.

## Fidelity

The target is the genuine `Evolution.swap`; the circuit uses *only* the genuine coupling propagator
`Observable.propagator` of `couplingZZHamiltonian` and the genuine `rotXGate` / `rotYGate` — no
`rotZGate`, `hadamardGate`, `controlledZGate`, or `cnotGate` appears in `NMRSwap.swapCircuit` as an
opaque block; each is expanded to the three building blocks. The global phases are carried
explicitly, and the only hypothesis is `c·t = π/4` (one free evolution period).
-/

noncomputable section

namespace AxQM

/-- **The controlled-`Z` gate is realised by the pure `R_x`/`R_y`/coupling circuit up to a global
phase** (`c·t = π/4`). Chains Exercise 7.41 (`controlledZGate ≈ nmrControlledZSequence`) with the
`R_z`-elimination `nmrControlledZSequence ≈ NMRSwap.controlledZ`. -/
theorem controlledZGate_globalPhaseEquiv (c t : ℝ) (h : c * t = Real.pi / 4) :
    GlobalPhaseEquiv controlledZGate (NMRSwap.controlledZ c t) := by
  refine GlobalPhaseEquiv.trans ?_ (NMRSwap.nmrControlledZSequence_globalPhaseEquiv c t)
  exact ⟨-(Real.pi / 4), (nmrControlledZ_globalPhase_eq_controlledZGate c t h).symm⟩

/-- **The `CNOT` gate is realised by the pure `R_x`/`R_y`/coupling circuit up to a global phase**
(`c·t = π/4`). From `CNOT = (1⊗H)·CZ·(1⊗H)` (Exercise 4.17) with `H`, `CZ` replaced by their pure
circuits via the congruence. -/
theorem cnotGate_globalPhaseEquiv (c t : ℝ) (h : c * t = Real.pi / 4) :
    GlobalPhaseEquiv cnotGate (NMRSwap.cnot c t) := by
  rw [cnotGate_eq_hadamard_conj_controlledZGate]
  exact (NMRSwap.hadamard_globalPhaseEquiv.onRight qubit).comp
    ((controlledZGate_globalPhaseEquiv c t h).comp
      (NMRSwap.hadamard_globalPhaseEquiv.onRight qubit))

/-- **The reversed `CNOT` is realised by the pure `R_x`/`R_y`/coupling circuit up to a global
phase.** From `reversedCNOT = (H⊗1)·CZ·(H⊗1)` with `H`, `CZ` replaced by their pure circuits, i.e.
`GlobalPhaseEquiv reversedCnotGate (NMRSwap.reversedCnot c t)` when `c·t = π/4`. -/
theorem reversedCnotGate_globalPhaseEquiv (c t : ℝ) (h : c * t = Real.pi / 4) :
    GlobalPhaseEquiv reversedCnotGate (NMRSwap.reversedCnot c t) := by
  rw [reversedCnotGate_eq_hadamard_conj_controlledZGate]
  exact (NMRSwap.hadamard_globalPhaseEquiv.onLeft qubit).comp
    ((controlledZGate_globalPhaseEquiv c t h).comp
      (NMRSwap.hadamard_globalPhaseEquiv.onLeft qubit))

/-- **The `SWAP` gate is realised by the pure `R_x`/`R_y`/coupling circuit up to a global phase**
(`c·t = π/4`). From Figure 1.7 (`SWAP = CNOT·reversedCNOT·CNOT`) with each `CNOT` replaced by its
pure circuit via the congruence. -/
theorem swapGate_globalPhaseEquiv (c t : ℝ) (h : c * t = Real.pi / 4) :
    GlobalPhaseEquiv Evolution.swap (NMRSwap.swapCircuit c t) := by
  rw [swapGate_eq_cnot_reversedCnot_cnot]
  exact (cnotGate_globalPhaseEquiv c t h).comp
    ((reversedCnotGate_globalPhaseEquiv c t h).comp (cnotGate_globalPhaseEquiv c t h))

/-- **Nielsen & Chuang, Exercise 7.49 — the exact gate identity up to phase.** For one period of
`Z₁Z₂`-coupled evolution with `c·t = π/4`, the pure `R_x`/`R_y`/coupling circuit
`NMRSwap.swapCircuit c t` equals the `SWAP` gate up to a single overall global phase `e^{iα}`:
`SWAP = e^{iα} · NMRSwap.swapCircuit c t`. This is the sense in which the NMR pulse sequence
realises `SWAP` "up to an irrelevant overall phase factor" — the phase is the accumulated
`√i`/`e^{iπ/2}` factors of the controlled-`Z` and Hadamard reductions. -/
theorem nmrSwapCircuit_eq_swap_up_to_globalPhase (c t : ℝ) (h : c * t = Real.pi / 4) :
    ∃ α : ℝ, Evolution.swap = (globalPhaseGate α).comp (NMRSwap.swapCircuit c t) :=
  swapGate_globalPhaseEquiv c t h

/-- **Nielsen & Chuang, Exercise 7.49 — the physics reading (channel equality).** For one period of
`Z₁Z₂`-coupled evolution with `c·t = π/4`, the circuit `NMRSwap.swapCircuit c t` — built from
**only** the coupling propagator `e^{-iH/2ℏJ}` and the `90°` rotations `R_x`, `R_y` — induces the
*same state
channel* `ρ ↦ U ρ U†` as the `SWAP` gate, on every state `ρ`. The overall global phase of the gate
identity is physically unobservable (it cancels in the conjugation), so this pulse sequence realises
a `SWAP` between the two coupled spins — the answer to the exercise. -/
theorem nmrSwapCircuit_evolve_eq_swap (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (NMRSwap.swapCircuit c t).evolve ρ = Evolution.swap.evolve ρ :=
  ((swapGate_globalPhaseEquiv c t h).evolve ρ).symm

end AxQM
