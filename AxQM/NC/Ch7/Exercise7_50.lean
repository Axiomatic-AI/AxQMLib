/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRGroverOracle
import AxQM.NC.Ch7.Exercise7_41

/-!
# Nielsen & Chuang, Exercise 7.50 (NMR Grover oracles for `x₀ = 0, 1, 2`)

*(N&C §7.7.4, p. 339.)*

Find quantum circuits using single-qubit rotations and e^{-iH/2ℏJ} to implement the Grover oracle O
for x0=0,1,2.

## Setup

Grover's search on `n = 2` qubits looks for the marked item `x₀ ∈ {0,1,2,3}`. The **oracle** `O`
flips the sign of the marked computational basis state `|x₀⟩` and fixes the other three, i.e.
`O = diag` with a single `−1`. N&C give the `x₀ = 3` circuit in the text (`O = diag(1,1,1,−1)` is
the controlled-`Z`, realised by `nmrControlledZSequence` — Exercise 7.41); **this file answers the
exercise for `x₀ = 0, 1, 2`.**

The construction is *conjugation of the controlled-`Z` by bit-flips*. Since `controlledZGate` flips
the sign of `|11⟩`, we move the marked corner `|x₀⟩` to `|11⟩` with Pauli-`X` gates, apply the
controlled-`Z`, and move back:

* `x₀ = 0` (`|00⟩`): flip **both** spins — `O = X₁X₂ · CZ · X₁X₂` (`groverOracleZero`);
* `x₀ = 1` (`|01⟩`): flip the **first** spin — `O = X₁ · CZ · X₁` (`groverOracleOne`);
* `x₀ = 2` (`|10⟩`): flip the **second** spin — `O = X₂ · CZ · X₂` (`groverOracleTwo`).

That each of these gates really is the sign-flip oracle is `groverOracle{..}_op_apply_qubitBasis`
(in `AxQM/Postulates/API/NMRGroverOracle.lean`). The **NMR circuit** (`nmrGroverOracle{..}`) uses
exactly the exercise's building blocks: the ideal `CZ` becomes `nmrControlledZSequence`
(single-qubit `R_z` rotations + one free-evolution period `e^{-iH/2ℏJ}` — Exercise 7.41), and
each ideal `X` becomes the physical `180°` pulse `R_x(π)` (a single-qubit rotation, equal to `X` up
to the global phase `−i`).

## What is proved

For each `x₀ ∈ {0,1,2}`:

* `nmrGroverOracle{..}_eq_globalPhaseGate_comp` — the **exact gate identity**: the NMR circuit
  equals the ideal oracle up to a global phase,
  `nmrGroverOracle{..} c t = globalPhase(β)·groverOracle{..}`
  (with `β = −3π/4` for the single-flip cases `x₀ = 1, 2`, and `β = −7π/4` for the double-flip case
  `x₀ = 0`). This is the precise "up to an irrelevant overall phase factor" sense of the N&C
  construction. Proof: rewrite each `R_x(π)` pulse and the `nmrControlledZSequence` into
  `globalPhase·(ideal gate)` form, then collect the (central) global phases of the symmetric
  conjugation to the front (`globalPhaseGate_conj_collect`/`_collect₂`) — real-angle arithmetic,
  no `i²`.
* `nmrGroverOracle{..}_evolve_eq_groverOracle{..}` — the **physics reading** (channel equality): the
  NMR circuit induces the *same state channel* `ρ ↦ U ρ U†` as the ideal oracle, on **every** state
  `ρ`. The residual global phase `β` is physically unobservable (it cancels in the conjugation), so
  the single-qubit rotations plus one free-evolution period realise the oracle — the answer to the
  exercise.

Every statement here is in terms of `nmrGroverOracle{..}`,
`groverOracle{..}`, `globalPhaseGate` and `Evolution.comp`/`evolve`;
the oracle and circuit gates, the sign-flip action and the gate algebra are
in `AxQM/Postulates/API/NMRGroverOracle.lean`.

## Fidelity

The controlled-`Z` is the genuine `controlledZGate`; its NMR realisation is the genuine
`nmrControlledZSequence` (Exercise 7.41), whose only free-evolution ingredient is the
`Observable.propagator` of the `Z₁Z₂` coupling Hamiltonian; the bit-flips are the genuine physical
`rotXGate π` pulses (not the idealised `pauliXGate` — the `−i` per pulse is carried honestly and
absorbed into the single global phase `β`). No hypotheses beyond `c·t = π/4` (the "one evolution
period" `1/2J` of the figure).
-/

noncomputable section

namespace AxQM

/-- **The NMR controlled-`Z` sequence equals the controlled-`Z` gate up to the global phase
`e^{iπ/4} = √i`:** `nmrControlledZSequence c t = globalPhase(π/4)·controlledZGate` when `c·t = π/4`.
The positive-time form of N&C's construction (Exercise 7.41), obtained by moving the `√(-i)` global
phase of `nmrControlledZ_globalPhase_eq_controlledZGate` to the other side (`gp(π/4)·gp(-π/4) = 1`).
The reusable form the Grover-oracle circuits build on. -/
theorem nmrControlledZSequence_eq_globalPhaseGate_comp (c t : ℝ) (h : c * t = Real.pi / 4) :
    nmrControlledZSequence c t = (globalPhaseGate (Real.pi / 4)).comp controlledZGate := by
  have h1 := nmrControlledZ_globalPhase_eq_controlledZGate c t h
  rw [← h1, ← Evolution.comp_assoc, globalPhaseGate_comp_globalPhaseGate,
    show Real.pi / 4 + -(Real.pi / 4) = 0 by ring, globalPhaseGate_zero, Evolution.id_comp]

/-! ### `x₀ = 0` -/

/-- **Exercise 7.50, `x₀ = 0` — the NMR circuit equals the oracle up to a global phase.** The
`R_x(π)`-pulse / `nmrControlledZSequence` circuit `nmrGroverOracleZero c t` equals the ideal oracle
`groverOracleZero` (`= diag(-1,1,1,1)`, the sign flip of `|00⟩`) up to the global phase
`e^{-i7π/4}`. Proof: rewrite the four `R_x(π)` pulses and the coupled evolution into
`globalPhase·(ideal gate)` form, then collect the five (central) global phases of the two-pulse
conjugation to the front via `globalPhaseGate_conj_collect₂`. -/
theorem nmrGroverOracleZero_eq_globalPhaseGate_comp (c t : ℝ) (h : c * t = Real.pi / 4) :
    nmrGroverOracleZero c t = (globalPhaseGate (-(7 * Real.pi / 4))).comp groverOracleZero := by
  rw [nmrGroverOracleZero, rotXGate_pi_onLeft_eq, rotXGate_pi_onRight_eq,
    nmrControlledZSequence_eq_globalPhaseGate_comp c t h, globalPhaseGate_conj_collect₂,
    show -(Real.pi / 2) + -(Real.pi / 2) + Real.pi / 4 + -(Real.pi / 2) + -(Real.pi / 2)
      = -(7 * Real.pi / 4) by ring, groverOracleZero]

/-- **Exercise 7.50, `x₀ = 0` — the channel reading.** `nmrGroverOracleZero c t` induces the *same
state channel* `ρ ↦ U ρ U†` as the ideal `x₀ = 0` oracle `groverOracleZero`, on every state `ρ`: the
global phase `e^{-i7π/4}` is unobservable, so the circuit (single-qubit rotations + one free
`J`-coupling period) realises the oracle. -/
theorem nmrGroverOracleZero_evolve_eq_groverOracleZero (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrGroverOracleZero c t).evolve ρ = groverOracleZero.evolve ρ := by
  rw [nmrGroverOracleZero_eq_globalPhaseGate_comp c t h, globalPhaseGate_comp_evolve]

/-! ### `x₀ = 1` -/

/-- **Exercise 7.50, `x₀ = 1` — the NMR circuit equals the oracle up to a global phase.** The
`R_x(π)₁`-conjugated `nmrControlledZSequence` circuit `nmrGroverOracleOne c t` equals the ideal
oracle `groverOracleOne` (`= diag(1,-1,1,1)`, the sign flip of `|01⟩`) up to the global phase
`e^{-i3π/4}` (collected from the three central phases of the single-pulse conjugation). -/
theorem nmrGroverOracleOne_eq_globalPhaseGate_comp (c t : ℝ) (h : c * t = Real.pi / 4) :
    nmrGroverOracleOne c t = (globalPhaseGate (-(3 * Real.pi / 4))).comp groverOracleOne := by
  rw [nmrGroverOracleOne, rotXGate_pi_onLeft_eq,
    nmrControlledZSequence_eq_globalPhaseGate_comp c t h, globalPhaseGate_conj_collect,
    show -(Real.pi / 2) + Real.pi / 4 + -(Real.pi / 2) = -(3 * Real.pi / 4) by ring,
    groverOracleOne]

/-- **Exercise 7.50, `x₀ = 1` — the channel reading.** `nmrGroverOracleOne c t` induces the same
state channel as the ideal `x₀ = 1` oracle `groverOracleOne`, on every state `ρ` — the global phase
`e^{-i3π/4}` cancels in the conjugation. -/
theorem nmrGroverOracleOne_evolve_eq_groverOracleOne (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrGroverOracleOne c t).evolve ρ = groverOracleOne.evolve ρ := by
  rw [nmrGroverOracleOne_eq_globalPhaseGate_comp c t h, globalPhaseGate_comp_evolve]

/-! ### `x₀ = 2` -/

/-- **Exercise 7.50, `x₀ = 2` — the NMR circuit equals the oracle up to a global phase.** The
`R_x(π)₂`-conjugated `nmrControlledZSequence` circuit `nmrGroverOracleTwo c t` equals the ideal
oracle `groverOracleTwo` (`= diag(1,1,-1,1)`, the sign flip of `|10⟩`) up to the global phase
`e^{-i3π/4}`. -/
theorem nmrGroverOracleTwo_eq_globalPhaseGate_comp (c t : ℝ) (h : c * t = Real.pi / 4) :
    nmrGroverOracleTwo c t = (globalPhaseGate (-(3 * Real.pi / 4))).comp groverOracleTwo := by
  rw [nmrGroverOracleTwo, rotXGate_pi_onRight_eq,
    nmrControlledZSequence_eq_globalPhaseGate_comp c t h, globalPhaseGate_conj_collect,
    show -(Real.pi / 2) + Real.pi / 4 + -(Real.pi / 2) = -(3 * Real.pi / 4) by ring,
    groverOracleTwo]

/-- **Exercise 7.50, `x₀ = 2` — the channel reading.** `nmrGroverOracleTwo c t` induces the same
state channel as the ideal `x₀ = 2` oracle `groverOracleTwo`, on every state `ρ` — the global phase
`e^{-i3π/4}` cancels in the conjugation. -/
theorem nmrGroverOracleTwo_evolve_eq_groverOracleTwo (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrGroverOracleTwo c t).evolve ρ = groverOracleTwo.evolve ρ := by
  rw [nmrGroverOracleTwo_eq_globalPhaseGate_comp c t h, globalPhaseGate_comp_evolve]

end AxQM
