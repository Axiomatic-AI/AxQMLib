/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRSingleQubitSynthesis

/-!
# AxQM.Postulates.API — the pure-`R_x`/`R_y` SWAP circuit (N&C Exercise 7.49)

Statements for **Nielsen & Chuang Exercise 7.49** (the NMR `SWAP` gate): build a `SWAP` using
**only** the coupling evolution `e^{-iH/2ℏJ}` and the `90°` rotations `R_x`, `R_y`, starting from
the three-`CNOT` circuit of Figure 1.7. The standard reductions produce Hadamards, `z`-rotations,
and controlled-`Z`s each realised only *up to a physically-irrelevant global phase* (N&C's own
words), so this file supplies the bookkeeping that makes those phases cancel automatically.

## What is here

* `GlobalPhaseEquiv E F` — `∃ α, E = e^{iα}·F`, "`E` and `F` differ by a global phase". Its closure
  lemmas (`refl`/`symm`/`trans`/`comp`/`onLeft`/`onRight`) make it a congruence, and `evolve` turns
  it into channel equality `E.evolve ρ = F.evolve ρ`, so the reduction `SWAP → 3 CNOT → CZ + H →
  R_x, R_y` telescopes with **no explicit phase arithmetic**.
* `NMRSwap.{hadamard, rotZ, controlledZ, cnot, reversedCnot, swapCircuit}` — the explicit circuits
  built **only** from `R_x`, `R_y`, and the coupling propagator: `H = R_x(π)·R_y(π/2)` (Ex 7.31),
  `R_z(θ) = H·R_x(θ)·H`, the controlled-`Z` (Ex 7.41 with its `R_z` pulses expanded), the two `CNOT`
  orientations `(1⊗H)·CZ·(1⊗H)` / `(H⊗1)·CZ·(H⊗1)`, and the three-`CNOT` `SWAP` of Figure 1.7.
* `NMRSwap.{hadamard, rotZ, nmrControlledZSequence}_globalPhaseEquiv` — each pure circuit differs by
  a global phase from the gate it realises (the `NC/`-independent steps; the controlled-`Z`, `CNOT`,
  and `SWAP` steps, which invoke Ex 7.41/4.17 in `NC/`, finish in `NC/Ch7/Exercise7_49.lean`).
-/

open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The "differ by a global phase" relation

The structural lemmas `globalPhaseGate_zero` / `globalPhaseGate_onLeft` / `globalPhaseGate_onRight`
now live in their canonical home `Postulates/API/NMRControlledZ` (beside `globalPhaseGate`); they
are used below through that import. -/

/-- **`E` and `F` differ by a global phase:** `∃ α, E = e^{iα} · F`. Since a global phase is
physically unobservable, `GlobalPhaseEquiv E F` implies `E` and `F` induce the *same channel*
(`GlobalPhaseEquiv.evolve`). Being a congruence (below), it accumulates the up-to-phase reductions
of Exercise 7.49 (`SWAP → 3 CNOT → CZ + H → R_x, R_y`) into one unobservable factor. -/
def GlobalPhaseEquiv {S : QSystem} (E F : Evolution S) : Prop :=
  ∃ α : ℝ, E = (globalPhaseGate α).comp F

/-- `GlobalPhaseEquiv` is reflexive (phase `0`). -/
theorem GlobalPhaseEquiv.refl {S : QSystem} (E : Evolution S) : GlobalPhaseEquiv E E :=
  ⟨0, by rw [globalPhaseGate_zero, Evolution.id_comp]⟩

/-- `GlobalPhaseEquiv` is symmetric (negate the phase). -/
theorem GlobalPhaseEquiv.symm {S : QSystem} {E F : Evolution S} (h : GlobalPhaseEquiv E F) :
    GlobalPhaseEquiv F E := by
  obtain ⟨α, rfl⟩ := h
  refine ⟨-α, ?_⟩
  rw [← Evolution.comp_assoc, globalPhaseGate_comp_globalPhaseGate, neg_add_cancel,
    globalPhaseGate_zero, Evolution.id_comp]

/-- `GlobalPhaseEquiv` is transitive (add the phases). -/
theorem GlobalPhaseEquiv.trans {S : QSystem} {E F G : Evolution S}
    (h₁ : GlobalPhaseEquiv E F) (h₂ : GlobalPhaseEquiv F G) : GlobalPhaseEquiv E G := by
  obtain ⟨α, rfl⟩ := h₁
  obtain ⟨β, rfl⟩ := h₂
  exact ⟨α + β, by rw [← Evolution.comp_assoc, globalPhaseGate_comp_globalPhaseGate]⟩

/-- **`GlobalPhaseEquiv` is a congruence for composition:** if `E ≈ E'` and `F ≈ F'` then
`E·F ≈ E'·F'`. The two global phases collect to the front (centrality of `globalPhaseGate`,
`globalPhaseGate_comp_comm`) and merge (`globalPhaseGate_comp_globalPhaseGate`). -/
theorem GlobalPhaseEquiv.comp {S : QSystem} {E E' F F' : Evolution S}
    (h₁ : GlobalPhaseEquiv E E') (h₂ : GlobalPhaseEquiv F F') :
    GlobalPhaseEquiv (E.comp F) (E'.comp F') := by
  obtain ⟨α, rfl⟩ := h₁
  obtain ⟨β, rfl⟩ := h₂
  refine ⟨α + β, ?_⟩
  rw [Evolution.comp_assoc, ← Evolution.comp_assoc E' (globalPhaseGate β) F',
    ← globalPhaseGate_comp_comm β E', Evolution.comp_assoc (globalPhaseGate β) E' F',
    ← Evolution.comp_assoc (globalPhaseGate α) (globalPhaseGate β) (E'.comp F'),
    globalPhaseGate_comp_globalPhaseGate]

/-- **`GlobalPhaseEquiv` is preserved by the right embedding:** `E ≈ F ⟹ (1⊗E) ≈ (1⊗F)`. The phase
`(globalPhaseGate α).onRight S` is again the same global phase (`globalPhaseGate_onRight`). -/
theorem GlobalPhaseEquiv.onRight {T : QSystem} {E F : Evolution T}
    (h : GlobalPhaseEquiv E F) (S : QSystem) :
    GlobalPhaseEquiv (E.onRight S) (F.onRight S) := by
  obtain ⟨α, rfl⟩ := h
  exact ⟨α, by rw [← Evolution.onRight_comp, globalPhaseGate_onRight]⟩

/-- **`GlobalPhaseEquiv` is preserved by the left embedding:** `E ≈ F ⟹ (E⊗1) ≈ (F⊗1)`. Mirror of
`GlobalPhaseEquiv.onRight`. -/
theorem GlobalPhaseEquiv.onLeft {S : QSystem} {E F : Evolution S}
    (h : GlobalPhaseEquiv E F) (T : QSystem) :
    GlobalPhaseEquiv (E.onLeft T) (F.onLeft T) := by
  obtain ⟨α, rfl⟩ := h
  exact ⟨α, by rw [← Evolution.onLeft_comp, globalPhaseGate_onLeft]⟩

/-- **A global-phase difference is invisible to the channel:** `GlobalPhaseEquiv E F` implies
`E.evolve ρ = F.evolve ρ` for every state `ρ` — the phase cancels in the conjugation
(`globalPhaseGate_comp_evolve`). This is the step that turns the accumulated phases of the Exercise
7.49 reduction into an exact channel equality. -/
theorem GlobalPhaseEquiv.evolve {S : QSystem} {E F : Evolution S}
    (h : GlobalPhaseEquiv E F) (ρ : State S) : E.evolve ρ = F.evolve ρ := by
  obtain ⟨α, rfl⟩ := h
  exact globalPhaseGate_comp_evolve α F ρ

/-! ### The pure-`R_x`/`R_y` circuits -/

namespace NMRSwap

/-- **The Hadamard gate as an `R_x`/`R_y` pulse sequence** (N&C Exercise 7.31):
`R_x(π) · R_y(π/2)`. Equals `hadamardGate` up to the global phase `e^{iπ/2}`
(`hadamard_globalPhaseEquiv`). -/
def hadamard : Evolution qubit := (rotXGate Real.pi).comp (rotYGate (Real.pi / 2))

/-- **The `z`-rotation from `R_x`, `R_y`:** `H · R_x(θ) · H` with the Hadamards `H` themselves
expanded to `R_x`/`R_y` pulses (`NMRSwap.hadamard`). Equals `rotZGate θ` up to a global phase
(`rotZ_globalPhaseEquiv`); this removes the `z`-rotations of the Exercise 7.41 controlled-`Z`. -/
def rotZ (θ : ℝ) : Evolution qubit := hadamard.comp ((rotXGate θ).comp hadamard)

/-- **The controlled-`Z` from coupling + `R_x`/`R_y`:** one period of `Z₁Z₂`-coupled evolution
`e^{-i c Z₁Z₂ t}` followed by the pure-`R_x`/`R_y` `z`-rotation `NMRSwap.rotZ (-π/2)` on each spin —
the Exercise 7.41 sequence with its `R_z` pulses expanded. Equals `controlledZGate` up to a global
phase when `c·t = π/4` (see `NC/Ch7/Exercise7_49.lean`). -/
def controlledZ (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((couplingZZHamiltonian c).propagator 1 0 t).comp
    (((rotZ (-(Real.pi / 2))).onLeft qubit).comp ((rotZ (-(Real.pi / 2))).onRight qubit))

/-- **The `CNOT` from coupling + `R_x`/`R_y`:** `(1⊗H) · CZ · (1⊗H)` (N&C Exercise 4.17), with the
Hadamards and the controlled-`Z` realised from `R_x`, `R_y`, and the coupling (`NMRSwap.hadamard`,
`NMRSwap.controlledZ`). The two Hadamards act on the *target* (right) qubit. -/
def cnot (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (hadamard.onRight qubit).comp ((controlledZ c t).comp (hadamard.onRight qubit))

/-- **The reversed `CNOT` from coupling + `R_x`/`R_y`:** `(H⊗1) · CZ · (H⊗1)` — the `CNOT`
controlled on the second qubit, with the Hadamards on the *first* (target) qubit
(`reversedCnotGate_eq_hadamard_conj_controlledZGate`). -/
def reversedCnot (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (hadamard.onLeft qubit).comp ((controlledZ c t).comp (hadamard.onLeft qubit))

/-- **The NMR `SWAP` circuit** (N&C Exercise 7.49): the three-`CNOT` circuit of Figure 1.7,
`CNOT · reversedCNOT · CNOT`, with every `CNOT` realised from the coupling and `R_x`, `R_y` only.
When `c·t = π/4` it induces the `SWAP` channel (`nmrSwapCircuit_evolve_eq_swap`, in
`NC/Ch7/Exercise7_49.lean`). -/
def swapCircuit (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (cnot c t).comp ((reversedCnot c t).comp (cnot c t))

/-! ### The `NC/`-independent global-phase reductions -/

/-- **The Hadamard circuit realises `hadamardGate` up to a global phase.** `hadamardGate =
e^{iπ/2} · (R_x(π)·R_y(π/2))` (N&C Exercise 7.31), i.e.
`GlobalPhaseEquiv hadamardGate NMRSwap.hadamard`. -/
theorem hadamard_globalPhaseEquiv : GlobalPhaseEquiv hadamardGate hadamard :=
  ⟨Real.pi / 2, hadamardGate_eq_globalPhaseGate_comp_rotXGate_comp_rotYGate⟩

/-- **The `z`-rotation circuit realises `rotZGate θ` up to a global phase.** From
`rotZGate θ = H · R_x(θ) · H` (`rotZGate_eq_hadamardGate_comp_rotXGate_comp_hadamardGate`) with each
`H` replaced by its `R_x`/`R_y` sequence via `hadamard_globalPhaseEquiv` — the congruence collects
the two Hadamard phases automatically. -/
theorem rotZ_globalPhaseEquiv (θ : ℝ) : GlobalPhaseEquiv (rotZGate θ) (rotZ θ) := by
  rw [rotZGate_eq_hadamardGate_comp_rotXGate_comp_hadamardGate]
  exact hadamard_globalPhaseEquiv.comp
    ((GlobalPhaseEquiv.refl _).comp hadamard_globalPhaseEquiv)

/-- **The pure controlled-`Z` circuit differs by a global phase from the Exercise 7.41 sequence.**
`NMRSwap.controlledZ` is `nmrControlledZSequence` with its two `R_z(-π/2)` pulses replaced by the
`R_x`/`R_y` circuit `NMRSwap.rotZ (-π/2)`; the two replacements each contribute a global phase,
which
the congruence carries. Chained with Exercise 7.41 (in `NC/Ch7/Exercise7_49.lean`) this grounds the
controlled-`Z` in `R_x`, `R_y`, and the coupling. -/
theorem nmrControlledZSequence_globalPhaseEquiv (c t : ℝ) :
    GlobalPhaseEquiv (nmrControlledZSequence c t) (controlledZ c t) := by
  unfold nmrControlledZSequence controlledZ
  exact (GlobalPhaseEquiv.refl _).comp
    (((rotZ_globalPhaseEquiv _).onLeft qubit).comp ((rotZ_globalPhaseEquiv _).onRight qubit))

end NMRSwap

end AxQM
