/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.OpticalHadamard

/-!
# Nielsen & Chuang, Exercise 7.9 (Optical Hadamard gate)

Show the given circuit acts as a Hadamard gate on dual-rail single-photon states.

(N&C p. 292.) In the dual-rail encoding a single photon occupies one of two spatial modes, so the
logical qubit is the two-mode single-photon space `Fin 2 → ℂ`, with logical `|01⟩` the photon in the
top mode `0` and `|10⟩` the photon in the bottom mode `1` — the `{|0_L⟩, |1_L⟩}` manifold on which
N&C write the beamsplitter and phase shifter as `2 × 2` matrices (eq. 7.23, 7.35). The circuit is a
π phase shifter on the top mode followed by an N&C `B(π/4)` beamsplitter; as a matrix it is
`beamSplitter 0 1 (π/2) * phaseMode 0 π`, and it equals the Hadamard matrix `H` up to the overall
phase `e^{iπ} = -1`, which is exactly the stated Hadamard action once the global phase is dropped.

The content is a `2 × 2` complex-matrix identity between named optical-gate matrices —
the beamsplitter/phase-shifter matrices (`AxQM.Concrete.beamSplitter` / `phaseMode`, the
linear-optical elements of `AxQM/Concrete/LinearOpticalElement.lean`) and the
Hadamard matrix (`AxQM.Concrete.hadamardC`).

**Why a matrix identity, unlike the sibling Exercise 7.7.** Exercise 7.7's
circuit is a *phase shifter*, `(phaseShiftGate π).onRight qubit`, which is **diagonal** — a clean
unitary on the whole two-qubit space `qubit ⊗ qubit`, so it is stated as an
`Evolution` on the dual-rail states (`AxQM/NC/Ch7/Exercise7_7.lean`, over
`AxQM/Postulates/API/DualRail.lean`). A
*beamsplitter* is different: it mixes the two modes, and a physical beamsplitter does **not**
preserve the `qubit ⊗ qubit` truncation to `{0, 1}` photons — it takes the two-photon state `|11⟩`
outside the codespace (into `|20⟩, |02⟩`). So there is no canonical beamsplitter `Evolution` on
`qubit ⊗ qubit`; any full-space unitary extending N&C's `B(θ)` would fix `|00⟩, |11⟩` by an *ad hoc*
choice outside the exercise. The exercise's honest content is exactly the action on the
two-dimensional single-photon logical manifold `{|01⟩, |10⟩}` — the `2 × 2` matrix N&C write in
eq. (7.35) — faithfully captured by the matrix identity over the canonical `beamSplitter`. Compare
the matrix treatment of Problem 7.2
(`AxQM/Concrete/LinearOpticalElement.lean`) and the Ch. 2 gate-matrix exercises (e.g. the Hadamard
of Exercise 2.51).

## The formalisation

In `AxQM/Concrete/OpticalHadamard.lean`:

* `opticalHadamardCircuit` — the circuit matrix `beamSplitter 0 1 (π/2) * phaseMode 0 π`.
* `opticalHadamardCircuit_eq_smul_hadamardC` — the headline: `opticalHadamardCircuit = e^{iπ} •
  hadamardC`, the circuit *is* a Hadamard gate up to the overall phase `e^{iπ}`.
* `opticalHadamardCircuit_eq_neg_hadamardC` — the same with the phase evaluated, `= -hadamardC`.
* `opticalHadamardCircuit_mulVec_zeroOne` / `_oneZero` — the explicit dual-rail action,
  `|01⟩ ↦ -(√2)⁻¹(|01⟩ + |10⟩)` and `|10⟩ ↦ -(√2)⁻¹(|01⟩ − |10⟩)`, N&C's stated mapping up to the
  overall phase `-1 = e^{iπ}`.
* `opticalHadamardCircuit_isLinearOpticalProduct` — the circuit is a product of linear-optical
  elements (a beamsplitter and a phase shifter), certifying it is the passive optical circuit drawn.

## Fidelity

"Up to an overall phase" is formalised exactly: the circuit equals `e^{iπ} • H`, so it and the
Hadamard differ only by the global phase `e^{iπ} = -1`, which is physically unobservable — precisely
the qualification N&C attach to the mapping. The beamsplitter mixing angle is N&C's `θ = π/4`
(eq. 7.35, `B = e^{iθY}`); in this library's half-angle `R_y` convention that is
`beamSplitter 0 1 (π/2)`.
-/
