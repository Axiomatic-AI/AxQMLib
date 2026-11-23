/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeutschAlgorithm
import AxQM.Postulates.API.Beamsplitter
import AxQM.NC.Ch4.Exercise4_17
import AxQM.NC.Ch7.Exercise7_23

/-!
# Nielsen & Chuang, Exercise 7.13 (optical Deutsch–Jozsa quantum circuit)

*(N&C p. 294.)*

Optical Deutsch-Jozsa quantum circuit for single-photon dual-rail states using beamsplitters/phase
shifters/Kerr media.

**The algorithm (N&C §1.4.3/§1.4.4).** The one-bit Deutsch–Jozsa problem is *Deutsch's problem*:
decide whether `f : {0,1} → {0,1}` is *constant* or *balanced* with a **single** query. Deutsch's
circuit is `(H ⊗ I) · U_f · (H ⊗ H)` applied to `|0⟩ ⊗ |1⟩`; measuring the query (first) qubit
returns `f(0) ⊕ f(1)`, which is `0` for the two constant functions and `1` for the two balanced
functions (N&C eq. 1.45). The four functions and their oracles `U_f|x, y⟩ = |x, y ⊕ f(x)⟩` are:

* `deutschOracleConstZero` — `f ≡ 0` (constant): `U_f = I`.
* `deutschOracleConstOne`  — `f ≡ 1` (constant): `U_f = I ⊗ X` (flip the answer rail).
* `deutschOracleIdentity`  — `f = id` (balanced): `U_f = CNOT`.
* `deutschOracleNegation`  — `f = ¬` (balanced): `U_f = (X ⊗ I) · CNOT · (X ⊗ I)`, the
  `0`-controlled `NOT`.

## The formalisation

The two logical qubits (query and answer) carry Deutsch's circuit `(H ⊗ I) · U_f · (H ⊗ H)`; the
four oracles `U_f`, their XOR-oracle correctness, and the measured `f(0) ⊕ f(1)` outcome are stated
at that two-qubit gate level. Part (1)'s **optical construction** is also formalised (a real
optical element — `phaseShiftGate`/`beamSplitterDualRail` on `dualRail` states — appears in each
statement): the balanced oracles' *entangling gate* is an actual optical **Kerr** object and the
**Hadamards** are an actual optical beamsplitter
(`opticalHadamardDualRail = beamSplitterDualRail(π/4) ∘ (1 ⊗ P(π))`, a beamsplitter and a `π` phase
shifter, `AxQM/Postulates/API/Beamsplitter.lean`), whose dual-rail action is the Hadamard up to
global phase (N&C Ex. 7.9). It also formalises **part (2)** — *why no phase shifters are
necessary*: the Hadamard can be built from a beamsplitter and a **mirror** instead
(`opticalHadamardMirror = SWAP ∘ B(π/4)`), realising it *exactly* with no phase shifter, so every
gate of the four `U_f` is a beamsplitter, a mirror, or a Kerr medium. All three parts of the
exercise carry Lean content: part (1) (the four `U_f`, their oracle correctness, and each gate's
optical realisation), part (2) (no phase shifters), and part (3) (interference, the `_bornProb`
outcomes). The full four-mode *assembly* of the circuit on `(qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)` is a
not formalised (see the Design notes): each claim is stated at full
strength and every optical ingredient is an `Evolution`.

* `deutschOracleConstZero_isDeutschOracle` … `deutschOracleNegation_isDeutschOracle` — **part (1)**:
  each of the four gates is the XOR oracle `U_f|x, y⟩ = |x, y ⊕ f(x)⟩` for its function `f`
  (`IsDeutschOracle`), verified against the gate truth tables.
* `opticalKerrGate_zero_pi_eq_controlledZGate` — **part (1), the Kerr entangling gate**: the actual
  optical Kerr gate `opticalKerrGate 0 0 π` (N&C's physical two-photon model, eq. 7.87 / Exercise
  7.23) with no single-photon phases and `χL = π` *is* the controlled-`Z` `K = diag(1,1,1,−1)`, i.e.
  the §7.4.1 Kerr medium `K = e^{iχL a†a b†b}` at `χL = π` (eqs. 7.42–7.45).
* `deutschOracleIdentity_eq_kerrGate_conj_hadamard` /
  `deutschOracleNegation_eq_kerrGate_conj_hadamard_mirror` — **part (1), the two balanced oracles
  from the Kerr gate**: the identity oracle's `CNOT = (I ⊗ H) · K · (I ⊗ H)` (N&C eq. 7.46) with the
  entangling gate the optical Kerr `K = opticalKerrGate 0 0 π` (not a bare `controlledZGate`), and
  the negation oracle that circuit conjugated by query-rail `X` **mirrors**. With the constant
  oracles (`I`, `I ⊗ X`) taking no entangling gate, the entangling optical content of all four `U_f`
  is carried by a Lean statement.
* `opticalHadamardDualRail_evolvePure_dualRailZero` / `_dualRailOne` — **part (1), the Hadamards as
  beamsplitters**: the optical Hadamard `opticalHadamardDualRail` — a balanced beamsplitter after a
  `π` phase shifter (`AxQM/Postulates/API/Beamsplitter.lean`) — sends the dual-rail logical basis to
  `|01⟩ ↦ -(|01⟩ + |10⟩)/√2` and `|10⟩ ↦ -(|01⟩ - |10⟩)/√2`, i.e. N&C's stated Hadamard action
  `|01⟩ → (|01⟩ + |10⟩)/√2`, `|10⟩ → (|01⟩ - |10⟩)/√2` (Ex. 7.9) up to the global phase
  `e^{iπ} = -1`. This realises the `I ⊗ H` factors of the Kerr `CNOT` (eq. 7.46) as a real
  **beamsplitter**, alongside the Kerr entangling gate. The general superposition action is
  `opticalHadamardDualRail_evolvePure_dualRail`.
* `opticalHadamardMirror_evolvePure_dualRailZero` / `_dualRailOne` — **part (2)**.
  The phase-shifter-free optical Hadamard `opticalHadamardMirror = SWAP ∘ B(π/4)` (a beamsplitter
  and a **mirror**, `AxQM/Postulates/API/Beamsplitter.lean`) sends the dual-rail basis to
  `|01⟩ ↦ (|01⟩ + |10⟩)/√2` and `|10⟩ ↦ (|01⟩ - |10⟩)/√2` — N&C's *exact* Hadamard action (Ex. 7.9),
  now with **no** global phase. The mirror is `Evolution.swap`, the same dual-rail `X` the oracles
  already use, so trading it for the `π` phase shifter of `opticalHadamardDualRail` shows no phase
  shifter is necessary. The general action is `opticalHadamardMirror_evolvePure_dualRail`.
* `deutschOracleConstZero_bornProb` … `deutschOracleNegation_bornProb` — **the outcome**: after
  Deutsch's circuit, measuring the query qubit in the computational basis yields `f(0) ⊕ f(1)` with
  probability `1` — `0` for the two constant oracles, `1` for the two balanced oracles. This is the
  interference of part (3) made quantitative: the query register's amplitudes recombine at the final
  Hadamard so that the constant/balanced answer is read out with certainty.

## Design notes

* **Shared engine.** `deutschCircuit`, `IsDeutschOracle`, the phase kickback, and the general
  outcome `IsDeutschOracle.deutschCircuit_bornProb` are in
  `AxQM/Postulates/API/DeutschAlgorithm.lean`; this file only *applies* them, once per oracle,
  verifying the four oracles against existing gate truth tables.
* **The measured outcome, not a bare vector.** Deutsch's circuit produces `|f(0)⊕f(1)⟩` in the
  query register *up to a global phase* `(−1)^{f(0)}` (N&C's own `±`, eq. 1.45). The faithful,
  phase-invariant statement of "measure to determine `f(0) ⊕ f(1)`" is the Born probability `= 1`,
  matching the Kitaev-phase-estimation outcome style (Problem 5.3).
* **"Kerr", "Fredkin", "beamsplitter", "mirror" — what each names here.** The entangling gate is the
  **Kerr** controlled-`Z` `opticalKerrGate 0 0 π` (eqs. 7.42–7.46), grounded in a Lean statement.
  A *Fredkin* gate is a controlled-**SWAP**, not a controlled-`Z`; N&C's optical Fredkin gate
  (Box 7.4) *corresponds to* a controlled-`Z` **in the dual-rail representation**, so "Fredkin gate"
  in part (1) is that dual-rail controlled-`Z` — the same `K` — and this file does **not** identify
  the abstract `controlledZGate` with a controlled-SWAP. The single-qubit **Hadamards** are the
  algorithm's `hadamardGate`; their optical realisation has two forms — a **beamsplitter after a
  phase shifter** (`opticalHadamardDualRail`, Hadamard up to phase `e^{iπ} = -1`, Ex. 7.9) and a
  **beamsplitter after a mirror** (`opticalHadamardMirror`, the *exact* Hadamard, no phase shifter —
  the part (2) answer). An answer/query-rail `X` is a **mirror** (`Evolution.swap`, swapping a
  dual-rail qubit's two modes).
* **Part (2), resolved.** N&C asks *why no phase shifters are necessary*. The apparent tension is
  that Exercise 7.9's optical Hadamard `= beamSplitter · phaseMode(π)` *does* use a `π` phase shift.
  The resolution (`opticalHadamardMirror_evolvePure_dualRailZero`/`_dualRailOne`): the Hadamard can
  instead be realised as `SWAP ∘ B(π/4)` — a beamsplitter and a **mirror** — which reproduces the
  Hadamard *exactly* (removing even the global phase of `opticalHadamardDualRail`). As a mirror is
  already needed for the oracles' `X` gates, and the constant oracles (`I`, `I ⊗ X`) and the Kerr
  entangling gate use no phase shifter either, the whole construction needs none. Part (3) — the
  interference explanation — *is* the `_bornProb` theorems: the phase kickback turns `f` into a
  relative sign on the query amplitudes, which the final Hadamard interferes into the single outcome
  `f(0) ⊕ f(1)`.
* **Scope: the logical/dual-rail level, not the four-mode assembly.** The four `U_f` are formalised
  as `Evolution (qubit ⊗ qubit)` (query ⊗ answer, each a dual-rail-encoded qubit per §7.4.2),
  and every optical *ingredient* of the construction is a grounded `Evolution`: the Kerr entangling
  gate `opticalKerrGate 0 0 π`, the beamsplitter Hadamards (`opticalHadamardDualRail`,
  `opticalHadamardMirror`), and the mirror (`Evolution.swap`). The one thing not assembled is the
  full circuit rebuilt on the four-mode space `(qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)` — each logical
  qubit expanded to its two modes, the Kerr `K` on the two *middle* modes (N&C eq. 7.46). That
  mode-level `Kerr-on-4-modes = logical controlled-Z` correspondence is a separate large development
  (a dual-rail *encoding functor* relating four-mode and two-qubit `Evolution`s); it is
  not carried out here; this file cites the gate-level identities (Ex. 4.17,
  eq. 7.46) instead. This is a scoping choice, not a weakening: no stated claim is narrowed. N&C's
  Exercise 7.13 has exactly three parts (1)–(3); there is no part (4).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The four optical oracles (Exercise 7.13, part 1) -/

/-- **Constant `f ≡ 0`, `U_f = I`.** The oracle that leaves both rails untouched. -/
def deutschOracleConstZero : Evolution (qubit ⊗ qubit) := Evolution.id

/-- **Constant `f ≡ 1`, `U_f = I ⊗ X`.** The oracle that flips the answer rail unconditionally
(an `X` on the second qubit, realised by a fully-reflecting beamsplitter / mirror). -/
def deutschOracleConstOne : Evolution (qubit ⊗ qubit) := pauliXGate.onRight qubit

/-- **Balanced `f = id`, `U_f = CNOT`.** The controlled-`NOT`, realised optically from the Kerr /
Fredkin controlled-`Z` and two Hadamards (N&C eq. 7.46, Exercise 4.17). -/
def deutschOracleIdentity : Evolution (qubit ⊗ qubit) := cnotGate

/-- **Balanced `f = ¬`, `U_f = (X ⊗ I) · CNOT · (X ⊗ I)`.** The `0`-controlled `NOT`: `CNOT`
conjugated by an `X` on the query rail, so the answer rail flips exactly when the query is `|0⟩`. -/
def deutschOracleNegation : Evolution (qubit ⊗ qubit) :=
  (pauliXGate.onLeft qubit).comp (cnotGate.comp (pauliXGate.onLeft qubit))

/-! ### Each gate is the oracle for its function (Exercise 7.13, part 1) -/

/-- `U_f = I` is the oracle for the constant function `f ≡ 0`: it maps `|x, y⟩` to `|x, y ⊕ 0⟩`. -/
theorem deutschOracleConstZero_isDeutschOracle :
    IsDeutschOracle (fun _ => 0) deutschOracleConstZero := by
  intro x y
  rw [deutschOracleConstZero, Evolution.id_evolvePure]
  simp

/-- `U_f = I ⊗ X` is the oracle for the constant function `f ≡ 1`: it maps `|x, y⟩` to
`|x, y ⊕ 1⟩` (the `X` on the answer rail). -/
theorem deutschOracleConstOne_isDeutschOracle :
    IsDeutschOracle (fun _ => 1) deutschOracleConstOne := by
  intro x y
  rw [deutschOracleConstOne, Evolution.onRight_evolvePure, pauliXGate_evolvePure_qubitBasis]

/-- `U_f = CNOT` is the oracle for the identity function `f = id`: it maps `|x, y⟩` to
`|x, y ⊕ x⟩` (the `CNOT` truth table). -/
theorem deutschOracleIdentity_isDeutschOracle :
    IsDeutschOracle id deutschOracleIdentity := by
  intro x y
  rw [deutschOracleIdentity, cnotGate_evolvePure_qubitBasis]
  rfl

/-- `U_f = (X ⊗ I) · CNOT · (X ⊗ I)` is the oracle for the negation `f = ¬` (`f x = x ⊕ 1`): the
two `X`s on the query rail turn `CNOT` into a `0`-controlled `NOT`, mapping `|x, y⟩` to
`|x, y ⊕ (x ⊕ 1)⟩`. -/
theorem deutschOracleNegation_isDeutschOracle :
    IsDeutschOracle (fun x => x + 1) deutschOracleNegation := by
  intro x y
  rw [deutschOracleNegation, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis, cnotGate_evolvePure_qubitBasis,
    Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis]
  congr 1
  fin_cases x <;> rfl

/-! ### Optical construction of the balanced oracles from the Kerr gate (Exercise 7.13, part 1) -/

/-- **The Kerr controlled-`Z`** (N&C §7.4.1, eqs. 7.42–7.45). The optical Kerr gate
`opticalKerrGate` — N&C's physical two-photon model (eq. 7.87; `opticalKerrGate φ_a φ_b Δ`,
Exercise 7.23) — with *no*
single-photon phases (`φ_a = φ_b = 0`) and the "hard" Kerr value `χL = Δ = π` is exactly the
controlled-`Z`: it fixes `|00⟩, |01⟩, |10⟩` and sends `|11⟩ ↦ −|11⟩`, i.e. the §7.4.1 Kerr medium
`K = e^{iχL a†a b†b}` at `χL = π` (eq. 7.45). This grounds the balanced oracles' entangling gate in
an **actual optical Kerr object** rather than a bare `controlledZGate` (whose basis action is
`controlledZGate_op_apply_qubitBasis`). -/
theorem opticalKerrGate_zero_pi_eq_controlledZGate :
    opticalKerrGate 0 0 Real.pi = controlledZGate := by
  rw [opticalKerrGate, phaseShiftGate_zero, Evolution.id_onLeft, Evolution.id_onRight,
    Evolution.id_comp, Evolution.id_comp, controlledPhaseShift_pi_eq_controlledZGate]

/-- **Part (1), the identity oracle from a Kerr gate (N&C eq. 7.46).** The balanced oracle `f = id`
is `CNOT = (I ⊗ H) · K · (I ⊗ H)`, where `K = opticalKerrGate 0 0 π` is the optical **Kerr**
controlled-`Z` (`opticalKerrGate_zero_pi_eq_controlledZGate`) and each `H` is the algorithm's
single-qubit Hadamard (realised optically by a beamsplitter with phase shifters, N&C p. 294). This
is eq. 7.46 with the entangling gate the Kerr object; the beamsplitter realisation of the `H`s at
the dual-rail *mode* level (§7.4.2, cf. `beamSplitterDualRail`) is not carried out here. -/
theorem deutschOracleIdentity_eq_kerrGate_conj_hadamard :
    deutschOracleIdentity
      = (hadamardGate.onRight qubit).comp
          ((opticalKerrGate 0 0 Real.pi).comp (hadamardGate.onRight qubit)) := by
  rw [deutschOracleIdentity, cnotGate_eq_hadamard_conj_controlledZGate,
    ← opticalKerrGate_zero_pi_eq_controlledZGate]

/-- **Part (1), the negation oracle from a Kerr gate and mirrors.** The balanced oracle `f = ¬` is
the `0`-controlled `NOT`: the identity oracle's optical `CNOT = (I ⊗ H) · K · (I ⊗ H)`
(`deutschOracleIdentity_eq_kerrGate_conj_hadamard`) conjugated by an `X` on the query rail (a
**mirror**, swapping the query dual-rail qubit's two modes), giving
`U_f = (X ⊗ I) · (I ⊗ H) · K · (I ⊗ H) · (X ⊗ I)`. With `deutschOracleConstZero = I` and
`deutschOracleConstOne = I ⊗ X` (a mirror) taking no entangling gate, all four `U_f` are now built
from the optical Kerr gate `K`, Hadamards, and mirrors — the entangling content in a Lean statement,
not prose. -/
theorem deutschOracleNegation_eq_kerrGate_conj_hadamard_mirror :
    deutschOracleNegation
      = (pauliXGate.onLeft qubit).comp
          ((hadamardGate.onRight qubit).comp
            ((opticalKerrGate 0 0 Real.pi).comp
              ((hadamardGate.onRight qubit).comp (pauliXGate.onLeft qubit)))) := by
  rw [deutschOracleNegation, cnotGate_eq_hadamard_conj_controlledZGate,
    ← opticalKerrGate_zero_pi_eq_controlledZGate, Evolution.comp_assoc, Evolution.comp_assoc]

/-! ### The Hadamards as beamsplitters (Exercise 7.13, part 1)

The `I ⊗ H` factors flanking the Kerr `CNOT` (eq. 7.46), and the `H`s of Deutsch's circuit, are
realised optically by the beamsplitter-plus-phase-shifter `opticalHadamardDualRail`
(`AxQM/Postulates/API/Beamsplitter.lean`). Its action on the dual-rail logical basis is N&C's stated
Hadamard action (Exercise 7.9) up to the global phase `e^{iπ} = -1`, giving the *beamsplitter*
half of part (1)'s optical toolkit, as the Kerr gate gives the *Fredkin* half. -/

/-- **Part (1), the beamsplitter Hadamard on `|0_L⟩ = |01⟩`.** The optical Hadamard (a balanced
beamsplitter after a `π` phase shifter) sends `|01⟩` to `-(|01⟩ + |10⟩)/√2` — N&C's Hadamard action
`|01⟩ → (|01⟩ + |10⟩)/√2` (Exercise 7.9) up to the global phase `e^{iπ} = -1`. Together with the
Kerr gate this shows the `I ⊗ H` of the `CNOT` construction (eq. 7.46) is a genuine
beamsplitter, no phase shifter beyond the one inside the Hadamard. -/
theorem opticalHadamardDualRail_evolvePure_dualRailZero :
    opticalHadamardDualRail.evolvePure dualRailZero
      = dualRail (-((Real.sqrt 2 : ℂ) / 2)) (-((Real.sqrt 2 : ℂ) / 2))
          (by simpa using opticalHadamardDualRail_amplitudes_normalized 1 0 (by norm_num)) := by
  rw [dualRailZero_eq_dualRail, opticalHadamardDualRail_evolvePure_dualRail]
  apply PureState.ext
  rw [dualRail_vec, dualRail_vec]
  apply dualRailVec_congr <;> ring

/-- **Part (1), the beamsplitter Hadamard on `|1_L⟩ = |10⟩`.** The optical Hadamard sends `|10⟩` to
`-(|01⟩ - |10⟩)/√2` — N&C's Hadamard action `|10⟩ → (|01⟩ - |10⟩)/√2` (Exercise 7.9) up to the
global phase `e^{iπ} = -1`. -/
theorem opticalHadamardDualRail_evolvePure_dualRailOne :
    opticalHadamardDualRail.evolvePure dualRailOne
      = dualRail (-((Real.sqrt 2 : ℂ) / 2)) ((Real.sqrt 2 : ℂ) / 2)
          (by simpa using opticalHadamardDualRail_amplitudes_normalized 0 1 (by norm_num)) := by
  rw [dualRailOne_eq_dualRail, opticalHadamardDualRail_evolvePure_dualRail]
  apply PureState.ext
  rw [dualRail_vec, dualRail_vec]
  apply dualRailVec_congr <;> ring

/-! ### Part (2): why no phase shifters are necessary

The only element of the construction that might seem to need a phase shifter is the single-qubit
Hadamard: Exercise 7.9 realises it as `B(π/4) ∘ (1 ⊗ P(π))`, a beamsplitter after a `π` phase
shifter. But the Hadamard can equally be built from a beamsplitter and a **mirror** — the mode
`SWAP` (`Evolution.swap`) that each dual-rail qubit already needs for its `X` gate (the oracles'
answer-rail flip and the negation oracle's query-rail flip are mirrors). Replacing the `π` phase
shifter by that mirror gives `opticalHadamardMirror = SWAP ∘ B(π/4)`, which realises the Hadamard
*exactly* — with **no** residual global phase, unlike `opticalHadamardDualRail`. So every gate in
the four `U_f` (identities, mirrors, the Kerr controlled-`Z`, and the Hadamards) is a beamsplitter,
a mirror, or a Kerr medium: no phase shifter is necessary. -/

/-- **Part (2), the phase-shifter-free Hadamard on `|0_L⟩ = |01⟩`.** The mirror Hadamard — a
balanced beamsplitter followed by a mirror (mode `SWAP`), *no phase shifter* — sends `|01⟩` to
`(|01⟩ + |10⟩)/√2`, N&C's exact Hadamard action `|01⟩ → (|01⟩ + |10⟩)/√2` (Exercise 7.9) with no
global phase. This is why no phase shifter is needed: the mirror the oracles already use replaces
the `π` phase shifter of `opticalHadamardDualRail` and removes its `e^{iπ} = -1` phase. -/
theorem opticalHadamardMirror_evolvePure_dualRailZero :
    opticalHadamardMirror.evolvePure dualRailZero
      = dualRail ((Real.sqrt 2 : ℂ) / 2) ((Real.sqrt 2 : ℂ) / 2)
          (by simpa using opticalHadamardMirror_amplitudes_normalized 1 0 (by norm_num)) := by
  rw [dualRailZero_eq_dualRail, opticalHadamardMirror_evolvePure_dualRail]
  apply PureState.ext
  rw [dualRail_vec, dualRail_vec]
  apply dualRailVec_congr <;> ring

/-- **Part (2), the phase-shifter-free Hadamard on `|1_L⟩ = |10⟩`.** The mirror Hadamard sends
`|10⟩` to `(|01⟩ - |10⟩)/√2`, N&C's exact Hadamard action `|10⟩ → (|01⟩ - |10⟩)/√2` (Exercise 7.9)
with no global phase — again with only a beamsplitter and a mirror, no phase shifter. -/
theorem opticalHadamardMirror_evolvePure_dualRailOne :
    opticalHadamardMirror.evolvePure dualRailOne
      = dualRail ((Real.sqrt 2 : ℂ) / 2) (-((Real.sqrt 2 : ℂ) / 2))
          (by simpa using opticalHadamardMirror_amplitudes_normalized 0 1 (by norm_num)) := by
  rw [dualRailOne_eq_dualRail, opticalHadamardMirror_evolvePure_dualRail]
  apply PureState.ext
  rw [dualRail_vec, dualRail_vec]
  apply dualRailVec_congr <;> ring

/-! ### The measured outcome: constant reads `0`, balanced reads `1` -/

/-- **Constant `f ≡ 0` (`U_f = I`) reads `0`** with probability `1` — reports "constant". -/
theorem deutschOracleConstZero_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleConstZero).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 0
      = 1 :=
  deutschOracleConstZero_isDeutschOracle.deutschCircuit_bornProb

/-- **Constant `f ≡ 1` (`U_f = I ⊗ X`) reads `0`** with probability `1` — reports "constant". -/
theorem deutschOracleConstOne_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleConstOne).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 0
      = 1 :=
  deutschOracleConstOne_isDeutschOracle.deutschCircuit_bornProb

/-- **Balanced `f = id` (`U_f = CNOT`) reads `1`** with probability `1` — reports "balanced". -/
theorem deutschOracleIdentity_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleIdentity).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 1
      = 1 :=
  deutschOracleIdentity_isDeutschOracle.deutschCircuit_bornProb

/-- **Balanced `f = ¬` (`0`-controlled `NOT`) reads `1`** with probability `1` — "balanced". -/
theorem deutschOracleNegation_bornProb :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit deutschOracleNegation).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState 1
      = 1 :=
  deutschOracleNegation_isDeutschOracle.deutschCircuit_bornProb

end AxQM
