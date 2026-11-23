/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.GateCircuit
import AxQM.Postulates.API.TwoLevelUnitaryCircuit
import AxQM.Postulates.API.ControlPairGates
import AxQM.Postulates.API.EvolutionTensorHom
import AxQM.NC.Ch4.Exercise4_20
import AxQM.NC.Ch4.Exercise4_22

/-!
# Nielsen & Chuang, Exercise 4.39 (a circuit for a two-level unitary)

*(N&C p. 193.)*

Find a circuit of single-qubit and CNOT gates implementing a given two-level unitary.

`CNOT`s and single-qubit gates are closed-system evolutions (Postulate 5 / `Evolution`); the
exercise asks for a concrete circuit built from them, together with the theorem that it performs
(4.60). This matrix is the *two-level* unitary acting non-trivially only on
the computational-basis states `|010⟩` (index `2`) and `|111⟩` (index `7`) — the `s = 010`,
`t = 111` example of N&C's Gray-code universality construction (§4.5.2).

## The formalisation, in two parts

**(1) The circuit and its action** — in `AxQM/Postulates/API/TwoLevelUnitaryCircuit.lean`.
A faithful statement of (4.60) must record the coupled-pair **amplitudes**
`a • |010⟩ + b • |111⟩` (a genuine superposition, expressed in terms of state vectors), and the
circuit and its truth table are stated there:

* `AxQM.twoLevelUnitaryCircuit` — **the exercise's circuit** `W · C²(Ũ) · W`: the
  doubly-controlled gate `C²(Ũ) = ccontrolledUnitary Ũ` conjugated by the routing permutation
  `W = twoLevelRoute` (a product of three `CNOT`s, `|q₁,q₂,q₃⟩ ↦ |q₁⊕q₂⊕q₃, q₂, q₃⟩`), which
  carries the coupled pair `{|110⟩,|111⟩}` to `{|010⟩,|111⟩}`.
* `twoLevelUnitaryCircuit_evolvePure_inactive` — the six identity columns of (4.60).
* `twoLevelUnitaryCircuit_evolvePure_active_ketZero` / `..._active_ketOne` — columns 2 and 7:
  `U|010⟩ = a • |010⟩ + b • |111⟩` and `U|111⟩ = c • |010⟩ + d • |111⟩`, the complete action for an
  *arbitrary* `Ũ`.

**(2) That the circuit is genuinely built from single-qubit and `CNOT` gates** — this file. Part (1)
exhibits `W · C²(Ũ) · W` with `W` a product of `CNOT`s and `C²(Ũ)` a *doubly*-controlled unitary,
which is not itself a single-qubit or `CNOT` gate. What the exercise asks — a circuit **using single
qubit operations and `CNOT`s** — is therefore made a formal proposition here, in the typed
single-qubit/`CNOT` circuit model `AxQM.Gate3` (`AxQM/Core/GateCircuit.lean`, the same model
Exercise 4.22 uses): a `List Gate3` is by construction a list of one-qubit gates and `CNOT`s,
and its `gateCircuit` denotation is the `Evolution` it implements. The statement is

* `AxQM.exists_gateCircuit_twoLevelUnitaryCircuit` — for every single-qubit `Ũ`, there is a
  circuit `gs : List Gate3` (single-qubit gates and `CNOT`s only) with
  `gateCircuit gs = twoLevelUnitaryCircuit Ũ`.

Combined with part (1)'s truth table, this is exactly the exercise: an explicit single-qubit/`CNOT`
circuit that implements (4.60). Two supporting objects assemble it:

* `AxQM.twoLevelRouteGates` — the routing `W` as an *explicit* `Gate3` list; each of its
  reversed `CNOT`s (`W` XORs `q₂ ⊕ q₃` into wire 0, which `Gate3`'s forward-`CNOT`s cannot target
  directly) is realised as a forward `CNOT` conjugated by Hadamards (N&C Exercise 4.20,
  `reversedCnotGate_eq_hadamardConj_cnotGate`). `gateCircuit_twoLevelRouteGates` proves
  `gateCircuit twoLevelRouteGates = twoLevelRoute`.
* The doubly-controlled `C²(Ũ)` is supplied by Exercise 4.22 as its own `List Gate3`
  (`ccontrolledUnitary_gateCount_le`, ≤ 8 one-qubit gates + ≤ 6 `CNOT`s). Concatenating
  `twoLevelRouteGates ++ (C²(Ũ)-circuit ++ twoLevelRouteGates)` gives `gs`.

## Design notes

* **Fidelity.** Part (1)'s truth table is the complete action of (4.60) for an
  arbitrary `Ũ`, and part (2) states "single qubit operations and `CNOT`s" as a genuine
  proposition (`gs : List Gate3`), not a prose claim — matching Exercises 4.22 / 4.29 / 4.30
  for circuit-construction items. The routing is fully explicit; the only existential is the
  `C²(Ũ)` sub-circuit, inherited from Exercise 4.22 (whose witness depends on `Ũ`'s ABC
  decomposition).
* **Why reversed `CNOT`s need Hadamards.** The coupled pair `{|010⟩, |111⟩}` differs in wire 0, and
  `C²(Ũ)` acts on `{|110⟩, |111⟩}` (differing in wire 2); the router must flip wire 0, which no
  forward `CNOT` (control on the lower wire) can target. A reversed `CNOT` does it, and a reversed
  `CNOT` is a forward `CNOT` conjugated by Hadamards on both wires — so the circuit stays within
  single-qubit and `CNOT` gates.
* **Supporting identities.** The reversed-`CNOT`/Hadamard identity
  `reversedCnotGate_eq_hadamardConj_cnotGate` is built from Exercise 4.20's truth table. The two
  generic `leftPairGate` gate-algebra identities this construction uses — `leftPairGate_cnotGate`
  (the forward-`CNOT` twin of `reversedCnotLeftGate_eq_leftPairGate`) and
  `leftPairGate_hadamardTmul` — are in `AxQM/Postulates/API/ControlPairGates.lean`, and the
  interchange fact `(H ⊗ 1)·(1 ⊗ H) = H ⊗ H` is the general `Evolution.onLeft_comp_onRight`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### Reversed `CNOT`s as single-qubit/`CNOT` circuits -/

/-- **The reversed `CNOT` is a forward `CNOT` conjugated by Hadamards** (N&C Exercise 4.20,
Figure 4.4), as an equality of `Evolution`s: `reversedCNOT = (H ⊗ H) · CNOT · (H ⊗ H)`. The
Evolution-level lift of `cnotGate_hadamardConj_evolvePure_qubitBasis`: both sides send
`|c⟩ ⊗ |t⟩` to `|c ⊕ t⟩ ⊗ |t⟩`. Stated here (rather than reused from `NC/Ch10`) to keep the
reversed-`CNOT`/Hadamard identity within Chapter 4, where Exercise 4.20 proves the truth table. -/
theorem reversedCnotGate_eq_hadamardConj_cnotGate :
    reversedCnotGate
      = (hadamardGate.tmul hadamardGate).comp (cnotGate.comp (hadamardGate.tmul hadamardGate)) := by
  apply twoQubit_evolution_ext
  intro c t
  rw [reversedCnotGate_evolvePure_qubitBasis, cnotGate_hadamardConj_evolvePure_qubitBasis]

/-- **The reversed `CNOT₃→₂` (control wire 2, target wire 1) as a `Gate3` list:** a forward
`CNOT₁→₂` conjugated by Hadamards on wires 1, 2. Used twice in the routing `W = twoLevelRoute`. -/
def reversedCnotRightGates : List Gate3 :=
  [Gate3.oneQubit 1 hadamardGate, Gate3.oneQubit 2 hadamardGate, Gate3.cnot 1 2,
   Gate3.oneQubit 1 hadamardGate, Gate3.oneQubit 2 hadamardGate]

/-- **The reversed `CNOT₂→₁` (control wire 1, target wire 0) as a `Gate3` list:** a forward
`CNOT₀→₁` conjugated by Hadamards on wires 0, 1. The routing's one wire-0-targeting gate. -/
def reversedCnotLeftGates : List Gate3 :=
  [Gate3.oneQubit 0 hadamardGate, Gate3.oneQubit 1 hadamardGate, Gate3.cnot 0 1,
   Gate3.oneQubit 0 hadamardGate, Gate3.oneQubit 1 hadamardGate]

/-- `reversedCnotRightGates` denotes to `reversedCnotGate.onRight qubit` (the reversed `CNOT` on the
right pair, wires 1, 2). All five gates are `.onRight qubit`, so they combine
(`Evolution.onRight_comp`) into `((H ⊗ 1)·(1 ⊗ H)·CNOT·(H ⊗ 1)·(1 ⊗ H)).onRight`, which is
`reversedCnotGate.onRight` by `Evolution.onLeft_comp_onRight` (`(H ⊗ 1)·(1 ⊗ H) = H ⊗ H`) and
`reversedCnotGate_eq_hadamardConj_cnotGate`. -/
theorem gateCircuit_reversedCnotRightGates :
    gateCircuit reversedCnotRightGates = reversedCnotGate.onRight qubit := by
  rw [reversedCnotRightGates, gateCircuit_cons, gateCircuit_cons, gateCircuit_cons,
    gateCircuit_cons, gateCircuit_cons, gateCircuit_nil]
  simp only [Gate3.denote, Gate3.onWire, Gate3.cnotOn]
  rw [Evolution.one_def, Evolution.comp_id]
  simp only [Evolution.onRight_comp]
  rw [reversedCnotGate_eq_hadamardConj_cnotGate, ← Evolution.comp_assoc,
    Evolution.onLeft_comp_onRight]

/-- `reversedCnotLeftGates` denotes to `reversedCnotLeftGate` (the reversed `CNOT` on the left pair,
control wire 1, target wire 0). Via `reversedCnotLeftGate = leftPairGate reversedCnotGate` and
`leftPairGate`'s functoriality, this reduces to `leftPairGate` of the Hadamard-conjugated `CNOT`,
whose Hadamard and `CNOT` factors are the wire-0/1 gates by `leftPairGate_hadamardTmul` /
`leftPairGate_cnotGate`. -/
theorem gateCircuit_reversedCnotLeftGates :
    gateCircuit reversedCnotLeftGates = reversedCnotLeftGate := by
  rw [reversedCnotLeftGates, gateCircuit_cons, gateCircuit_cons, gateCircuit_cons,
    gateCircuit_cons, gateCircuit_cons, gateCircuit_nil]
  simp only [Gate3.denote, Gate3.onWire]
  rw [Evolution.one_def, Evolution.comp_id,
    show Gate3.cnotOn 0 1 = cnotLeftGate from rfl, reversedCnotLeftGate_eq_leftPairGate,
    reversedCnotGate_eq_hadamardConj_cnotGate, leftPairGate_comp, leftPairGate_comp,
    leftPairGate_hadamardTmul, leftPairGate_cnotGate, ← Evolution.comp_assoc]

/-! ### The routing and the full circuit -/

/-- **The routing `W = twoLevelRoute` as an explicit single-qubit/`CNOT` circuit.** Three reversed
`CNOT`s `reversedCNOT₃→₂ · reversedCNOT₂→₁ · reversedCNOT₃→₂` (each a forward `CNOT` conjugated by
Hadamards), matching `twoLevelRoute`'s definition. -/
def twoLevelRouteGates : List Gate3 :=
  reversedCnotRightGates ++ (reversedCnotLeftGates ++ reversedCnotRightGates)

/-- **The routing circuit is correct:** `gateCircuit twoLevelRouteGates = twoLevelRoute`. The three
`Gate3` blocks denote to the three reversed `CNOT`s composing `twoLevelRoute`. -/
theorem gateCircuit_twoLevelRouteGates : gateCircuit twoLevelRouteGates = twoLevelRoute := by
  rw [twoLevelRouteGates, gateCircuit_append, gateCircuit_append,
    gateCircuit_reversedCnotRightGates, gateCircuit_reversedCnotLeftGates, twoLevelRoute]

/-- **Nielsen & Chuang, Exercise 4.39.** For every single-qubit unitary `Ũ`, the two-level unitary
(4.60) is implemented by a circuit built from single-qubit gates and `CNOT`s: there is a
`gs : List Gate3` (a list of one-qubit gates and `CNOT`s, by construction) with
`gateCircuit gs = twoLevelUnitaryCircuit Ũ`. Together with the truth table of
`twoLevelUnitaryCircuit`
(`twoLevelUnitaryCircuit_evolvePure_inactive` / `..._active_ketZero` / `..._active_ketOne` in
`AxQM/Postulates/API/TwoLevelUnitaryCircuit.lean`), this is exactly the exercise: an explicit
single-qubit/`CNOT` circuit implementing (4.60).

The witness is `twoLevelRouteGates ++ (C²(Ũ)-circuit ++ twoLevelRouteGates)`, conjugating the
doubly-controlled `C²(Ũ)`-circuit of Exercise 4.22 (`ccontrolledUnitary_gateCount_le`) by the
routing `twoLevelRouteGates`, so `gateCircuit gs = W · C²(Ũ) · W = twoLevelUnitaryCircuit Ũ`. -/
theorem exists_gateCircuit_twoLevelUnitaryCircuit (u : Evolution qubit) :
    ∃ gs : List Gate3, gateCircuit gs = twoLevelUnitaryCircuit u := by
  obtain ⟨cc, hcc, _, _⟩ := ccontrolledUnitary_gateCount_le u
  refine ⟨twoLevelRouteGates ++ (cc ++ twoLevelRouteGates), ?_⟩
  rw [gateCircuit_append, gateCircuit_append, gateCircuit_twoLevelRouteGates, hcc,
    twoLevelUnitaryCircuit]

end AxQM
