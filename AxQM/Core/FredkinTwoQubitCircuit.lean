/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.TwoQubitGateCircuit
import AxQM.Postulates.API.Fredkin
import AxQM.Postulates.API.UnitarySquareRoot

/-!
# Figure 4.8 for the middle Toffoli: `middleToffoliGate` as five two-qubit gates (N&C Ex 4.25.3)

Nielsen & Chuang **Exercise 4.25** part (3) instructs one to "replace the middle Toffoli gate with
the circuit in Figure 4.8" to obtain a Fredkin construction using only *two-qubit gates*. The middle
Toffoli of the swap construction (`middleToffoliGate`, Exercise 4.25 part 1) is the
doubly-controlled `X` with controls on qubits 1 and 3 and target qubit 2 — a `C²(X)` whose target is
the *middle* wire rather than the last. This file decomposes the middle Toffoli into a genuine
**five-two-qubit-gate** circuit in the `TwoQubitGate3` cost model of `Core.TwoQubitGateCircuit`, so
that the six-gate (part 3) and five-gate (part 4) constructions can merge it against the outer
`CNOT`s (see `AxQM/NC/Ch4/Exercise4_25.lean`).

## The construction (Figure 4.8 on the middle-wire layout)

Figure 4.8 (Exercise 4.21, `ccontrolledUnitaryCircuit`) decomposes `C²(V²)` — for a single-qubit
square root `V`, `V² = U` — as five gates: `C(V)`, `CNOT`, `C(V†)`, `CNOT`, `C(V)`. For the middle
Toffoli the two controls are wires `0` and `2` and the target is wire `1`, so choosing wire `0` as
the "outer" control `c₁` and wire `2` as the "inner" control `c₂` places the five gates as
(reading left to right — leftmost acts first):

1. `C(V)` with control wire `2` on target wire `1`;
2. `CNOT` with control wire `0` on wire `2`;
3. `C(V†)` with control wire `2` on target wire `1`;
4. `CNOT` with control wire `0` on wire `2`;
5. `C(V)` with control wire `0` on target wire `1`.

Every gate is a genuine two-qubit gate of the `TwoQubitGate3` alphabet:

* gates 1, 3 are `pair`s — a `C(V)` / `C(V†)` **controlled on wire `2`, targeting wire `1`**, i.e.
  the two-qubit gate `reversedControlledUnitary V` on the target pair `{1, 2}` (control on the
  *second* factor, target on the *first*), with wire `0` idle;
* gates 2, 4 are `ctrl 1 X` — the control-wire-`0` bit flip of wire `2`;
* gate 5 is `ctrl 0 V` — the control-wire-`0` gate `V` on wire `1`.

The "reversed" placement of gates 1, 3 is exactly the placement the six-gate merge of part 3 needs:
they sit on the swapped pair `{1, 2}`, so one of the outer `CNOT`s of the part-2 construction
(`Fredkin = (I ⊗ CNOT) · middleToffoli · (I ⊗ CNOT)`) is adjacent to a `pair` gate and merges into
it, dropping the count `7 → 6`.

## What is formalised

* `reversedControlledUnitary U` — the **reversed controlled-`U`** on two qubits: control on the
  *second* qubit, target on the *first*, `SWAP · C(U) · SWAP`. Generalises `reversedCnotGate`
  (`= reversedControlledUnitary pauliXGate`); its two branch actions are
  `reversedControlledUnitary_evolvePure_ketZero`/`_ketOne`.
* `middleToffoliTwoQubitGates V` — the length-5 list of `TwoQubitGate3`s above.
* `twoQubitCircuit_middleToffoliTwoQubitGates` — **the Figure 4.8 identity**, fully general in `V`:
  the circuit implements the middle-layout `C²(V²)`, `twoQubitCircuit (middleToffoliTwoQubitGates V)
  = controlledUnitary (reversedControlledUnitary (V.comp V))`.
* `twoQubitCircuit_middleToffoliTwoQubitGates_eq_middleToffoliGate` — the **middle-Toffoli
  specialisation**: whenever `V² = X`, the circuit equals `middleToffoliGate`.
* `exists_twoQubitCircuit_eq_middleToffoliGate` — the **five-two-qubit-gate existence statement**:
  there is a two-qubit-gate circuit equal to `middleToffoliGate` with `twoQubitCount = 5` (the `V`
  is supplied by `Evolution.exists_comp_self_eq`, so no concrete √X is named).

## Design notes

* **Fidelity.** The main identity is proved for an **arbitrary** single-qubit `V`
  (it implements `C²(V²)`), exactly mirroring Exercise 4.21's generality; the middle Toffoli is the
  `V² = X` instance. `V†` is the genuine adjoint gate `V.adjoint = V⁻¹`, and the equalities are full
  `Evolution` equalities, not "on basis states" surrogates.
* **Proof.** `threeQubit_evolution_ext` reduces to agreement on the eight basis inputs; the circuit
  unfolds one gate at a time; casework on the two controls `(wire 0, wire 2)` drives the
  factor-wise gate actions and the unitarity cancellations `V† V = 1`, `V V† = 1`, `V (V ψ) = V² ψ`
  — the same mechanism as `ccontrolledUnitaryCircuit_eq_ccontrolledUnitary`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The reversed controlled-`U` gate -/

/-- **The reversed controlled-`U` gate** on two qubits: the single-qubit unitary `U` is applied to
the *first* qubit exactly when the *second* qubit is `|1⟩` — the roles of control and target of
`controlledUnitary` interchanged. Realised as the swap-conjugate `SWAP · C(U) · SWAP`, so it is a
genuine unitary `Evolution`. It generalises `reversedCnotGate` (which is `reversedControlledUnitary
pauliXGate`), and supplies the `pair` gates of the middle Toffoli's Figure 4.8 decomposition (a
`C(V)` on the target pair `{1, 2}` controlled on the *second* wire). -/
def reversedControlledUnitary (U : Evolution qubit) : Evolution (qubit ⊗ qubit) :=
  (Evolution.swap (S := qubit)).comp ((controlledUnitary U).comp (Evolution.swap (S := qubit)))

/-- **Reversed controlled-`U`, control (second qubit) `|0⟩`:** the target (first qubit) is
untouched, `revC(U)(ψ ⊗ |0⟩) = ψ ⊗ |0⟩`. Computed from `SWAP · C(U) · SWAP` factor by factor. -/
theorem reversedControlledUnitary_evolvePure_ketZero (U : Evolution qubit) (ψ : PureState qubit) :
    (reversedControlledUnitary U).evolvePure (ψ ⊗ (qubitBasis 0)) = ψ ⊗ (qubitBasis 0) := by
  rw [reversedControlledUnitary, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.swap_evolvePure_tmul, controlledUnitary_evolvePure_ketZero,
    Evolution.swap_evolvePure_tmul]

/-- **Reversed controlled-`U`, control (second qubit) `|1⟩`:** the gate `U` is applied to the target
(first qubit), `revC(U)(ψ ⊗ |1⟩) = (Uψ) ⊗ |1⟩`. Computed from `SWAP · C(U) · SWAP` factor by
factor. -/
theorem reversedControlledUnitary_evolvePure_ketOne (U : Evolution qubit) (ψ : PureState qubit) :
    (reversedControlledUnitary U).evolvePure (ψ ⊗ (qubitBasis 1))
      = (U.evolvePure ψ) ⊗ (qubitBasis 1) := by
  rw [reversedControlledUnitary, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.swap_evolvePure_tmul, controlledUnitary_evolvePure_ketOne,
    Evolution.swap_evolvePure_tmul]

/-- **The middle Toffoli equals the reversed doubly-controlled `X`.** Unfolding definitions,
`middleToffoliGate = controlledUnitary reversedCnotGate` and `reversedCnotGate =
reversedControlledUnitary pauliXGate` (both are `SWAP · CNOT · SWAP` since `cnotGate =
controlledUnitary pauliXGate`), so `middleToffoliGate = controlledUnitary (reversedControlledUnitary
pauliXGate)` — the middle-wire `C²(X)`. This is the `V² = X` case of
`twoQubitCircuit_middleToffoliTwoQubitGates`'s right-hand side. -/
theorem middleToffoliGate_eq_controlledUnitary_reversedControlledUnitary :
    middleToffoliGate = controlledUnitary (reversedControlledUnitary pauliXGate) := rfl

/-! ### The middle Toffoli as five two-qubit gates -/

/-- **The five two-qubit gates of the middle Toffoli's Figure 4.8 decomposition** (for a
single-qubit square root `V`, `V² = X`), as a `TwoQubitGate3` list on `qubit ⊗ (qubit ⊗ qubit)`. In
*list order* the leftmost element is applied last (it is the leftmost `comp` factor), so reading the
circuit left to right — leftmost gate first — the list is the reverse: `C(V)`(0→1), `CNOT`(0→2),
`C(V†)`(2→1), `CNOT`(0→2), `C(V)`(2→1). Gates 1, 3 (the wire-`2`-controlled `C(V)` / `C(V†)`
on target wire `1`) are `pair (reversedControlledUnitary _)`; gates 2, 4 are `ctrl 1 X`; gate 5 is
`ctrl 0 V`. -/
def middleToffoliTwoQubitGates (V : Evolution qubit) : List TwoQubitGate3 :=
  [TwoQubitGate3.ctrl 0 V,
   TwoQubitGate3.ctrl 1 pauliXGate,
   TwoQubitGate3.pair (reversedControlledUnitary V.adjoint),
   TwoQubitGate3.ctrl 1 pauliXGate,
   TwoQubitGate3.pair (reversedControlledUnitary V)]

/-- **Nielsen & Chuang, Exercise 4.25 part 3 (Figure 4.8 for the middle Toffoli).** For every
single-qubit gate `V`, the five-two-qubit-gate circuit `middleToffoliTwoQubitGates V` implements the
middle-wire doubly-controlled gate on `U = V²`, `twoQubitCircuit (middleToffoliTwoQubitGates V) =
controlledUnitary (reversedControlledUnitary (V.comp V))` (controls on wires `0`, `2`, target wire
`1`).

This is the faithful, fully general Figure 4.8 identity (the analogue of
`ccontrolledUnitaryCircuit_eq_ccontrolledUnitary` for the middle-wire target). Proved by three-qubit
computational-basis extensionality: unfold the circuit, then case on the two controls `(q1, q3)` =
(wire 0, wire 2); the factor-wise gate actions and the unitarity cancellations `V† V = 1`,
`V V† = 1`, `V (V ψ) = (V²) ψ` make each of the four branches agree. -/
theorem twoQubitCircuit_middleToffoliTwoQubitGates (V : Evolution qubit) :
    twoQubitCircuit (middleToffoliTwoQubitGates V)
      = controlledUnitary (reversedControlledUnitary (V.comp V)) := by
  refine threeQubit_evolution_ext (fun q1 q2 q3 => ?_)
  simp only [middleToffoliTwoQubitGates, twoQubitCircuit_cons, twoQubitCircuit_nil,
    TwoQubitGate3.denote_ctrl_zero, TwoQubitGate3.denote_ctrl_one, TwoQubitGate3.denote_pair,
    Evolution.evolvePure_comp, Evolution.one_def, Evolution.id_evolvePure]
  fin_cases q1 <;> fin_cases q3 <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue,
      controlledUnitary_evolvePure_ketZero, controlledUnitary_evolvePure_ketOne,
      Evolution.onLeft_evolvePure, Evolution.onRight_evolvePure,
      reversedControlledUnitary_evolvePure_ketZero, reversedControlledUnitary_evolvePure_ketOne,
      pauliXGate_evolvePure_qubitBasis, Fin.reduceAdd,
      Evolution.evolvePure_adjoint_evolvePure, Evolution.evolvePure_adjoint_evolvePure',
      Evolution.evolvePure_comp]

/-- **The middle Toffoli is a five-two-qubit-gate circuit** (Exercise 4.25 part 3). Whenever `V` is
a square root of `X` (`V.comp V = pauliXGate`), the circuit `middleToffoliTwoQubitGates V` equals
`middleToffoliGate`. Immediate from the general Figure 4.8 identity
`twoQubitCircuit_middleToffoliTwoQubitGates` and `middleToffoliGate = controlledUnitary
(reversedControlledUnitary X)`. -/
theorem twoQubitCircuit_middleToffoliTwoQubitGates_eq_middleToffoliGate (V : Evolution qubit)
    (hV : V.comp V = pauliXGate) :
    twoQubitCircuit (middleToffoliTwoQubitGates V) = middleToffoliGate := by
  rw [twoQubitCircuit_middleToffoliTwoQubitGates, hV,
    middleToffoliGate_eq_controlledUnitary_reversedControlledUnitary]

/-- **The middle Toffoli's decomposition uses five two-qubit gates.** The list has length `5`, so
its `twoQubitCount` is `5` — every element is a genuine two-qubit gate. -/
theorem twoQubitCount_middleToffoliTwoQubitGates (V : Evolution qubit) :
    twoQubitCount (middleToffoliTwoQubitGates V) = 5 := rfl

/-- **The middle Toffoli is implementable by five two-qubit gates** (Exercise 4.25 part 3, existence
form). There is a `TwoQubitGate3` circuit whose evolution is `middleToffoliGate` and whose
`twoQubitCount` is `5`. The square root `V` of `X` is supplied by `Evolution.exists_comp_self_eq`,
so no concrete √X gate is named. This is the honest "middle Toffoli = five two-qubit gates"
proposition the six- and five-gate Fredkin constructions build on. -/
theorem exists_twoQubitCircuit_eq_middleToffoliGate :
    ∃ gs : List TwoQubitGate3,
      twoQubitCircuit gs = middleToffoliGate ∧ twoQubitCount gs = 5 := by
  obtain ⟨V, hV⟩ := Evolution.exists_comp_self_eq pauliXGate
  exact ⟨middleToffoliTwoQubitGates V,
    twoQubitCircuit_middleToffoliTwoQubitGates_eq_middleToffoliGate V hV,
    twoQubitCount_middleToffoliTwoQubitGates V⟩

end AxQM
