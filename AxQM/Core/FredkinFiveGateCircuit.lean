/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.TwoQubitGateCircuit
import AxQM.Core.FredkinTwoQubitCircuit
import AxQM.Postulates.API.ControlBranchExt
import AxQM.Postulates.API.HadamardGate
import AxQM.Postulates.API.AxisAngleGateValues

/-!
# The five-two-qubit-gate Fredkin construction: gate + control-branch reduction (N&C Ex 4.25.4)

Nielsen & Chuang **Exercise 4.25** part (4) asks for an *even simpler* Fredkin construction using
"only **five two-qubit gates**" — the Smolin–DiVincenzo result. This file contains the
gate and the control-branch reduction for that construction in the `TwoQubitGate3` cost model of
`Core.TwoQubitGateCircuit`.

## The shape of the five-gate circuit

Part 2 gives `Fredkin = (I ⊗ CNOT) · middleToffoli · (I ⊗ CNOT)` and part 3 expands the middle
Toffoli by Figure 4.8 to get *six* two-qubit gates. The five-gate construction cannot come from
merging further: a controlled-single-qubit alphabet on the control pairs cannot reach five (the same
obstruction as Problem 3.5). It must use a genuinely **entangling** two-qubit gate. The clean choice
places the two entangling gates on the *target* pair `{a, b}` (`pair B`, `pair B†`) sandwiching
three
controlled-single-qubit gates (`ctrl`), so that on control `|0⟩` the `pair` gates cancel
(`B† B = 1`) and on control `|1⟩` the whole thing must implement `SWAP`. Concretely the five-gate
list is
```
[pair B†, ctrl 0 W₃, ctrl 1 W₂, pair B, ctrl 0 W₁]
```
with `B` an entangling two-qubit gate and `W₁, W₂, W₃` single-qubit gates. This is exactly the shape
whose *control-branch reduction* is `twoQubitCircuit_pair_ctrl_eq_fredkinGate` below.

## What is formalised

* `swapDiagonalizingGate` — the entangling two-qubit gate `B` used on the target pair,
  `B = (I ⊗ H) · revC(S) · (H ⊗ I) · CNOT`, a product of four elementary gates. It is the (unique up
  to phase) gate that diagonalises the four-cycle permutation `(I ⊗ X) · SWAP`, a "Fourier-type"
  entangling gate — the kind the five-gate construction provably needs (a controlled-single-qubit
  alphabet cannot supply it).
* `twoQubitCircuit_pair_ctrl_eq_fredkinGate` — **the control-branch reduction.** For *any* two-qubit
  gate `B` and single-qubit gates `W₁, W₂, W₃`, if the control-`|1⟩` branch operator implements the
  swap,
  `B† · (W₃ on a) · (W₂ on b) · B · (W₁ on a) = SWAP`,
  then the five-gate circuit `[pair B†, ctrl 0 W₃, ctrl 1 W₂, pair B, ctrl 0 W₁]` equals
  `fredkinGate`. This reduces "the five-gate circuit is the Fredkin gate" to a single **two-qubit**
  identity, discharging the three-qubit control structure once and for all.

## Design notes

* **Why the reduction is clean.** The three-qubit circuit is split on its control qubit with
  `controlBranch_evolution_ext` (agreement on `|i⟩ ⊗ φ`, `i ∈ {0, 1}`, `φ` arbitrary). On `|0⟩` the
  `ctrl` gates are identities and the two `pair` gates cancel by `B† B = 1`
  (`Evolution.evolvePure_adjoint_evolvePure`); on `|1⟩` the `ctrl` gates fire and the branch
  operator
  is exactly the swap hypothesis, matched against `fredkinGate = controlledUnitary SWAP` via
  `controlledUnitary_evolvePure_ketOne`. No superposition bookkeeping — that is isolated to the
  separate two-qubit `SWAP`-conjugation identity a consumer supplies.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The swap-diagonalizing entangling gate -/

/-- **The swap-diagonalizing gate** `B = (I ⊗ H) · revC(S) · (H ⊗ I) · CNOT` on two qubits: the
entangling two-qubit gate used on the target pair of the five-two-qubit-gate Fredkin construction
(Exercise 4.25 part 4). Reading right to left (`CNOT` applied first): a `CNOT` with control the
first qubit, a Hadamard on the first qubit, a reversed controlled-`S` (control second, target
first), then a Hadamard on the second qubit. It is the (unique up to phase) gate diagonalising the
four-cycle permutation `(I ⊗ X) · SWAP`; being a genuinely entangling "Fourier-type" gate it
supplies the entanglement a controlled-single-qubit alphabet cannot (Smolin–DiVincenzo). -/
def swapDiagonalizingGate : Evolution (qubit ⊗ qubit) :=
  (hadamardGate.onRight qubit).comp
    ((reversedControlledUnitary sGate).comp
      ((hadamardGate.onLeft qubit).comp cnotGate))

/-! ### Control-branch reduction to the Fredkin gate -/

/-- **Control-branch reduction for the five-two-qubit-gate Fredkin construction** (Exercise 4.25
part 4). For any two-qubit gate `B` and single-qubit gates `W₁, W₂, W₃`, if the control-`|1⟩` branch
operator implements the swap,
`B† · (W₃ on the first target) · (W₂ on the second target) · B · (W₁ on the first target) = SWAP`,
then the five-gate circuit `[pair B†, ctrl 0 W₃, ctrl 1 W₂, pair B, ctrl 0 W₁]` equals the Fredkin
gate `C(SWAP)`.

Proof: split on the control qubit with `controlBranch_evolution_ext`. On control `|0⟩` the three
`ctrl` gates act as the identity and the two `pair` gates cancel (`B† B = 1`,
`Evolution.evolvePure_adjoint_evolvePure`), matching `fredkinGate`'s identity branch. On control
`|1⟩` the `ctrl` gates fire, exhibiting exactly the branch operator of the hypothesis, matched
against `fredkinGate = controlledUnitary SWAP` on the swap branch
(`controlledUnitary_evolvePure_ketOne`). No superposition bookkeeping is needed here; it is confined
to establishing the two-qubit swap hypothesis for a concrete `B`. -/
theorem twoQubitCircuit_pair_ctrl_eq_fredkinGate
    (B : Evolution (qubit ⊗ qubit)) (W₁ W₂ W₃ : Evolution qubit)
    (hswap : B.adjoint.comp
        ((W₃.onLeft qubit).comp ((W₂.onRight qubit).comp (B.comp (W₁.onLeft qubit))))
      = Evolution.swap) :
    twoQubitCircuit
        [TwoQubitGate3.pair B.adjoint, TwoQubitGate3.ctrl 0 W₃, TwoQubitGate3.ctrl 1 W₂,
          TwoQubitGate3.pair B, TwoQubitGate3.ctrl 0 W₁]
      = fredkinGate := by
  refine controlBranch_evolution_ext (fun i φ => ?_)
  simp only [twoQubitCircuit_cons, twoQubitCircuit_nil, TwoQubitGate3.denote_pair,
    TwoQubitGate3.denote_ctrl_zero, TwoQubitGate3.denote_ctrl_one, Evolution.one_def,
    Evolution.comp_id, Evolution.evolvePure_comp]
  fin_cases i
  · -- control |0⟩ : the ctrl gates are identities and the pair gates cancel.
    rw [Fin.mk_zero, controlledUnitary_evolvePure_ketZero, Evolution.onRight_evolvePure,
      controlledUnitary_evolvePure_ketZero, controlledUnitary_evolvePure_ketZero,
      Evolution.onRight_evolvePure, Evolution.evolvePure_adjoint_evolvePure,
      fredkinGate_evolvePure_ketZero_left]
  · -- control |1⟩ : the ctrl gates fire; the branch operator is the swap hypothesis.
    rw [Fin.mk_one, controlledUnitary_evolvePure_ketOne, Evolution.onRight_evolvePure,
      controlledUnitary_evolvePure_ketOne, controlledUnitary_evolvePure_ketOne,
      Evolution.onRight_evolvePure, fredkinGate, controlledUnitary_evolvePure_ketOne]
    have := congrArg (fun U => U.evolvePure φ) hswap
    simp only [Evolution.evolvePure_comp] at this
    rw [this]

end AxQM
