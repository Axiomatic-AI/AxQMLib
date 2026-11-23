/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ControlledPowerSequence
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.CnotXBasis

/-!
# The phase-estimation Hadamard layer (N&C §5.2, Figure 5.2) — the circuit's input-preparation gate

The first gate of the phase-estimation circuit (N&C Figure 5.2) is a **Hadamard layer**: a Hadamard
applied to each of the `t` control qubits, leaving the target register `S` untouched. Run on the
computational input `|0…0⟩ ⊗ |u⟩` it prepares the equal superposition `(1/√2ᵗ) ∑_b |b⟩ ⊗ |u⟩` over
all `2ᵗ` control registers — the state the controlled-power sequence `seqCtrlPow U t` then acts on.

## What is formalised

* `qtowerPlusKet t u` — the **prepared control register** `|+⟩^{⊗t} ⊗ |u⟩` on `qtower t S`: the `t`
  control qubits each in `|+⟩ = (|0⟩ + |1⟩)/√2`, tensored with the target `u`. Because
  `|+⟩^{⊗t} = (1/√2ᵗ) ∑_b |b⟩`, this **is** the equal superposition of all computational control
  registers; built through the `PureState.tmul` product (so its normalization is inherited, not
  re-proved).
* `qtowerHadamardLayer t` — the **Hadamard layer** as an `Evolution` on `qtower t S`: a Hadamard on
  each control wire, identity on the target. Recursion on the number of controls: `H` on the
  outermost wire (`hadamardGate.onLeft`) composed with the layer on the remaining wires
  (`(·).onRight`).
* `qtowerHadamardLayer_evolvePure_qtowerKet_zero` — **the gate's action**: on the computational
  input `|0…0⟩ ⊗ |u⟩` the layer produces the prepared superposition
  `qtowerHadamardLayer t (|0…0⟩ ⊗ |u⟩) = |+⟩^{⊗t} ⊗ |u⟩`. Induction on `t`, peeling the outermost
  wire: `H|0⟩ = |+⟩` on the head and the layer's action on the tail (inductive hypothesis).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The prepared control register** `|+⟩^{⊗t} ⊗ |u⟩` on `qtower t S`: each of the `t` control
qubits in `|+⟩ = (|0⟩ + |1⟩)/√2`, tensored with the target pure state `u`. Since
`|+⟩^{⊗t} = (1/√2ᵗ) ∑_b |b⟩`, this is the equal superposition of all `2ᵗ` computational control
registers — the output of the phase-estimation Hadamard layer, and the input to `seqCtrlPow U t`. -/
def qtowerPlusKet : (t : ℕ) → PureState S → PureState (qtower t S)
  | 0, u => u
  | (t + 1), u => qubitPlus ⊗ qtowerPlusKet t u

@[simp] theorem qtowerPlusKet_zero (u : PureState S) : qtowerPlusKet 0 u = u := rfl

/-- Peeling the outermost wire: `qtowerPlusKet (t+1) u = |+⟩ ⊗ qtowerPlusKet t u`. -/
theorem qtowerPlusKet_succ (t : ℕ) (u : PureState S) :
    qtowerPlusKet (t + 1) u = qubitPlus ⊗ qtowerPlusKet t u := rfl

/-- **The phase-estimation Hadamard layer** as an `Evolution` on `qtower t S`: a Hadamard on each of
the `t` control wires, identity on the target register `S`. Recursion on the number of controls:
`qtowerHadamardLayer 0` is the identity, and `qtowerHadamardLayer (t+1)` is a Hadamard on the
outermost wire (`hadamardGate.onLeft`) composed with the `t`-wire layer on the inner register
(`(·).onRight qubit`). The first gate of N&C Figure 5.2, generalised over an arbitrary target
`S`. -/
def qtowerHadamardLayer : (t : ℕ) → Evolution (qtower t S)
  | 0 => Evolution.id
  | (t + 1) => (hadamardGate.onLeft (qtower t S)).comp ((qtowerHadamardLayer t).onRight qubit)

/-- Peeling the outermost wire of the Hadamard layer:
`qtowerHadamardLayer (t+1) = (H ⊗ 1) · (layer on the inner register)`. -/
theorem qtowerHadamardLayer_succ (t : ℕ) :
    qtowerHadamardLayer (t + 1) (S := S)
      = (hadamardGate.onLeft (qtower t S)).comp ((qtowerHadamardLayer t).onRight qubit) := rfl

/-- **The Hadamard layer prepares the equal superposition.** On the computational input
`|0…0⟩ ⊗ |u⟩` (the control register all-zero, `qtowerKet t (fun _ => 0) u`), the Hadamard layer
produces the prepared control register `|+⟩^{⊗t} ⊗ |u⟩`:
`qtowerHadamardLayer t (|0…0⟩ ⊗ |u⟩) = qtowerPlusKet t u`.

This is the state-preparation stage of the phase-estimation circuit — the equal superposition
`(1/√2ᵗ) ∑_b |b⟩ ⊗ |u⟩` on which the controlled-power sequence `seqCtrlPow U t` then loads the
eigenphases. Induction on the number of controls `t`: the outermost wire is peeled with
`Evolution.evolvePure_comp`; the outer Hadamard sends `|0⟩` to `|+⟩` (via
`Evolution.onLeft_evolvePure`, `hadamardGate_evolvePure_qubitBasis_zero`) and the inner layer acts
on the tail (`Evolution.onRight_evolvePure`, inductive hypothesis). -/
theorem qtowerHadamardLayer_evolvePure_qtowerKet_zero :
    ∀ (t : ℕ) (u : PureState S),
      (qtowerHadamardLayer t).evolvePure (qtowerKet t (fun _ => 0) u) = qtowerPlusKet t u
  | 0, _ => rfl
  | (t + 1), u => by
      simp only [qtower, qtowerHadamardLayer, qtowerKet_succ, Evolution.evolvePure_comp,
        Evolution.onRight_evolvePure, Evolution.onLeft_evolvePure,
        hadamardGate_evolvePure_qubitBasis_zero, qtowerPlusKet]
      rw [show Fin.tail (fun _ : Fin (t + 1) => (0 : Fin 2)) = (fun _ => 0) from rfl,
        qtowerHadamardLayer_evolvePure_qtowerKet_zero t u]

end AxQM
