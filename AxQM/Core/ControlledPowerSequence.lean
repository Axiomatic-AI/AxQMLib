/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction

/-!
# The phase-estimation controlled-`U` sequence — first stage of Figure 5.2 (Nielsen & Chuang §5.2)

The building blocks behind the first stage of the phase-estimation circuit
(N&C Figure 5.2): a `t`-qubit control register wrapping a target `S`, and, for each control wire, a
controlled power of `U` acting on `S`. On a computational-basis control `|j⟩ = |j₁…j_t⟩` the wire
`jₛ` applies `U^{jₛ·2^{t-s}}`, so the whole sequence applies `Uʲ`.

These are the direct analogs, over an **arbitrary** inner target system `S`, of the register ket
`towerKet` (`Core/MultiControlledNotBasis`, inner system a qubit) and its gate-action lemmas: shared
theory that the phase-estimation cluster (N&C Exercises 5.7, 5.8, 5.9, …) consumes. Exercise 5.7
(`AxQM/NC/Ch5/Exercise5_7.lean`) applies `seqCtrlPow_evolvePure` (proved here) to state it.

## What is formalised

* `qtowerKet t b u` — the input state `|b₀…b_{t-1}⟩ ⊗ |u⟩` on the register `qtower t S` (`t` control
  qubits wrapping the target `S`), for a bit-string `b : Fin t → Fin 2` (`b 0` the outermost /
  most-significant wire) and an **arbitrary** target pure state `u : PureState S`.
* `seqCtrlPow U t` — the sequence of controlled-`U` operations of Figure 5.2, as an `Evolution` on
  `qtower t S`. Built by recursion on the number of controls: the outermost (most-significant) wire
  controls `U^{2^t}` on the target — reaching *through* the inner controls via the idle wrap
  `unCtrl t` — and the remaining wires are the `t`-control sequence `seqCtrlPow U t`.
* `unCtrl_evolvePure_qtowerKet` — the idle wrap acts only on the target of a tower ket: the building
  block that lets the outermost controlled gate of `seqCtrlPow` apply a power of `U` to the
  innermost target.

## Design notes

* **Reaching through the register.** The `s`-th wire controls a power of `U` on the *innermost*
  target `S`, which sits below the other control qubits. The idle wrap `unCtrl t (U^{2^t})` places
  `U^{2^t}` on `S` while acting as the identity on the `t` inner control qubits, so no associator or
  swap is needed; `controlledUnitary` then conditions it on the outermost wire.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The control register in a computational-basis state -/

/-- **The phase-estimation input state** `|b₀ … b_{t-1}⟩ ⊗ |u⟩` on `qtower t S` (`t` control qubits
wrapping the target `S`): the control register in the computational-basis state indexed by the
bit-string `b : Fin t → Fin 2` (`b 0` the outermost / most-significant wire), tensored with an
arbitrary target pure state `u`. The arbitrary-inner-system analog of `towerKet`. -/
def qtowerKet : (t : ℕ) → (Fin t → Fin 2) → PureState S → PureState (qtower t S)
  | 0, _, u => u
  | (t + 1), b, u => (qubitBasis (b 0)) ⊗ qtowerKet t (Fin.tail b) u

@[simp] theorem qtowerKet_zero (b : Fin 0 → Fin 2) (u : PureState S) : qtowerKet 0 b u = u := rfl

/-- Peeling the outermost control wire of a tower ket:
`qtowerKet (t+1) b u = |b₀⟩ ⊗ qtowerKet t (tail b) u`. -/
theorem qtowerKet_succ (t : ℕ) (b : Fin (t + 1) → Fin 2) (u : PureState S) :
    qtowerKet (t + 1) b u = (qubitBasis (b 0)) ⊗ qtowerKet t (Fin.tail b) u := rfl

/-! ### The sequence of controlled-`U` operations (first stage of Figure 5.2) -/

/-- **The sequence of controlled-`U` operations of Figure 5.2**, as an `Evolution` on the register
`qtower t S`. Recursion on the number of controls: `seqCtrlPow U 0` is the identity (no controls),
and `seqCtrlPow U (t+1)` conditions `U^{2^t}` on the outermost (most-significant) wire — placed on
the target `S` through the `t` inner controls by `unCtrl t` — and then runs the `t`-control sequence
on the remaining wires. On a computational-basis control `|j⟩` the wire of weight `2^w` contributes
`U^{jₛ·2^w}`, so the whole sequence applies `Uʲ` (`seqCtrlPow_evolvePure`, in
`AxQM/NC/Ch5/Exercise5_7.lean`). -/
def seqCtrlPow (U : Evolution S) : (t : ℕ) → Evolution (qtower t S)
  | 0 => Evolution.id
  | (t + 1) => (controlledUnitary (unCtrl t (U ^ 2 ^ t))).comp ((seqCtrlPow U t).onRight qubit)

@[simp] theorem seqCtrlPow_zero (U : Evolution S) : seqCtrlPow U 0 = Evolution.id := rfl

/-- Peeling the outermost control of the sequence:
`seqCtrlPow U (t+1) = C(unCtrl t (U^{2^t})) · (seqCtrlPow U t on the inner register)`. -/
theorem seqCtrlPow_succ (U : Evolution S) (t : ℕ) :
    seqCtrlPow U (t + 1)
      = (controlledUnitary (unCtrl t (U ^ 2 ^ t))).comp ((seqCtrlPow U t).onRight qubit) := rfl

/-! ### The idle wrap acts only on the target of a tower ket -/

/-- **The idle wrap reaches through the controls to the target.** `unCtrl t V` (`V` wrapped by `t`
idle control qubits) acts on `|b⟩ ⊗ |u⟩` by leaving the control register `|b⟩` untouched and
applying `V` to the target `u`: `(unCtrl t V)(|b⟩⊗|u⟩) = |b⟩⊗(V|u⟩)`. The building block that lets
the outermost controlled gate of `seqCtrlPow` apply a power of `U` to the innermost target. -/
theorem unCtrl_evolvePure_qtowerKet (V : Evolution S) :
    ∀ (t : ℕ) (b : Fin t → Fin 2) (u : PureState S),
      (unCtrl t V).evolvePure (qtowerKet t b u) = qtowerKet t b (V.evolvePure u)
  | 0, _, _ => rfl
  | (t + 1), b, u => by
    simp only [qtower, unCtrl_succ, qtowerKet_succ, Evolution.onRight_evolvePure,
      unCtrl_evolvePure_qtowerKet V t (Fin.tail b) u]

end AxQM
