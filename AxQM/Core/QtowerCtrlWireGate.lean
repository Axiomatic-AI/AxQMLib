/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerSingleWireGate

/-!
# Placing a controlled single-qubit gate on a wire pair of the control tower (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` (the register bridge `quditPowTower`) as a
*product of wire-addressed tower gates* (`qftTowerEvolution_eq_map_congr_prod`), so
each transported Figure 5.1 gate must be re-expressed as such a tower gate. The gates come in three
shapes: the swap layer (a *wire permutation*, `Evolution.qtowerPermWires`), the **Hadamards** (a
*single-wire gate*, `Evolution.qtowerSingleWire`), and the
**controlled-`Rₖ`** rotations — the circuit's only **two-wire** gate. This file supplies the
wire-addressed placement of a *controlled* single-qubit gate on the tower, the two-wire sibling of
`Evolution.qtowerSingleWire`, with its computational-basis action.

On the tower the QFT's controlled-`Rₖ` gate always has its **control wire above its target wire**:
in the register (little-endian `finFunctionFinEquiv`) target `t` is driven by the later control
wires `c > t`, and the register bridge reverses the wire order (`Fin.rev`), so on the tower the
control lands at index `c.rev < t.rev`. The placement here is therefore built for the
control-above-target configuration `c < t`, the exact shape the QFT produces.

## What is formalised

* `Evolution.qtowerCtrlWire n c t g` — the **controlled single-wire gate**: control wire `c`, target
  wire `t`, applying the single-qubit `Evolution` `g` to wire `t` when wire `c` is `|1⟩`, the
  identity on every other wire (and the identity when the control is `|0⟩`). Defined by recursion on
  the tower peeling the head wire: when the control is the head (`c = 0`, `t = t'+1`) it is
  `controlledUnitary (Evolution.qtowerSingleWire n t' g)` — control on the head, the single-wire
  gate on the tail; when the head is idle (`c = c'+1`, `t = t'+1`) it wraps the tail placement with
  an idle head, `(Evolution.qtowerCtrlWire n c' t' g).onRight qubit`. (The residual cases —
  `t = 0`, or a one-wire tower — cannot arise under `c < t`; the definition returns `Evolution.id`
  there.) The two-wire analogue of `Evolution.qtowerSingleWire`, built on the same head-peel
  `qtower (n+1) qubit = qubit ⊗ qtower n qubit`.
* `Evolution.qtowerCtrlWire_ctrl_zero` / `_ctrl_succ` — the two head-peel unfoldings above.
* `qtowerCtrlWire_evolvePure_towerKet` — the **action** (for `c < t`): `Evolution.qtowerCtrlWire n c
  t g` sends the computational tower basis state `towerKet n b` to `g` applied to wire `t` when the
  control bit `b c` is `1`, and to `towerKet n b` unchanged otherwise:

    `(qtowerCtrlWire n c t g) (towerKet n b)`
      `= if b c = 1 then towerProd n (Function.update (fun j => |b j⟩) t (g |b t⟩))`
      `  else towerKet n b`.

  So the placement fires exactly on the `|1⟩` branch of its control wire, and there acts as a
  single-wire gate on the target — touching only wires `c` and `t`. This is the form the
  wire-addressed re-expression of the Figure 5.1 controlled-`Rₖ` rotations (read on the tower
  through the register bridge, in `AxQM/Core/QftTowerControlled.lean`) is matched against.

## The proof

`qtowerCtrlWire_evolvePure_towerKet` is a recursion on the tower peeling the head wire, exactly the
shape of `qtowerSingleWire_evolvePure_towerProd` and `mcCtrl_evolvePure_ctrlTower`. Since `c < t`
forces `t = t'+1`, the outer wire is never the target; casing the control splits the step:

* control is the head (`c = 0`): `controlledUnitary`'s `|0⟩`/`|1⟩` basis action
  (`controlledUnitary_evolvePure_ketZero` / `_ketOne`) reads the control bit `b 0`, and on the `|1⟩`
  branch `qtowerSingleWire_evolvePure_towerKet` places `g` on the tail's wire `t'`;
* the head is idle (`c = c'+1`): `Evolution.onRight_evolvePure` peels it and the inductive
  hypothesis (at `c' < t'`, from `Fin.succ_lt_succ_iff`) handles the tail, the control bit
  `b c'.succ = b c` unchanged.

The head/tail bookkeeping — reassembling a `towerProd (n+1)` over an updated wire `t'+1` from its
head `|b 0⟩` and the tail update on wire `t'` — is the shared `towerProd_head_update` step, matching
`Function.update` across `Fin.tail` with `Fin.tail_update_succ` (as in
`AxQM/Core/QftTowerHadamard.lean`).

-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A controlled single-qubit gate placed on a wire pair of the control tower** `qtower n qubit`:
control wire `c`, target wire `t`, applying the single-qubit gate `g` to wire `t` when wire `c` is
`|1⟩` and the identity everywhere else. Defined by recursion on the tower peeling the head wire —
when the control is the head (`c = 0`, `t = t'+1`) it is `controlledUnitary` of the single-wire gate
on the tail, `controlledUnitary (Evolution.qtowerSingleWire n t' g)`; when the head is idle
(`c = c'+1`, `t = t'+1`) it wraps the tail placement with an idle head,
`(Evolution.qtowerCtrlWire n c' t' g).onRight qubit`. The residual cases (`t = 0`, or a one-wire
tower) cannot arise under the intended `c < t`; the definition returns `Evolution.id` there. The
two-wire sibling of `Evolution.qtowerSingleWire`, the shape of the Figure 5.1 controlled-`Rₖ` gates;
its basis action is `qtowerCtrlWire_evolvePure_towerKet`. -/
def Evolution.qtowerCtrlWire :
    (n : ℕ) → Fin (n + 1) → Fin (n + 1) → Evolution qubit → Evolution (qtower n qubit)
  | 0, _, _, _ => Evolution.id
  | n + 1, c, t, g =>
      Fin.cases Evolution.id
        (fun t' =>
          Fin.cases (controlledUnitary (Evolution.qtowerSingleWire n t' g))
            (fun c' => (Evolution.qtowerCtrlWire n c' t' g).onRight qubit) c)
        t

/-- Control-head unfolding: on control wire `0` and target wire `t'+1` the controlled single-wire
gate is `controlledUnitary` of the single-wire gate placed on the tail's wire `t'`,
`controlledUnitary (Evolution.qtowerSingleWire n t' g)`. -/
theorem Evolution.qtowerCtrlWire_ctrl_zero (n : ℕ) (t' : Fin (n + 1)) (g : Evolution qubit) :
    Evolution.qtowerCtrlWire (n + 1) 0 t'.succ g
      = controlledUnitary (Evolution.qtowerSingleWire n t' g) := by
  erw [Evolution.qtowerCtrlWire, Fin.cases_succ, Fin.cases_zero]

/-- Idle-head unfolding: on control wire `c'+1` and target wire `t'+1` the controlled single-wire
gate wraps the tail placement with an idle head,
`(Evolution.qtowerCtrlWire n c' t' g).onRight qubit`. -/
theorem Evolution.qtowerCtrlWire_ctrl_succ (n : ℕ) (c' t' : Fin (n + 1)) (g : Evolution qubit) :
    Evolution.qtowerCtrlWire (n + 1) c'.succ t'.succ g
      = (Evolution.qtowerCtrlWire n c' t' g).onRight qubit := by
  erw [Evolution.qtowerCtrlWire, Fin.cases_succ, Fin.cases_succ]

/-- **Computational action of the controlled single-wire gate on a basis input.** For a control wire
`c` above its target wire `t` (`c < t`), placing the controlled gate on the pair `(c, t)` sends the
computational tower basis state `towerKet n b` to `g` applied to wire `t` when the control bit `b c`
is `1`, and to `towerKet n b` unchanged otherwise:

  `(qtowerCtrlWire n c t g) (towerKet n b)`
    `= if b c = 1 then towerProd n (Function.update (fun j => |b j⟩) t (g |b t⟩))`
    `  else towerKet n b`.

So the gate fires exactly on the `|1⟩` branch of its control wire, and there acts as the single-wire
gate `g` on the target wire, leaving every other wire (and, on the `|0⟩` branch, the target too)
fixed — it touches only wires `c` and `t`. Proved by recursion on the tower peeling the head wire:
since `c < t` forces `t = t'+1`, the head is never the target, and casing the control uses either
`controlledUnitary`'s `|0⟩`/`|1⟩` basis action with `qtowerSingleWire_evolvePure_towerKet` on the
tail (control head), or `Evolution.onRight_evolvePure` with the inductive hypothesis (idle head).
This is the form the Figure 5.1 controlled-`Rₖ` gates — read on the tower through the register
bridge — are re-expressed against. -/
theorem qtowerCtrlWire_evolvePure_towerKet (n : ℕ) (c t : Fin (n + 1)) (hct : c < t)
    (g : Evolution qubit) (b : Fin (n + 1) → Fin 2) :
    (Evolution.qtowerCtrlWire n c t g).evolvePure (towerKet n b)
      = if b c = 1 then
          towerProd n
            (Function.update (fun j => qubitBasis (b j)) t (g.evolvePure (qubitBasis (b t))))
        else towerKet n b := by
  induction n with
  | zero =>
      obtain rfl := Fin.fin_one_eq_zero c
      obtain rfl := Fin.fin_one_eq_zero t
      exact absurd hct (lt_irrefl 0)
  | succ n ih =>
      -- Reassemble a `towerProd (n+1)` over an updated wire `t'+1` from head and tail update.
      have towerProd_head_update : ∀ (t' : Fin (n + 1)) (χ : PureState qubit),
          towerProd (n + 1) (Function.update (fun j => qubitBasis (b j)) t'.succ χ)
            = (qubitBasis (b 0)).tmul
                (towerProd n (Function.update (fun j => qubitBasis (b j.succ)) t' χ)) := by
        intro t' χ
        rw [towerProd_succ, Fin.tail_update_succ, Function.update_of_ne (Fin.succ_ne_zero t').symm]
        rfl
      -- `c < t` forces `t = t'+1`; the head wire is never the target. Case the control.
      revert hct
      refine Fin.cases (fun hct => absurd hct (Fin.not_lt_zero c)) (fun t' => ?_) t
      refine Fin.cases (fun _ => ?_) (fun c' hct => ?_) c
      · -- control is the head wire `0`; target `t'+1`. Expose `qtower (n+1) = qubit ⊗ qtower n`.
        change (controlledUnitary (Evolution.qtowerSingleWire n t' g)).evolvePure
          (towerKet (n + 1) b) = _
        rw [towerKet_succ]
        by_cases h0 : b 0 = 1
        · erw [ite_eq_left h0, towerProd_head_update, h0, controlledUnitary_evolvePure_ketOne,
            qtowerSingleWire_evolvePure_towerKet]
        · erw [ite_eq_right h0]
          have h0' : b 0 = 0 := by omega
          rw [h0', controlledUnitary_evolvePure_ketZero]
      · -- head wire idle; recurse on the tail with `c' < t'`.
        change ((Evolution.qtowerCtrlWire n c' t' g).onRight qubit).evolvePure
          (towerKet (n + 1) b) = _
        rw [towerKet_succ, Evolution.onRight_evolvePure, ih c' t' (Fin.succ_lt_succ_iff.mp hct)]
        by_cases hc : b c'.succ = 1
        · erw [ite_eq_left hc, ite_eq_left hc, towerProd_head_update]
        · erw [ite_eq_right hc, ite_eq_right hc, ← towerKet_succ]

end AxQM
