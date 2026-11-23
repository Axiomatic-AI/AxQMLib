/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudgetOnRight
import AxQM.Core.QtowerSingleWireGate
import AxQM.Postulates.API.MeasureObservableRegister
import AxQM.Postulates.API.CompositeReducedEvolution

/-!
# A single-qubit gate on *any* tower wire costs one single-qubit gate (N&C Problem 4.1)

The elementary-gate budget `CircuitBudget E t s` (`Core/CircuitBudget`) has a leaf, `single`, for a
single-qubit gate on the **deepest** wire of the control tower (`(unCtrl d g).onRight qubit`), and
the idle-front closure `CircuitBudget.onRight` (`Core/CircuitBudgetOnRight`) that prepends one idle
head wire. Assembling Problem 4.1's phase layer `D` gate-by-gate needs a single-qubit gate on
**each** ancilla wire, not just the deepest one: the phase layer read on the tower is
`∏ₜ qtowerSingleWire n t.rev (phaseShiftGate (φ t))` (`quditPowTower_congr_phaseGradientLayer`), one
`Evolution.qtowerSingleWire` per wire `t.rev` ranging over **all** of `Fin (n+1)`.
This file proves that **placing a single-qubit gate on any tower wire costs
exactly one single-qubit gate.**

* `qtowerSingleWire_zero_circuitBudget` — the **head-wire budget**: for every tower depth `m`,
  `CircuitBudget (g.onLeft (qtower m qubit)) 0 1` — a single-qubit gate `g` on wire `0` (the head)
  of `qtower (m+1) qubit`. By induction on `m`: the base `g.onLeft qubit` is the bare gate wrapped
  by one idle wire and swapped to the front (`CircuitBudget.bare`, `CircuitBudget.onRight`,
  `Evolution.tmul_congr_comm` on the braiding `QSystem.Iso.comm`); the step re-associates one more
  idle wire to the front with the middle-factor braiding
  `Evolution.congr_leftComm_onLeft_onRight`, `congr (leftComm) ((g.onLeft _).onRight qubit) =
  g.onLeft (qubit ⊗ _)`, keeping the budget via `CircuitBudget.congr`.

* `qtowerSingleWire_circuitBudget` — **main result**: `CircuitBudget (qtowerSingleWire n i g) 0 1`
  for an arbitrary wire `i : Fin (n+1)`. By induction on `n` with `Fin.cases` on `i` over the
  `qtowerSingleWire` recursion: at the single-qubit tower (`n = 0`) it is the bare gate
  (`CircuitBudget.bare`, since `qtowerSingleWire 0 i g = g`); on wire `0` it is the head-wire budget
  (`qtowerSingleWire_zero`); on wire `i'+1` it peels the idle head wire and applies the induction
  hypothesis under `CircuitBudget.onRight` (`qtowerSingleWire_succ`). This makes each of Problem
  4.1's `n` single-qubit phase gates an honest `0 1` budget, whatever wire it sits on — the reusable
  step feeding the phase-layer budget `CircuitBudget (I_A ⊗ D) 0 n`.

Placing the *same* single-qubit gate on a different wire is one single-qubit gate either way: the
`CircuitBudget.congr` transports here relabel the register through **system isomorphisms** (the
tensor-factor braidings `comm` / `leftComm`), never insert a physical swap, so no gate is hidden.

The idle-front closure it builds on is in `AxQM/Core/CircuitBudgetOnRight.lean`, and the
wire-addressed gate it budgets is in `AxQM/Core/QtowerSingleWireGate.lean`.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **The head-wire budget** (N&C Problem 4.1). A single-qubit gate `g` placed on wire `0` (the
head) of the control tower — `g.onLeft (qtower m qubit) = g ⊗ 1` on `qtower (m+1) qubit` — is one
single-qubit gate: `CircuitBudget (g.onLeft (qtower m qubit)) 0 1`.

Proved by induction on the tower depth `m`. The base `m = 0` is the bare gate `g` wrapped by one
idle wire on the right (`CircuitBudget.bare` then `CircuitBudget.onRight`, giving `1 ⊗ g`), then
swapped to the front by the braiding `QSystem.Iso.comm` (`Evolution.tmul_congr_comm`:
`congr comm (1 ⊗ g) = g ⊗ 1`). The step re-associates one further idle wire to the front: the IH on
the
depth-`m` tower gets an idle head wire via `CircuitBudget.onRight`, then the middle-factor braiding
`Evolution.congr_leftComm_onLeft_onRight` (`congr (leftComm qubit qubit _) ((g.onLeft _).onRight
qubit) = g.onLeft (qubit ⊗ _)`) carries it into the depth-`m+1` head position, the budget preserved
by `CircuitBudget.congr`. -/
theorem qtowerSingleWire_zero_circuitBudget :
    ∀ (m : ℕ) (g : Evolution qubit),
      CircuitBudget (g.onLeft (qtower m qubit)) 0 1
  | 0, g => by
      -- base: `g ⊗ 1 = congr comm (1 ⊗ g)`, where `1 ⊗ g = g.onRight qubit` is the idle-front bare
      have hbudget : CircuitBudget (Evolution.congr (QSystem.Iso.comm qubit qubit)
          (g.onRight qubit)) 0 1 := CircuitBudget.congr _ (CircuitBudget.bare g).onRight
      have heq : Evolution.congr (QSystem.Iso.comm qubit qubit) (g.onRight qubit)
          = g.onLeft qubit := Evolution.tmul_congr_comm Evolution.id g
      rwa [heq] at hbudget
  | m + 1, g => by
      -- step: peel an idle head wire off the depth-`m` head gate, then braid it to the front
      have h : CircuitBudget ((g.onLeft (qtower m qubit)).onRight qubit) 0 1 :=
        (qtowerSingleWire_zero_circuitBudget m g).onRight
      have hbudget := CircuitBudget.congr
        (QSystem.Iso.leftComm qubit qubit (qtower m qubit)) h
      rwa [Evolution.congr_leftComm_onLeft_onRight] at hbudget

/-- **A single-qubit gate on any tower wire costs one single-qubit gate** (N&C Problem 4.1, the `n`
single-qubit gates of the `2T + n` count). For every wire `i : Fin (n+1)` of the control tower
`qtower n qubit`, placing a single-qubit gate there has budget `CircuitBudget (qtowerSingleWire n i
g) 0 1` — at most one single-qubit gate, no `≤ 2`-control gates.

Proved by induction on `n` with `Fin.cases` on the wire `i`, following the `qtowerSingleWire`
recursion: when the tower is a single qubit (`n = 0`, `qtowerSingleWire 0 i g = g`) it is the bare
leaf `CircuitBudget.bare`; on the head wire (`i = 0`, `qtowerSingleWire_zero`) it is the head-wire
budget `qtowerSingleWire_zero_circuitBudget`; on a later wire (`i = i'+1`, `qtowerSingleWire_succ`)
the placement peels an idle head wire, so the induction hypothesis on the depth-`n` tower is lifted
by the idle-front closure `CircuitBudget.onRight`.

This is the reusable per-wire budget the phase-layer assembly folds over: each single-qubit phase
gate `qtowerSingleWire n t.rev (phaseShiftGate (φ t))` of Problem 4.1's phase gradient contributes
exactly `0 1`, whatever wire `t.rev` it sits on. -/
theorem qtowerSingleWire_circuitBudget :
    ∀ (n : ℕ) (i : Fin (n + 1)) (g : Evolution qubit),
      CircuitBudget (Evolution.qtowerSingleWire n i g) 0 1
  | 0, _, g => CircuitBudget.bare g
  | n + 1, i, g => by
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Evolution.qtowerSingleWire_zero]
        exact qtowerSingleWire_zero_circuitBudget n g
      · rw [Evolution.qtowerSingleWire_succ]
        exact (qtowerSingleWire_circuitBudget n i' g).onRight

end

end AxQM
