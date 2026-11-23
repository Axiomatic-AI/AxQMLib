/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudgetSingleWire
import AxQM.Core.QftRegisterBridge
import AxQM.Postulates.API.NMRControlledZ

/-!
# The global-phase gate is one single-qubit gate (N&C Problem 4.3(6))

The global-phase gate `globalPhaseGate α = e^{iα} · 1` (`Postulates/API/NMRControlledZ`) multiplies
every state vector of the register by a fixed unit-modulus scalar. In N&C Problem 4.3's Trotter
construction it is the summand corresponding to the **identity Pauli string** `g = I^{⊗n}`: the
propagator `exp(-i h_I · I · Δ) = e^{-i h_I Δ} · 1` is exactly such a global phase. To count the
Figure-4.19 Trotter circuit with the elementary-gate budget `CircuitBudget` (`Core/CircuitBudget`),
that identity summand — like every other summand — needs an honest gate count.

This file supplies it:

* `globalPhaseGate_circuitBudget` — for every register `qudit (2ⁿ⁺¹)` and phase `α`,
  `CircuitBudget (globalPhaseGate α : Evolution (qudit (2ⁿ⁺¹))) 0 1`: **one single-qubit gate**, no
  `≤ 2`-control gates. A global phase `e^{iα} · 1` on the whole register is realised as the scalar
  single-qubit gate `e^{iα} · 1₂` placed on one wire — `(e^{iα} · 1₂) ⊗ 1 = e^{iα} · 1` — which the
  single-wire tower budget `qtowerSingleWire_circuitBudget` counts as one single-qubit gate.

## Proof route (the reachable `R_z`-rotation budget's global-phase analogue)

Mirroring `rotZWireEvolution_circuitBudget`, the register gate is transported onto the `(n+1)`-qubit
control tower `qtower n qubit` along the register bridge `quditPowTower n` and counted there:

* `Evolution.congr_globalPhaseGate` (in `Postulates/API/NMRControlledZ`, beside `globalPhaseGate`) —
  the global phase is **invariant under transport**: for any system isomorphism `e`,
  `Evolution.congr e (globalPhaseGate α) = globalPhaseGate α`, because `Evolution.congr` conjugates
  the operator by the (linear, unital) `conjStarAlgEquiv`, and conjugating the scalar `e^{iα} · 1`
  leaves it fixed (`map_smul`/`map_one`). So the transported register phase is the tower phase.
* `qtowerSingleWire_zero_globalPhaseGate` — placing the one-qubit phase gate on the head wire is the
  whole-tower phase: `qtowerSingleWire n 0 (globalPhaseGate α) = globalPhaseGate α`, since
  `(e^{iα} · 1₂) ⊗ 1 = e^{iα} · 1` (the `n = 0` tower is a single qubit, giving the phase directly;
  the `n+1` case is the head-wire placement `g ⊗ 1`, discharged by the structural lemma
  `globalPhaseGate_onLeft`).

Transport gives a tower budget from `qtowerSingleWire_circuitBudget n 0 (globalPhaseGate α)`, which
`CircuitBudget.congr (quditPowTower n).symm` carries back onto the register.

The wire-gate budgets this one mirrors are in `CircuitBudgetSingleWire` and
`CnotFanEvolutionBudget`.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **Placing the one-qubit global phase on the head wire is the whole-tower global phase.**
`Evolution.qtowerSingleWire n 0 (globalPhaseGate α) = globalPhaseGate α` on `qtower n qubit`: the
scalar phase `e^{iα} · 1₂` on wire `0`, tensored with the identity on the remaining wires, is the
register-wide phase `(e^{iα} · 1₂) ⊗ 1 = e^{iα} · 1`. On the single-qubit tower (`n = 0`) the gate
*is* the phase; on `qtower (m+1) qubit` the head-wire placement `g.onLeft (qtower m qubit) = g ⊗ 1`
is the same global phase by the structural lemma `globalPhaseGate_onLeft`. -/
theorem qtowerSingleWire_zero_globalPhaseGate (n : ℕ) (α : ℝ) :
    Evolution.qtowerSingleWire n 0 (globalPhaseGate α)
      = (globalPhaseGate α : Evolution (qtower n qubit)) := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [Evolution.qtowerSingleWire_zero]
    exact globalPhaseGate_onLeft α qubit (qtower m qubit)

/-- **Problem 4.3(6): the global-phase gate costs one single-qubit gate.** For every register
`qudit (2ⁿ⁺¹)` and phase `α`,

  `CircuitBudget (globalPhaseGate α : Evolution (qudit (2ⁿ⁺¹))) 0 1`

— at most one single-qubit gate and no `≤ 2`-control gates. This is the identity-Pauli-string
summand `exp(-i h_I · I · Δ) = e^{-i h_I Δ} · 1` of the N&C Trotter product, counted as the single
single-qubit gate that realises a global phase (`e^{iα} · 1₂` on one wire).

Proof: transport onto the control tower via `quditPowTower n` — the phase is transport-invariant
(`Evolution.congr_globalPhaseGate`), so the register phase becomes the tower phase; that tower phase
is the head-wire placement `qtowerSingleWire n 0 (globalPhaseGate α)`
(`qtowerSingleWire_zero_globalPhaseGate`), which `qtowerSingleWire_circuitBudget` budgets `0 1`;
then `CircuitBudget.congr (quditPowTower n).symm` carries the budget back onto the register. The
`R_z`-rotation budget `rotZWireEvolution_circuitBudget`'s global-phase analogue. -/
theorem globalPhaseGate_circuitBudget (n : ℕ) (α : ℝ) :
    CircuitBudget (globalPhaseGate α : Evolution (qudit (2 ^ (n + 1)))) 0 1 := by
  rw [← Evolution.congr_symm_congr (quditPowTower n) (globalPhaseGate α),
    Evolution.congr_globalPhaseGate]
  refine CircuitBudget.congr (quditPowTower n).symm ?_
  rw [← qtowerSingleWire_zero_globalPhaseGate n α]
  exact qtowerSingleWire_circuitBudget n 0 (globalPhaseGate α)

end

end AxQM
