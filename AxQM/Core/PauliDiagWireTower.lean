/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliDiagWire
import AxQM.Core.CircuitBudgetSingleWire
import AxQM.Core.QftTowerHadamard
import AxQM.Core.PhaseLayerBudget

/-!
# The Problem 4.3(3) basis-change gate on a register wire is one single-qubit gate on the tower

Problem 4.3(3)'s basis-change layer `B = ⨂ₖ B_{gₖ}` is built from the per-wire gates
`pauliDiagWireEvolution n t (g t)` (`Postulates/API/PauliDiagWire`) on the flat `2ⁿ`-level register
`qudit (2ⁿ)`; the elementary-gate accountant `CircuitBudget` (`Core/CircuitBudget`) instead counts
gates on the qubit control tower. This file transports each such wire gate across the register
bridge `quditPowTower n` onto the tower — where its budget lives — and reads off its cost. It is the
basis-change analogue of `Core/PhaseWireTower` (the phase gate) and `Core/QftTowerHadamard` (the
Hadamard), specialised to the Problem 4.3 diagonalising gates `pauliDiagGate a`.

## What is formalised

* `quditPowTower_congr_pauliDiagWireEvolution` — **the register lift.** Transporting the register
  gate `pauliDiagWireEvolution (n+1) t a` onto the `(n+1)`-qubit control tower via `quditPowTower n`
  yields exactly the single-wire gate applying the grounded gate `pauliDiagGateEvolution a` to tower
  wire `t.rev`:

    `Evolution.congr (quditPowTower n) (pauliDiagWireEvolution (n+1) t a)`
      `= Evolution.qtowerSingleWire n t.rev (pauliDiagGateEvolution a)`.

  The `Fin.rev` reconciles the big-endian register bridge with the little-endian wire-indexing. The
  exact analogue of `quditPowTower_congr_qftHadamardEvolution` with the Hadamard block replaced by
  `pauliDiagGate a`: on each basis input both sides give `∑_z (pauliDiagGate a) z (b t.rev) ·
  towerKet n (update b t.rev z)` (register side `pauliDiagWireEvolution_evolvePure_quditBasis`,
  single-wire side `pauliDiagGateEvolution_evolvePure_qubitBasis_sum`), matched through the tensor
  multilinearity of the tower product state.

* `pauliDiagWireEvolution_circuitBudget` — **the per-wire budget**:
  `CircuitBudget (pauliDiagWireEvolution (n+1) t a) 0 1` — the basis-change gate on any wire of the
  `2ⁿ⁺¹`-level register costs at most one single-qubit gate and no `≤ 2`-control gates, whatever the
  Pauli `a` and wire `t`. Proved by transporting the budget across the register bridge: the register
  lift makes the transported gate the tower single-wire gate
  `qtowerSingleWire n t.rev (pauliDiagGateEvolution a)`, whose budget is
  `qtowerSingleWire_circuitBudget`, then `CircuitBudget.congr` carries it back off the tower. This
  is the per-wire cost the basis-change layer `B = ∏ₜ pauliDiagWireEvolution n t (g t)`
  folds with `CircuitBudget.listProd` to obtain `CircuitBudget B 0 n` — the `n` single-qubit gates
  of Problem 4.3(3).

* `quditPowTower_congr_pauliDiagLayer` — **the layer bridge**: the whole basis-change layer
  `pauliDiagLayer (n+1) g` (`Postulates/API/PauliDiagWire`), read on the tower, is the ordered
  product of the `n+1` single-wire gates `qtowerSingleWire n t.rev (pauliDiagGateEvolution (g t))`.
  The basis-change analogue of `quditPowTower_congr_phaseGradientLayer`, via `Evolution.congr_prod`
  and the per-wire bridge above.

* `pauliDiagLayer_circuitBudget` — **the layer budget**:
  `CircuitBudget (pauliDiagLayer (n+1) g) 0 (n+1)` — the whole basis-change layer `B = ⨂ₖ B_{gₖ}`
  costs at most `n+1` single-qubit gates and no `≤ 2`-control gates. Transports the layer onto the
  tower (`quditPowTower_congr_pauliDiagLayer`), folds the per-wire budgets with
  `CircuitBudget.listProd` (base `CircuitBudget.id_qtower`), and carries the budget back off the
  tower. Together with the faithfulness `pauliDiagLayer_op` (`Postulates/API/PauliDiagWire`), this
  is Problem 4.3(3)'s basis-change layer counted as its `n` single-qubit gates.

The proof mirrors that of `Core/QftTowerHadamard`; the per-wire tower budget it transports is in
`Core/CircuitBudgetSingleWire`, and the wire gates and their basis actions are defined in
`Postulates/API/PauliDiagWire`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The transported Problem 4.3(3) basis-change wire gate is the grounded gate on tower wire
`t.rev`.** Transporting the register gate `pauliDiagWireEvolution (n+1) t a` (the diagonalising gate
`pauliDiagGate a` on register wire `t`) onto the `(n+1)`-qubit control tower via the register bridge
`quditPowTower n` yields exactly the single-wire gate applying `pauliDiagGateEvolution a` to tower
wire `t.rev`:

  `Evolution.congr (quditPowTower n) (pauliDiagWireEvolution (n+1) t a)`
    `= Evolution.qtowerSingleWire n t.rev (pauliDiagGateEvolution a)`.

The basis-change analogue of `quditPowTower_congr_qftHadamardEvolution` /
`quditPowTower_congr_phaseWireEvolution` (whose gate blocks are the Hadamard and the phase gate).
Proved through the combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`: both the single-wire
gate (via `qtowerSingleWire_evolvePure_towerKet` and the shared tower-product multilinearity
`towerProd_vec_update_sum_smul`) and the transported register gate (via
`pauliDiagWireEvolution_evolvePure_quditBasis`, the bridge isometry, and the dictionary
`quditPowTower_congr_quditBasis_apply`) send `towerKet n b` to the two-term superposition
`∑_z (pauliDiagGate a) z (b t.rev) · towerKet n (Function.update b t.rev z)`, the two `Fin.rev`s
collapsing by `Fin.rev_rev`.
-/
theorem quditPowTower_congr_pauliDiagWireEvolution (n : ℕ) (t : Fin (n + 1)) (a : Fin 4) :
    Evolution.congr (quditPowTower n) (pauliDiagWireEvolution (n + 1) t a)
      = Evolution.qtowerSingleWire n t.rev (pauliDiagGateEvolution a) := by
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  apply PureState.ext
  rw [qtowerSingleWire_evolvePure_towerKet, PureState.congr_vec,
    pauliDiagWireEvolution_evolvePure_quditBasis,
    towerProd_vec_update_sum_smul n (fun j => qubitBasis (b j)) t.rev
      (fun z => Concrete.pauliDiagGate a z (b t.rev)) qubitBasis
      ((pauliDiagGateEvolution a).evolvePure (qubitBasis (b t.rev)))
      (pauliDiagGateEvolution_evolvePure_qubitBasis_sum a (b t.rev)),
    map_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [map_smul, towerProd_update_qubitBasis b t z, ← PureState.congr_vec,
    quditPowTower_congr_quditBasis_apply, update_rev_eq b t z]

/-- **The Problem 4.3(3) basis-change gate on any wire costs one single-qubit gate.** For every wire
`t : Fin (n+1)` of the `2ⁿ⁺¹`-level register and every Pauli `a : Fin 4`, placing the diagonalising
gate `pauliDiagGate a` on wire `t` has budget

  `CircuitBudget (pauliDiagWireEvolution (n+1) t a) 0 1`

— at most one single-qubit gate and no `≤ 2`-control gates. Proved by transporting the budget across
the register bridge: `quditPowTower_congr_pauliDiagWireEvolution` makes the transported gate the
tower single-wire gate `qtowerSingleWire n t.rev (pauliDiagGateEvolution a)`, whose budget is
`qtowerSingleWire_circuitBudget`, and `CircuitBudget.congr` carries the budget back off the tower
(the register round-trip `Evolution.congr_symm_congr`). This is the per-wire cost the basis-change
layer `B = ∏ₜ pauliDiagWireEvolution n t (g t)` folds with `CircuitBudget.listProd` to obtain
`CircuitBudget B 0 n` — the `n` single-qubit gates of Problem 4.3(3). -/
theorem pauliDiagWireEvolution_circuitBudget (n : ℕ) (t : Fin (n + 1)) (a : Fin 4) :
    CircuitBudget (pauliDiagWireEvolution (n + 1) t a) 0 1 := by
  rw [← Evolution.congr_symm_congr (quditPowTower n) (pauliDiagWireEvolution (n + 1) t a),
    quditPowTower_congr_pauliDiagWireEvolution]
  exact CircuitBudget.congr (quditPowTower n).symm
    (qtowerSingleWire_circuitBudget n t.rev (pauliDiagGateEvolution a))

/-- **The transported basis-change layer is the ordered product of single-wire gates on the tower.**
Transporting the whole register basis-change layer `pauliDiagLayer (n+1) g` — the product of the
`n+1` per-wire diagonalising gates on the flat register `qudit (2ⁿ⁺¹)` — onto the qubit control
tower `qtower n qubit` yields the ordered product of the `n+1` single-qubit gates
`pauliDiagGateEvolution (g t)` placed on tower wire `t.rev`:

  `Evolution.congr (quditPowTower n) (pauliDiagLayer (n+1) g)`
    `= ((List.finRange (n+1)).map fun t => Evolution.qtowerSingleWire n t.rev
        (pauliDiagGateEvolution (g t))).prod`.

The basis-change analogue of `quditPowTower_congr_phaseGradientLayer` (the phase gate replaced by
the diagonalising gate `pauliDiagGateEvolution (g t)`). It follows from the per-wire bridge
`quditPowTower_congr_pauliDiagWireEvolution` and the monoid-homomorphism property
`Evolution.congr_prod` of the register transport, which pushes the transport through the list
product gate-by-gate. -/
theorem quditPowTower_congr_pauliDiagLayer (n : ℕ) (g : Fin (n + 1) → Fin 4) :
    Evolution.congr (quditPowTower n) (pauliDiagLayer (n + 1) g)
      = ((List.finRange (n + 1)).map
          (fun t => Evolution.qtowerSingleWire n t.rev (pauliDiagGateEvolution (g t)))).prod := by
  rw [pauliDiagLayer, Evolution.congr_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun t _ => ?_)
  simpa only [Function.comp_apply] using quditPowTower_congr_pauliDiagWireEvolution n t (g t)

/-- **Problem 4.3(3)'s basis-change layer is `n+1` single-qubit gates.** For any Pauli string
`g : Fin (n+1) → Fin 4`, the basis-change layer `pauliDiagLayer (n+1) g` on the `(n+1)`-qubit
register `qudit (2ⁿ⁺¹)` — the product of the `n+1` per-wire diagonalising gates
`pauliDiagWireEvolution (n+1) t (g t)` — has budget

  `CircuitBudget (pauliDiagLayer (n+1) g) 0 (n+1)`:

at most `n+1` single-qubit gates and **no** `≤ 2`-control gates. This is the `O(n)` single-qubit
basis-change cost that opens Problem 4.3(3)'s circuit, made a genuine `CircuitBudget`; combined with
`pauliDiagLayer_op` it shows the tensor basis change `B = ⨂ₖ B_{gₖ}` is implemented by exactly `n+1`
single-qubit gates.

Proof (the analogue of `phaseGradientLayer_circuitBudget`): transport the layer onto the qubit
control tower via `quditPowTower_congr_pauliDiagLayer`, where it is the ordered product of the `n+1`
single-wire gates `qtowerSingleWire n t.rev (pauliDiagGateEvolution (g t))`, each budgeted `0 1` by
`qtowerSingleWire_circuitBudget`; fold those with `CircuitBudget.listProd` (base
`CircuitBudget.id_qtower`) to get `0 (n+1)`; then carry the budget back off the tower with
`CircuitBudget.congr (quditPowTower n).symm` and `Evolution.congr_symm_congr`. -/
theorem pauliDiagLayer_circuitBudget (n : ℕ) (g : Fin (n + 1) → Fin 4) :
    CircuitBudget (pauliDiagLayer (n + 1) g) 0 (n + 1) := by
  rw [← Evolution.congr_symm_congr (quditPowTower n) (pauliDiagLayer (n + 1) g),
    quditPowTower_congr_pauliDiagLayer]
  refine CircuitBudget.congr (quditPowTower n).symm ?_
  have hbud := CircuitBudget.listProd (CircuitBudget.id_qtower n)
    ((List.finRange (n + 1)).map
      (fun t => Evolution.qtowerSingleWire n t.rev (pauliDiagGateEvolution (g t))))
    (by
      intro E hE
      simp only [List.mem_map] at hE
      obtain ⟨t, -, rfl⟩ := hE
      exact qtowerSingleWire_circuitBudget n t.rev (pauliDiagGateEvolution (g t)))
  rwa [List.length_map, List.length_finRange] at hbud

end AxQM

end
