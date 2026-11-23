/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PhaseWire
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.TowerProdMultilinear
import AxQM.Core.QtowerSingleWireGate
import AxQM.Core.EvolutionTowerBasisExt
import AxQM.Core.QftTowerBasis

/-!
# Register phase-wire gates as single-qubit phase gates on a tower wire (N&C Problem 4.1, gate-count
bridge)

Problem 4.1's phase layer `D = diagPhase (computablePhaseAngle n)` is, in the textbook construction,
**`n` single-qubit phase gates** — one on each wire of the `n`-qubit ancilla register. The register
side of that decomposition is `phaseGradientLayer n φ` (`Postulates/API/PhaseWire`): the product of
the `n` single-wire phase gates `phaseWireEvolution n t (φ t)` on the *flat* `2ⁿ`-level register
`qudit (2ⁿ)`. The elementary-gate cost model `CircuitBudget` (`Core/CircuitBudget`) instead counts
gates on the **qubit control tower** `qtower n qubit`, where a single-qubit gate is placed by
`Evolution.qtowerSingleWire`. This file supplies the missing register bridge: it transports each
register phase-wire gate — and the whole phase-gradient layer — across the register isomorphism
`quditPowTower n : qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit` onto the tower, where the budget lives.

* `quditPowTower_congr_phaseWireEvolution` — **the per-wire bridge**: transporting the register
  gate `phaseWireEvolution (n+1) t φ` onto the tower gives exactly the grounded single-qubit phase
  gate `phaseShiftGate φ` placed on tower wire `t.rev`:

    `Evolution.congr (quditPowTower n) (phaseWireEvolution (n+1) t φ)`
      `= Evolution.qtowerSingleWire n t.rev (phaseShiftGate φ)`.

  The phase analogue of `quditPowTower_congr_rotZWireEvolution`, with the `z`-rotation replaced by
  the phase gate `P(φ) = diag(1, e^{iφ})`. Because the phase gate is *diagonal*, its basis action
  has no off-diagonal branch: on each computational tower ket `towerKet n b` both sides equal the
  single scalar multiple `(e^{iφ})^{b t.rev} · towerKet n b`, so the proof is a one-scalar
  computation rather than the two-term rotation sum.

* `quditPowTower_congr_phaseGradientLayer` — **the layer bridge**: transporting the whole
  phase-gradient layer `phaseGradientLayer (n+1) φ` gives the ordered product of the `n+1`
  single-wire phase gates on the tower,

    `Evolution.congr (quditPowTower n) (phaseGradientLayer (n+1) φ)`
      `= ((List.finRange (n+1)).map fun t => qtowerSingleWire n t.rev (phaseShiftGate (φ t))).prod`.

  This exhibits Problem 4.1's phase layer, read on the tower, as literally the composition of `n+1`
  single-qubit phase gates — the `n` of the exercise's `2T + n` gate count, now on the register the
  `CircuitBudget` accountant operates on. It follows from the per-wire bridge and the monoid-hom
  property `Evolution.congr_prod` of the transport.

The proof mirrors that of `quditPowTower_congr_rotZWireEvolution` in
`AxQM/Core/FourGateReachableWireTower.lean`; the wire gate `phaseWireEvolution` and its diagonal
basis action are defined in `AxQM/Postulates/API/PhaseWire.lean`.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **The transported register phase-wire gate is the grounded phase gate on tower wire `t.rev`.**
Transporting the register gate `phaseWireEvolution (n+1) t φ` (the single-qubit phase gate
`P(φ) = diag(1, e^{iφ})` on register wire `t`) onto the `(n+1)`-qubit control tower via the register
bridge `quditPowTower n` yields exactly the single-wire gate applying the grounded phase gate
`phaseShiftGate φ` to tower wire `t.rev`:

  `Evolution.congr (quditPowTower n) (phaseWireEvolution (n+1) t φ)`
    `= Evolution.qtowerSingleWire n t.rev (phaseShiftGate φ)`.

The phase analogue of `quditPowTower_congr_rotZWireEvolution`, with the `z`-rotation block replaced
by the phase gate. Because `P(φ)` is diagonal, its basis action has no off-diagonal branch: on each
computational tower ket `towerKet n b`, the single-wire side scales wire `t.rev` by
`(e^{iφ})^{b t.rev}` (`phaseShiftGate_evolvePure_qubitBasis`, pulled through the tower product by
the shared single-wire multilinearity `towerProd_vec_update_smul`), and the register side scales
`|f⟩` by the same `(e^{iφ})^{f t}` with
`f = b ∘ Fin.rev` (`phaseWireEvolution_evolvePure_quditBasis`); both are
`(e^{iφ})^{b t.rev} · towerKet n b` (the `Fin.rev` reconciling the big-endian register bridge with
the little-endian wire indexing, `quditPowTower_congr_quditBasis_rev`). -/
theorem quditPowTower_congr_phaseWireEvolution (n : ℕ) (t : Fin (n + 1)) (φ : ℝ) :
    Evolution.congr (quditPowTower n) (phaseWireEvolution (n + 1) t φ)
      = Evolution.qtowerSingleWire n t.rev (phaseShiftGate φ) := by
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  apply PureState.ext
  -- `phaseShiftGate φ` on wire `t.rev` scales by the single diagonal phase `(e^{iφ})^{b t.rev}`
  -- (`phaseShiftGate_evolvePure_qubitBasis`), pulled through the tower product by
  -- `towerProd_vec_update_smul`; the register side scales `|f⟩` by the same power.
  rw [qtowerSingleWire_evolvePure_towerKet,
    towerProd_vec_update_smul n (fun j => qubitBasis (b j)) t.rev
      (Complex.exp ((φ : ℂ) * Complex.I) ^ ((b t.rev : Fin 2) : ℕ))
      ((phaseShiftGate φ).evolvePure (qubitBasis (b t.rev)))
      (phaseShiftGate_evolvePure_qubitBasis φ (b t.rev)),
    ← towerKet_eq_towerProd, PureState.congr_vec, phaseWireEvolution_evolvePure_quditBasis,
    map_smul, ← PureState.congr_vec, quditPowTower_congr_quditBasis_rev]

/-- **The transported phase-gradient layer is the ordered product of single-wire phase gates on the
tower.** Transporting the whole register phase-gradient layer `phaseGradientLayer (n+1) φ` — the
product of the `n+1` single-wire phase gates on the flat register `qudit (2ⁿ⁺¹)` — onto the qubit
control tower `qtower n qubit` yields the ordered product of the `n+1` single-qubit phase gates
`phaseShiftGate (φ t)` placed on tower wire `t.rev`:

  `Evolution.congr (quditPowTower n) (phaseGradientLayer (n+1) φ)`
    `= (List.finRange (n+1)).map (fun t => qtowerSingleWire n t.rev (phaseShiftGate (φ t)))).prod`.

This is Problem 4.1's phase layer, read on the tower, as **literally the composition of `n+1`
single-qubit phase gates** — the `n` single-qubit gates of the exercise's `2T + n` count, now placed
on the register the `CircuitBudget` accountant counts gates on. It follows from the per-wire bridge
`quditPowTower_congr_phaseWireEvolution` and the monoid-homomorphism property `Evolution.congr_prod`
of the register transport (which pushes the transport through the list product gate-by-gate). -/
theorem quditPowTower_congr_phaseGradientLayer (n : ℕ) (φ : Fin (n + 1) → ℝ) :
    Evolution.congr (quditPowTower n) (phaseGradientLayer (n + 1) φ)
      = ((List.finRange (n + 1)).map
          (fun t => Evolution.qtowerSingleWire n t.rev (phaseShiftGate (φ t)))).prod := by
  rw [phaseGradientLayer, Evolution.congr_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun t _ => ?_)
  simpa only [Function.comp_apply] using quditPowTower_congr_phaseWireEvolution n t (φ t)

end

end AxQM
