/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FourGateReachableWire
import AxQM.Core.QftTowerHadamard

/-!
# The reachable single-qubit rotations as rotation gates on a tower wire (N&C Exercise
4.43, register lift)

The universality argument of Exercise 4.43 transfers the abstract density result
`Concrete.exists_phase_smul_mem_closure_reachableCircuits` onto the `H, S, CNOT, Toffoli`
gate set. One generating family of the reachable gate set is the reachable single-qubit rotations
placed on a wire, `Concrete.singleQubitOnWire finFunctionFinEquiv t g` for
`g ∈ Concrete.reachableRotations θ`. This file re-expresses such a **wire gate on the qudit
register** as the rotation **gate on the corresponding tower wire**, relating the matrix-level
generators to the `Evolution` gates, exactly as `AxQM/Core/QftTowerHadamard.lean` does for the
Figure 5.1 Hadamard.

## What is formalised

* `quditPowTower_congr_rotZWireEvolution` / `quditPowTower_congr_rotXWireEvolution` — **the register
  lift for the reachable rotation generators**: the wire-`t` reachable rotation gate on the register
  is, on the tower, the gate `rotZGate θ` (resp. `rotXGate θ`) on the single tower wire
  `t.rev`:

    `Evolution.congr (quditPowTower n) (rotZWireEvolution (n+1) t θ)`
      `= Evolution.qtowerSingleWire n t.rev (rotZGate θ)`.

  The four generators of `Concrete.reachableRotations θ` are `R_z(±θ), R_x(±θ)`, so these two
  families (at `θ` and `-θ`) cover them all: every generator of the reachable single-qubit
  rotations, placed on a register wire, is a rotation gate on a tower wire — a genuine
  one-qubit gate on one wire, built (with measurement) from `H, S, CNOT, Toffoli`.

## Proof

Both are the exact analogue of `quditPowTower_congr_qftHadamardEvolution` (the Figure 5.1
Hadamard on a tower wire) with the Hadamard block replaced by the reachable rotation. Via the
transported-gate re-expression combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`: on every
basis input
`towerKet n b`, both sides produce the two-term superposition
`∑_z (rotZ θ) z (b t.rev) · towerKet n (update b t.rev z)`, the single-wire side via
`qtowerSingleWire_evolvePure_towerKet` and the tensor multilinearity of the tower product state (the
shared `towerProd_vec_update_sum_smul`), the register side via
`rotZWireEvolution_evolvePure_quditBasis`, the bridge isometry, and
`quditPowTower_congr_quditBasis_apply` (the two `Fin.rev`s collapsing by `Fin.rev_rev`). The
register basis action (`rotZWireEvolution_evolvePure_quditBasis`) and the single-qubit column
(`rotZGate_evolvePure_qubitBasis_sum`) are the two matching two-term superpositions, both the column
`((rotZ θ) · , b t.rev)`. The tensor-multilinearity step is the lemma
`towerProd_vec_update_sum_smul` (`AxQM/Postulates/API/TowerProdMultilinear.lean`); the two purely
ket-combinatorial steps are the lemmas `towerProd_update_qubitBasis` / `update_rev_eq`
(`AxQM/Core/QtowerSingleWireGate.lean`). The wire gates and their basis actions are in
`AxQM/Postulates/API/FourGateReachableWire.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The transported reachable wire `z`-rotation is the grounded `z`-rotation on tower wire
`t.rev`.** Transporting the register gate `rotZWireEvolution (n+1) t θ` (the reachable `R_z(θ)` on
register wire `t`) onto the `(n+1)`-qubit control tower via the register bridge `quditPowTower n`
yields exactly the single-wire gate applying the grounded gate `rotZGate θ` to tower wire `t.rev`:

  `Evolution.congr (quditPowTower n) (rotZWireEvolution (n+1) t θ)`
    `= Evolution.qtowerSingleWire n t.rev (rotZGate θ)`.

The register wire gate — a genuine one-qubit gate — is, on the grounded tower, precisely the
reachable `z`-rotation gate on the single wire `t.rev` (the `Fin.rev` reconciling the big-endian
register bridge with the little-endian wire-indexing). The exact analogue of
`quditPowTower_congr_qftHadamardEvolution`, with the Hadamard block replaced by `R_z(θ)`: on each
basis input both sides give `∑_z (rotZ θ) z (b t.rev) · towerKet n (update b t.rev z)` (register
side `rotZWireEvolution_evolvePure_quditBasis`, single-wire side
`rotZGate_evolvePure_qubitBasis_sum`). -/
theorem quditPowTower_congr_rotZWireEvolution (n : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    Evolution.congr (quditPowTower n) (rotZWireEvolution (n + 1) t θ)
      = Evolution.qtowerSingleWire n t.rev (rotZGate θ) := by
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  apply PureState.ext
  rw [qtowerSingleWire_evolvePure_towerKet, PureState.congr_vec,
    rotZWireEvolution_evolvePure_quditBasis,
    towerProd_vec_update_sum_smul n (fun j => qubitBasis (b j)) t.rev
      (fun z => Concrete.rotZ θ z (b t.rev)) qubitBasis
      ((rotZGate θ).evolvePure (qubitBasis (b t.rev)))
      (rotZGate_evolvePure_qubitBasis_sum θ (b t.rev)),
    map_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [map_smul, towerProd_update_qubitBasis b t z, ← PureState.congr_vec,
    quditPowTower_congr_quditBasis_apply, update_rev_eq b t z]

/-- **The transported reachable wire `x`-rotation is the grounded `x`-rotation on tower wire
`t.rev`.** The `x`-axis counterpart of `quditPowTower_congr_rotZWireEvolution`:

  `Evolution.congr (quditPowTower n) (rotXWireEvolution (n+1) t θ)`
    `= Evolution.qtowerSingleWire n t.rev (rotXGate θ)`.

Together with the `z`-axis version (at `θ` and `-θ`) this covers all four generators `R_z(±θ),
R_x(±θ)` of `Concrete.reachableRotations θ`: every reachable single-qubit rotation generator, placed
on a register wire, is a grounded rotation gate on a tower wire. Same proof as the `z`-axis version
with the `R_x(θ)` column (`rotXWireEvolution_evolvePure_quditBasis` /
`rotXGate_evolvePure_qubitBasis_sum`). -/
theorem quditPowTower_congr_rotXWireEvolution (n : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    Evolution.congr (quditPowTower n) (rotXWireEvolution (n + 1) t θ)
      = Evolution.qtowerSingleWire n t.rev (rotXGate θ) := by
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  apply PureState.ext
  rw [qtowerSingleWire_evolvePure_towerKet, PureState.congr_vec,
    rotXWireEvolution_evolvePure_quditBasis,
    towerProd_vec_update_sum_smul n (fun j => qubitBasis (b j)) t.rev
      (fun z => Concrete.rotX θ z (b t.rev)) qubitBasis
      ((rotXGate θ).evolvePure (qubitBasis (b t.rev)))
      (rotXGate_evolvePure_qubitBasis_sum θ (b t.rev)),
    map_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [map_smul, towerProd_update_qubitBasis b t z, ← PureState.congr_vec,
    quditPowTower_congr_quditBasis_apply, update_rev_eq b t z]

end AxQM

end
