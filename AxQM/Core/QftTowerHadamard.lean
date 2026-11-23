/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QftHadamardEvolution
import AxQM.Postulates.API.TowerProdMultilinear
import AxQM.Core.EvolutionTowerBasisExt
import AxQM.Core.QtowerSingleWireGate

/-!
# The QFT Hadamard layer re-expressed as a single-wire gate on the tower (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` as a product of *transported* Figure 5.1 gates
(`qftTowerEvolution_eq_map_congr_prod`). To defer the terminal per-wire measurement
past that product gate by gate, each transported gate must be re-expressed as an honest
**wire-addressed tower `Evolution`**. This file does so for a Figure 5.1 **Hadamard**, the second of
the circuit's three gate shapes (the swap layer is done in `QftTowerSwap`; the controlled-`Rₖ`
rotations follow).

## What is formalised

* `quditPowTower_congr_qftHadamardEvolution` — **the transported Figure 5.1 Hadamard on wire `t` is
  the single-wire Hadamard on tower wire `t.rev`.** Transporting the register Hadamard gate
  `qftHadamardEvolution (n+1) t` (`Postulates/API`) onto the tower through the register bridge
  `quditPowTower n` equals the single-wire gate `Evolution.qtowerSingleWire n t.rev hadamardGate`
  that applies the one-qubit Hadamard to tower wire `t.rev`, the identity on every other wire:

    `Evolution.congr (quditPowTower n) (qftHadamardEvolution (n+1) t)`
      `= Evolution.qtowerSingleWire n t.rev hadamardGate`.

  So the QFT circuit's Hadamard — a genuine one-qubit gate, never touching two wires — is, on the
  grounded control tower, precisely the Hadamard on the single wire `t.rev` (the reversal `Fin.rev`
  reconciling the big-endian register bridge with the little-endian wire-indexing of the Figure 5.1
  matrix gates). It is thus already in the form the deferred-measurement reduction wants: a
  one-qubit gate on one measured wire.

## Proof

Via the transported-gate re-expression combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`:
it suffices to check, for every bit-string `b`, that the single-wire Hadamard
sends `towerKet n b` to the transport of the register Hadamard's action on
`|finFunctionFinEquiv (b ∘ Fin.rev)⟩`. Unlike the swap (a basis permutation), the Hadamard produces
a **superposition**, so both sides are matched at the vector level as the two-term sum

  `∑_z hadamardC z (b t.rev) · towerKet n (Function.update b t.rev z)`.

* the left side: `qtowerSingleWire_evolvePure_towerKet` puts the wire into `hadamardGate |b t.rev⟩`,
  and the **tensor multilinearity of the tower product state in wire `t.rev`** (the shared
  `towerProd_vec_update_sum_smul`) distributes the qubit Hadamard's column
  `hadamardGate_evolvePure_qubitBasis_sum` over the two branch kets;
* the right side: `qftHadamardEvolution_evolvePure_quditBasis` gives the register two-term
  superposition, whose transport is pushed through the bridge isometry term by term
  (`map_sum` / `map_smul`) and read by the binary-expansion dictionary
  `quditPowTower_congr_quditBasis_apply` — the `Fin.rev`s aligning the wire orderings.

The Hadamard gate and its basis action are in `AxQM/Postulates/API/QftHadamardEvolution.lean`; the
tower gates used are in `QtowerSingleWireGate` and `EvolutionTowerBasisExt`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The transported Figure 5.1 Hadamard on wire `t` is the single-wire Hadamard on tower wire
`t.rev`.** Transporting the register Hadamard gate `qftHadamardEvolution (n+1) t` from the
`2ⁿ⁺¹`-level register onto the `(n+1)`-qubit control tower via the register bridge `quditPowTower n`
yields exactly the single-wire gate applying the one-qubit Hadamard to tower wire `t.rev`,

  `Evolution.congr (quditPowTower n) (qftHadamardEvolution (n+1) t)`
    `= Evolution.qtowerSingleWire n t.rev hadamardGate`.

This re-expresses the QFT circuit's Hadamard as an honest wire-addressed tower gate — a genuine
one-qubit gate on the single wire `t.rev`, touching no two wires at once — the second of the three
Figure 5.1 gate shapes the whole-circuit measured-QFT reduction (Problem 5.2) defers the terminal
measurement past. Proved through the combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`:
both the single-wire gate (via `qtowerSingleWire_evolvePure_towerKet` and the tensor multilinearity
of the tower product state) and the transported register Hadamard (via
`qftHadamardEvolution_evolvePure_quditBasis`, the bridge isometry, and the dictionary
`quditPowTower_congr_quditBasis_apply`) send `towerKet n b` to the two-term superposition
`∑_z hadamardC z (b t.rev) · towerKet n (Function.update b t.rev z)`, the two `Fin.rev`s collapsing
by `Fin.rev_rev`. -/
theorem quditPowTower_congr_qftHadamardEvolution (n : ℕ) (t : Fin (n + 1)) :
    Evolution.congr (quditPowTower n) (qftHadamardEvolution (n + 1) t)
      = Evolution.qtowerSingleWire n t.rev hadamardGate := by
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  apply PureState.ext
  rw [qtowerSingleWire_evolvePure_towerKet, PureState.congr_vec,
    qftHadamardEvolution_evolvePure_quditBasis,
    towerProd_vec_update_sum_smul n (fun j => qubitBasis (b j)) t.rev
      (fun z => Concrete.hadamardC z (b t.rev)) qubitBasis
      (hadamardGate.evolvePure (qubitBasis (b t.rev)))
      (hadamardGate_evolvePure_qubitBasis_sum (b t.rev)),
    map_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [map_smul, towerProd_update_qubitBasis b t z, ← PureState.congr_vec,
    quditPowTower_congr_quditBasis_apply, update_rev_eq b t z]

end AxQM
