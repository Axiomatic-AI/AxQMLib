/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QftSwapEvolution
import AxQM.Core.EvolutionTowerBasisExt
import AxQM.Core.QtowerWirePermutation

/-!
# The QFT swap layer re-expressed as a wire-permutation gate on the tower (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` as a product of *transported* Figure 5.1 gates
(`qftTowerEvolution_eq_map_congr_prod`). To defer the final per-wire measurement
past that product gate by gate, each transported gate must be re-expressed as an honest
**wire-addressed tower `Evolution`**. This file does so for the **swap (wire-reversal) layer**, the
first of the circuit's three gate shapes (the Hadamards and the controlled-`Rₖ` rotations are in
`AxQM/Core/QftTowerHadamard.lean` and `AxQM/Core/QftTowerControlled.lean`).

## What is formalised

* `quditPowTower_congr_qftSwapEvolution` — **the transported swap layer is the tower wire-reversal
  permutation.** Transporting the register swap `qftSwapEvolution (n+1)`
  (`AxQM/Postulates/API/QftSwapEvolution.lean`) onto the tower through the register bridge
  `quditPowTower n` equals the wire-permutation gate `Evolution.qtowerPermWires Fin.revPerm` that
  reverses the tower's `n+1` wires:

    `Evolution.congr (quditPowTower n) (qftSwapEvolution (n+1))`
      `= Evolution.qtowerPermWires Fin.revPerm`.

  So the QFT circuit's swap — a *relabelling* of the wires, not a two-wire entangling gate — is,
  on the grounded control tower, precisely the wire reversal `Fin.rev`, and it never touches two
  wires. It is thus already in the form the deferred-measurement reduction wants: a permutation of
  the measured wires.

## Proof

Via the transported-gate re-expression combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`:
it suffices to check, for every bit-string `b`, that
`qtowerPermWires Fin.revPerm` sends `towerKet n b` to the transport of the register swap's action on
`|finFunctionFinEquiv (b ∘ Fin.rev)⟩`. Both sides compute to `towerKet n (b ∘ Fin.rev)`:

* the left side by `qtowerPermWires_evolvePure_towerKet` (`qtowerPermWires σ` sends `towerKet n b`
  to `towerKet n (b ∘ σ⁻¹)`, and `Fin.revPerm⁻¹ = Fin.rev`);
* the right side because the register swap reverses the wire labels of the ket
  (`qftSwapEvolution_evolvePure_quditBasis`), turning `b ∘ Fin.rev` into `b ∘ Fin.rev ∘ Fin.rev = b`
  by `Fin.rev_rev`, and the register bridge then reads `|finFunctionFinEquiv b⟩` as
  `towerKet n (b ∘ Fin.rev)` (`quditPowTower_congr_quditBasis_apply`).

The `Fin.rev` reconciles the big-endian register bridge with the little-endian wire-indexing of the
Figure 5.1 matrix gates; that a *register* wire-reversal transports to a *tower* wire-reversal is
the content.

The swap gate `qftSwapEvolution` and its basis action are in
`AxQM/Postulates/API/QftSwapEvolution.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The transported QFT swap layer is the tower wire-reversal permutation.** Transporting the
Figure 5.1 swap (wire-reversal) gate `qftSwapEvolution (n+1)` from the `2ⁿ⁺¹`-level register onto
the `(n+1)`-qubit control tower via the register bridge `quditPowTower n` yields exactly the
wire-permutation gate reversing the tower's wires,

  `Evolution.congr (quditPowTower n) (qftSwapEvolution (n+1))`
    `= Evolution.qtowerPermWires Fin.revPerm`.

This re-expresses the QFT circuit's swap layer as an honest wire-addressed tower gate — a bare
*relabelling* of the `n+1` wires, touching no two wires at once — the first of the three Figure 5.1
gate shapes the whole-circuit measured-QFT reduction (Problem 5.2) defers the final measurement
past. Proved through the transported-gate re-expression combinator
`quditPowTower_congr_eq_of_evolvePure_towerKet`: both the tower permutation
(`qtowerPermWires_evolvePure_towerKet`, `Fin.revPerm⁻¹ = Fin.rev`) and the transported register swap
(`qftSwapEvolution_evolvePure_quditBasis` reversing the wire labels, then the register bridge
`quditPowTower_congr_quditBasis_apply`) send `towerKet n b` to `towerKet n (b ∘ Fin.rev)`, the two
`Fin.rev`s collapsing by `Fin.rev_rev`. -/
theorem quditPowTower_congr_qftSwapEvolution (n : ℕ) :
    Evolution.congr (quditPowTower n) (qftSwapEvolution (n + 1))
      = Evolution.qtowerPermWires Fin.revPerm := by
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  rw [qtowerPermWires_evolvePure_towerKet, qftSwapEvolution_evolvePure_quditBasis,
    quditPowTower_congr_quditBasis_apply]
  simp only [Fin.rev_rev, Fin.revPerm_symm, Fin.revPerm_apply]

end AxQM
