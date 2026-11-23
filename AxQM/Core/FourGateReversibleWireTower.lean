/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FourGateReversibleWire
import AxQM.Core.EvolutionTowerBasisExt
import AxQM.Core.McNotCircuitEvolution

/-!
# The reversible ≤ 2-control gates as `placedMcNot` on a tower wire set

*(N&C Exercise 4.43, reversible register lift.)*

The universality argument of Exercise 4.43 transfers the abstract density result
`Concrete.exists_phase_smul_mem_closure_reachableCircuits` onto the `H, S, CNOT, Toffoli`
gate set. One generating family of the reachable gate set is the `≤ 2`-control reversible gates
`Concrete.IsToffoliPermGate finFunctionFinEquiv G` — the matrices
`permGate finFunctionFinEquiv (mcNotPerm S t)` with `|S| ≤ 2` (`Toffoli`/`CNOT`/`NOT`). This file
re-expresses such a **matrix gate on the qudit register** as the multiply-controlled `NOT`
**gate on the corresponding tower wire set**, relating the matrix-level generators
to the `Evolution` gates, exactly as `AxQM/Core/FourGateReachableWireTower.lean` does for the
rotation generators (and `AxQM/Core/QftTowerHadamard.lean` for the Figure 5.1 Hadamard).

The target is `Evolution.placedMcNot` — the multiply-controlled `NOT` `Cᵏ(X)` placed on a
wire set of the symmetric register `qubit ^⊗ₛ (n+1)`, which for `|S| ≤ 2` is a genuine
`Toffoli`/`CNOT`/`NOT` built from the four gates. Because the rotation half lands on the control
tower `qtower n qubit`, so must the reversible half; `placedMcNot` is therefore transported back
onto the tower along the bridge `qtowerQubitTensorPow n : qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)`.

## What is formalised

* `mcNotTowerGate n S t ht` — the reversible **gate on the control tower**: the placed
  multiply-controlled `NOT` `Evolution.placedMcNot S t ht` (a `Toffoli`/`CNOT`/`NOT` for `|S| ≤ 2`),
  transported from the symmetric register `qubit ^⊗ₛ (n+1)` back onto the tower `qtower n qubit` via
  `(qtowerQubitTensorPow n).symm`. Its computational-basis action is
  `mcNotTowerGate_evolvePure_towerKet` — it flips wire `t` iff every control in `S` is set:
  `towerKet n b ↦ towerKet n (mcNot S t b)`. The reversible counterpart of the rotation half's
  `qtowerSingleWire n t.rev (rotZGate θ)`.
* `quditPowTower_congr_mcNotWireEvolution` — **the register lift for the reversible gates**:
  the wire-`(S, t)` reversible gate on the register (`mcNotWireEvolution (n+1) S t ht`) is, on the
  tower, the gate `mcNotTowerGate` on the reversed wire set
  `(S.map Fin.revPerm.toEmbedding, t.rev)` (the `Fin.rev` reconciling the big-endian register bridge
  with the little-endian wire indexing, as for the rotation register-lift's `t.rev`):

    `Evolution.congr (quditPowTower n) (mcNotWireEvolution (n+1) S t ht)`
      `= mcNotTowerGate n (S.map Fin.revPerm.toEmbedding) t.rev _`.

  Proved via the transported-gate re-expression combinator
  `quditPowTower_congr_eq_of_evolvePure_towerKet`: on every basis input both sides send
  `towerKet n b` to `towerKet n (mcNot (S.map rev) t.rev b)`; the register side computes it through
  `mcNotWireEvolution_evolvePure_quditBasis` and the bridge dictionary
  `quditPowTower_congr_quditBasis_apply`, the tower side through
  `mcNotTowerGate_evolvePure_towerKet`, and the two are reconciled by the `mcNot` relabelling
  naturality `Concrete.mcNot_map_equiv` at `σ = Fin.revPerm`. Since a reversible gate is a basis
  permutation there is **no** tensor-multilinearity step (the rotation half's inline `mult`) — the
  proof stays entirely in basis states.

The definition of `mcNotWireEvolution` (via the permutation matrix) is in
`AxQM/Postulates/API/FourGateReversibleWire.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The reversed wire set keeps the target off the controls.** If `t ∉ S` then, after reversing
every wire index by `Fin.rev`, the reversed target `t.rev` is still off the reversed control set
`S.map Fin.revPerm.toEmbedding`. The membership witness the reversed grounded gate
`mcNotTowerGate n (S.map Fin.revPerm.toEmbedding) t.rev` needs. -/
private theorem rev_not_mem_map_revPerm {n : ℕ} {S : Finset (Fin (n + 1))} {t : Fin (n + 1)}
    (ht : t ∉ S) : t.rev ∉ S.map Fin.revPerm.toEmbedding := by
  rw [Finset.mem_map_equiv]
  simpa using ht

/-- **The grounded reversible gate on the control tower.** The multiply-controlled `NOT` with
controls `S` and target `t ∉ S`, as a genuine grounded `Evolution (qtower n qubit)`: the placed
gate `Evolution.placedMcNot S t ht` on the symmetric register `qubit ^⊗ₛ (n+1)` (a
`Toffoli`/`CNOT`/`NOT` for `|S| ≤ 2`, built from the four gates) transported back onto the tower
along the bridge `(qtowerQubitTensorPow n).symm`. Its computational-basis action is
`mcNotTowerGate_evolvePure_towerKet` (`towerKet n b ↦ towerKet n (mcNot S t b)`); the reversible
counterpart of `qtowerSingleWire n t.rev (rotZGate θ)`. -/
def mcNotTowerGate (n : ℕ) (S : Finset (Fin (n + 1))) (t : Fin (n + 1)) (ht : t ∉ S) :
    Evolution (qtower n qubit) :=
  Evolution.congr (qtowerQubitTensorPow n).symm (Evolution.placedMcNot S t ht)

/-- **The grounded reversible tower gate is the classical `mcNot` on the tower basis.** On the
computational tower basis state `towerKet n b` the gate `mcNotTowerGate n S t ht` produces
`towerKet n (mcNot S t b)`: it flips wire `t` iff every control in `S` is set. Proved by carrying
the `placedMcNot` truth table `Evolution.placedMcNot_evolvePure_qubitBasis` across the tower ↔
tensor-power bridge: `towerKet n c` is the bridge preimage of the product basis state `⨂ᵢ |c i⟩`
(`qtowerQubitTensorPow_congr_towerKet` + the transport roundtrip `PureState.congr_symm_congr`), and
`Evolution.congr_evolvePure_congr` intertwines the transported gate's action with that of
`placedMcNot`. -/
theorem mcNotTowerGate_evolvePure_towerKet {n : ℕ} (S : Finset (Fin (n + 1))) (t : Fin (n + 1))
    (ht : t ∉ S) (b : Fin (n + 1) → Fin 2) :
    (mcNotTowerGate n S t ht).evolvePure (towerKet n b) = towerKet n (Concrete.mcNot S t b) := by
  have key : ∀ c : Fin (n + 1) → Fin 2, towerKet n c
      = PureState.congr (qtowerQubitTensorPow n).symm
          (PureState.piTensor fun i => qubitBasis (c i)) := fun c => by
    rw [← qtowerQubitTensorPow_congr_towerKet n c, PureState.congr_symm_congr]
  erw [mcNotTowerGate, key b, Evolution.congr_evolvePure_congr,
    Evolution.placedMcNot_evolvePure_qubitBasis, ← key (Concrete.mcNot S t b)]

/-- **The transported reachable wire multiply-controlled `NOT` is the grounded `placedMcNot` on the
reversed tower wire set.** Transporting the register gate `mcNotWireEvolution (n+1) S t ht` (the
`≤ 2`-control reversible gate on register wires `(S, t)`) onto the `(n+1)`-qubit control tower via
the register bridge `quditPowTower n` yields exactly the grounded reversible gate on the reversed
wire set:

  `Evolution.congr (quditPowTower n) (mcNotWireEvolution (n+1) S t ht)`
    `= mcNotTowerGate n (S.map Fin.revPerm.toEmbedding) t.rev _`.

The register gate — a genuine `Toffoli`/`CNOT`/`NOT` — is, on the grounded tower, precisely the
`placedMcNot` gate on the reversed wire set (the `Fin.rev` reconciling the big-endian register
bridge with the little-endian wire-indexing, as for the rotation register-lift's `t.rev`). Proved
via the transported-gate re-expression combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`:
on each basis input both sides give `towerKet n (mcNot (S.map rev) t.rev b)` — register side
`mcNotWireEvolution_evolvePure_quditBasis` + the bridge dictionary
`quditPowTower_congr_quditBasis_apply`, grounded side `mcNotTowerGate_evolvePure_towerKet` —
reconciled by the `mcNot` relabelling naturality `Concrete.mcNot_map_equiv` at `σ = Fin.revPerm`. -/
theorem quditPowTower_congr_mcNotWireEvolution (n : ℕ) (S : Finset (Fin (n + 1)))
    (t : Fin (n + 1)) (ht : t ∉ S) :
    Evolution.congr (quditPowTower n) (mcNotWireEvolution (n + 1) S t ht)
      = mcNotTowerGate n (S.map Fin.revPerm.toEmbedding) t.rev (rev_not_mem_map_revPerm ht) := by
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  rw [mcNotTowerGate_evolvePure_towerKet, mcNotWireEvolution_evolvePure_quditBasis,
    quditPowTower_congr_quditBasis_apply]
  congr 1
  funext i
  have h := Concrete.mcNot_map_equiv Fin.revPerm S t b i
  simpa only [Fin.revPerm_apply, Fin.revPerm_symm] using h

end AxQM

end
