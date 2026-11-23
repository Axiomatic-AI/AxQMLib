/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudget
import AxQM.Core.FourGateReversibleWireTower

/-!
# The elementary two-control-gate budget: a placed/tower `CNOT`/`Toffoli` is one gate

This file supplies the **leaf** and **fold** of the elementary-gate budget `CircuitBudget`
(`Core/CircuitBudget`) for `≤ 2`-control gates — the counterpart, for `Toffoli`/`CNOT`/`NOT`, of the
single-qubit-gate machinery `qtowerSingleWire_circuitBudget` (leaf) and `CircuitBudget.listProd`
(fold) that Problem 4.1's phase layer uses. It is the budget foundation of Nielsen & Chuang
**Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit gates" — whose
Figure-4.19 parity circuit (`Concrete/PauliStringParityCascade`) is a fan of `≤ n` `CNOT`s (the two-
control gates counted here) around a single collector `Z`-rotation.

## The `CircuitBudget` leaf for a multiply-controlled `NOT`

`CircuitBudget E t s` (N&C Ex 4.29) counts an `Evolution` `E` as at most `t` `≤ 2`-control gates
(`Toffoli`/`CNOT`/`NOT`) and `s` single-qubit gates. Its `block` constructor already witnesses that
a list `gs` of `≤ 2`-control classical gates, realised by an `Evolution` on the flat register
`qubit ^⊗ₛ m`, costs `gs.length` `≤ 2`-control gates. A *single* placed multiply-controlled `NOT`
`Evolution.placedMcNot S t ht` is exactly the `gs = [(S, t)]` case of `block`: its computational-
basis truth table is the classical `mcNot S t` (`Evolution.placedMcNot_evolvePure_qubitBasis`), i.e.
the denotation `mcNotDenote [(S, t)]`. So, whenever it addresses `≤ 2` control wires (`S.card ≤ 2` —
a `Toffoli`, `CNOT`, or `NOT`), it costs **one** `≤ 2`-control gate.

## What is formalised

* `Evolution.placedMcNot_circuitBudget` — the **leaf on the flat register**: for `S.card ≤ 2`,
  `CircuitBudget (Evolution.placedMcNot S t ht) 1 0` — a placed `Toffoli`/`CNOT`/`NOT` on
  `qubit ^⊗ₛ m` is one `≤ 2`-control gate and no single-qubit gates. Direct from the
  `CircuitBudget.block` leaf with the singleton gate list `[(S, t)]`, whose truth table is
  `placedMcNot_evolvePure_qubitBasis`.

* `mcNotTowerGate_circuitBudget` — the **leaf on the control tower**: for `S.card ≤ 2`,
  `CircuitBudget (mcNotTowerGate n S t ht) 1 0` — the same gate read on the qubit control tower
  `qtower n qubit`, where the elementary-gate budget is folded. Immediate from the flat-register
  leaf transported along the bridge `qtowerQubitTensorPow n` by `CircuitBudget.congr`, since
  `mcNotTowerGate n S t ht = Evolution.congr (qtowerQubitTensorPow n).symm
  (Evolution.placedMcNot S t ht)`. This is the tower analogue of `qtowerSingleWire_circuitBudget`
  (the single-qubit wire gate) for `≤ 2`-control gates.

* `CircuitBudget.listProd_twoControl` — the **two-control fold**: a `List.prod` of gates each
  costing `1 0` (one `≤ 2`-control gate) costs `l.length 0`. The `≤ 2`-control twin of
  `CircuitBudget.listProd` (which folds single-qubit `0 1` gates): `comp` sums the two-control
  counts down the list, the empty product discharged by an identity budget on the register
  (`hid`, e.g. `CircuitBudget.id_qtower` on a tower). This is the accountant that turns the `≤ n`
  per-`CNOT` leaves of the Figure-4.19 parity fan into its `O(n)` two-qubit-gate total (used in
  `AxQM/Core/CnotFanEvolutionBudget.lean`, Problem 4.3(3)).

The `block` leaf it specialises is in `Core/CircuitBudget`, and the single-qubit `listProd` fold it
mirrors is in `Core/PhaseLayerBudget`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A placed `Toffoli`/`CNOT`/`NOT` is one `≤ 2`-control gate.** For a control set `S` with at
most two wires (`S.card ≤ 2`) and target `t ∉ S`, the placed multiply-controlled `NOT`
`Evolution.placedMcNot S t ht` on the flat register `qubit ^⊗ₛ m` has budget

  `CircuitBudget (Evolution.placedMcNot S t ht) 1 0`

— at most one `≤ 2`-control gate (`Toffoli` for `|S| = 2`, `CNOT` for `|S| = 1`, `NOT` for
`|S| = 0`) and no single-qubit gates. This is the `gs = [(S, t)]` case of the `CircuitBudget.block`
leaf: the
singleton list of `≤ 2`-control gates has `hgs` from `S.card ≤ 2` and `t ∉ S`, and its denotation
`mcNotDenote [(S, t)] = mcNot S t` is exactly the placed gate's computational-basis truth table
`Evolution.placedMcNot_evolvePure_qubitBasis`. It is the two-control analogue of the single-qubit
wire leaf `qtowerSingleWire_circuitBudget`. -/
theorem Evolution.placedMcNot_circuitBudget {m : ℕ} (S : Finset (Fin m)) (t : Fin m) (ht : t ∉ S)
    (hcard : S.card ≤ 2) : CircuitBudget (Evolution.placedMcNot S t ht) 1 0 := by
  have h := CircuitBudget.block [(S, t)] (Evolution.placedMcNot S t ht)
    (by
      intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      exact ⟨hcard, ht⟩)
    (by
      intro c
      rw [Evolution.placedMcNot_evolvePure_qubitBasis]
      simp only [Concrete.mcNotDenote_cons, Concrete.mcNotDenote_nil]
      rfl)
  simpa using h

/-- **A tower `Toffoli`/`CNOT`/`NOT` is one `≤ 2`-control gate.** For a control set `S` with at most
two wires (`S.card ≤ 2`) and target `t ∉ S`, the multiply-controlled `NOT` `mcNotTowerGate n S t ht`
on the qubit control tower `qtower n qubit` has budget

  `CircuitBudget (mcNotTowerGate n S t ht) 1 0`

— at most one `≤ 2`-control gate and no single-qubit gates. Immediate from the flat-register leaf
`Evolution.placedMcNot_circuitBudget` transported off the tensor power onto the tower along the
bridge `qtowerQubitTensorPow n` by `CircuitBudget.congr`, since
`mcNotTowerGate n S t ht = Evolution.congr (qtowerQubitTensorPow n).symm (Evolution.placedMcNot S t
ht)`. This is the tower `≤ 2`-control leaf the Figure-4.19 `CNOT` parity fan of Problem 4.3(3) folds
wire-by-wire (`CircuitBudget.listProd_twoControl`) — the tower counterpart, for `≤ 2`-control gates,
of the single-qubit wire leaf `qtowerSingleWire_circuitBudget`. -/
theorem mcNotTowerGate_circuitBudget {n : ℕ} (S : Finset (Fin (n + 1))) (t : Fin (n + 1))
    (ht : t ∉ S) (hcard : S.card ≤ 2) : CircuitBudget (mcNotTowerGate n S t ht) 1 0 :=
  CircuitBudget.congr (qtowerQubitTensorPow n).symm
    (Evolution.placedMcNot_circuitBudget S t ht hcard)

/-- **A product of `≤ 2`-control gates costs one gate per factor.** If every gate in a list `l` has
budget `CircuitBudget · 1 0` (one `≤ 2`-control gate, no single-qubit gates), then their composition
`l.prod` has `CircuitBudget l.prod l.length 0` — the `≤ 2`-control counts add down the list. The
`≤ 2`-control twin of `CircuitBudget.listProd` (which folds single-qubit `0 1` gates): the reusable
accountant behind a `Toffoli`/`CNOT` fan or layer, e.g. the Figure-4.19 `CNOT` parity fan of
Problem 4.3(3). The empty product `1` needs an identity budget on the register, passed as `hid`
because a general system carries no elementary-gate witness for `1` (its constructors place gates on
qubit registers only); on a qubit tower `hid` is `CircuitBudget.id_qtower`. The `t₀ = 1, s₀ = 0`
specialisation of the general uniform fold `CircuitBudget.listProd_uniform`
(`l.length * 1 = l.length`, `l.length * 0 = 0`) — the count twin of the single-qubit
`CircuitBudget.listProd` (`t₀ = 0, s₀ = 1`). -/
theorem CircuitBudget.listProd_twoControl {S : QSystem} (hid : CircuitBudget (1 : Evolution S) 0 0)
    (l : List (Evolution S)) (h : ∀ E ∈ l, CircuitBudget E 1 0) :
    CircuitBudget l.prod l.length 0 := by
  simpa using CircuitBudget.listProd_uniform hid l h

end AxQM

end
