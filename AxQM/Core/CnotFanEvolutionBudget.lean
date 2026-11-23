/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CnotFanEvolution
import AxQM.Core.McNotCircuitBudget
import AxQM.Core.FourGateReversibleWireTower
import AxQM.Core.FourGateReachableWireTower
import AxQM.Core.PhaseLayerBudget

/-!
# The Figure-4.19 parity `CNOT` fan is `O(n)` two-qubit gates; the collector `Z`-rotation, one gate

This file discharges the gate-count half of the **third step** of Nielsen & Chuang
**Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit gates". After the
`O(n)` single-qubit basis change of Problem 4.3(3) step 2 (`Core/PauliDiagWireTower`), the diagonal
Hamiltonian `Z^{⊗S}` is implemented by the Figure-4.19 parity circuit: a `CNOT` fan `V` computing
the support parity onto a collector wire, a single-qubit `Z`-rotation on the collector, then the
uncomputation `V†` (`Concrete/PauliStringParityCascade`). This file counts the two pieces — the fan
and the collector rotation — with the elementary-gate budget `CircuitBudget` (`Core/CircuitBudget`).

The two pieces are the register `Evolution`s `cnotFanIntoEvolution` / `rotZWireEvolution`
(`Postulates/API`); their budgets are read off on the qubit control tower, where `CircuitBudget`
folds, using the register-tower bridges `quditPowTower_congr_mcNotWireEvolution` /
`quditPowTower_congr_rotZWireEvolution` already in the library.

## What is formalised

* `mcNotWireEvolution_circuitBudget` — the **register `≤ 2`-control leaf**: for `S.card ≤ 2`,
  `CircuitBudget (mcNotWireEvolution (n+1) S t ht) 1 0` — a register `Toffoli`/`CNOT`/`NOT` is one
  `≤ 2`-control gate. The register analogue of the tower leaf `mcNotTowerGate_circuitBudget`
  (`Core/McNotCircuitBudget`): transport onto the tower along the reversible-wire register bridge
  turns it into `mcNotTowerGate n (S.map Fin.revPerm) t.rev`, whose budget is
  `mcNotTowerGate_circuitBudget` (the card unchanged by the wire relabelling, `Finset.card_map`).

* `rotZWireEvolution_circuitBudget` — the **collector `Z`-rotation budget**:
  `CircuitBudget (rotZWireEvolution (n+1) t θ) 0 1` — the single-qubit `R_z(θ)` on any register wire
  is one single-qubit gate, whatever the angle `θ`. The `R_z`-instance of the per-wire single-qubit
  budget: transport along `quditPowTower_congr_rotZWireEvolution` makes it the tower single-wire
  gate `qtowerSingleWire n t.rev (rotZGate θ)`, budgeted `0 1` by `qtowerSingleWire_circuitBudget`.
  This is the one single-qubit gate of Figure 4.19's collector rotation (its angle `θ = 2 h_g Δ` is
  irrelevant to the count).

* `cnotFanIntoEvolution_circuitBudget` — the **fan budget**: for a collector `c ∉ ts`,
  `CircuitBudget (cnotFanIntoEvolution (n+1) c ts) ts.length 0` — the reverse `CNOT` fan into `c`
  costs its `ts.length` `CNOT`s in `≤ 2`-control gates and no single-qubit gates. Proof (the
  `≤ 2`-control analogue of `pauliDiagLayer_circuitBudget`): transport the fan onto the tower with
  `Evolution.congr_prod` (a product of transported factors), then fold the per-`CNOT` budgets with
  `CircuitBudget.listProd_twoControl` (base `CircuitBudget.id_qtower`). Each factor
  `cnotWireEvolution (n+1) t c` for `t ∈ ts` is a genuine `CNOT` (`c ≠ t`, from `c ∉ ts`), budgeted
  `1 0` by `mcNotWireEvolution_circuitBudget` (its single control `{t}` has card `1 ≤ 2`); the
  `List.length` of the transported list is `ts.length` (`List.length_map`). The `ts.length` here is
  the fan's `|S| − 1` `CNOT`s; with the uncomputation `V†` it is the `2(|S| − 1) = O(n)` two-qubit
  gates of Figure 4.19.

The tower `≤ 2`-control leaf it transports is in `AxQM/Core/McNotCircuitBudget.lean`, and
`AxQM/Core/PhaseLayerBudget.lean` has the `listProd`/`id_qtower` pattern it mirrors. The fan
`Evolution` itself is defined in `AxQM/Postulates/API/CnotFanEvolution.lean`.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **A register `Toffoli`/`CNOT`/`NOT` is one `≤ 2`-control gate.** For a control set `S` with at
most two wires (`S.card ≤ 2`) and target `t ∉ S`, the register multiply-controlled `NOT`
`mcNotWireEvolution (n+1) S t ht` on `qudit (2ⁿ⁺¹)` has budget
`CircuitBudget (mcNotWireEvolution (n+1) S t ht) 1 0`. The register analogue of the grounded tower
leaf `mcNotTowerGate_circuitBudget` (`Core/McNotCircuitBudget`): transport the gate onto the
`(n+1)`-qubit control tower along `quditPowTower_congr_mcNotWireEvolution`, where it is
`mcNotTowerGate n (S.map Fin.revPerm) t.rev` (the wire relabelling leaving the control count fixed,
`Finset.card_map`), read its budget with `mcNotTowerGate_circuitBudget`, and carry it back off the
tower with `CircuitBudget.congr`. This is the per-`CNOT` leaf the parity fan
`cnotFanIntoEvolution_circuitBudget` folds. -/
theorem mcNotWireEvolution_circuitBudget {n : ℕ} (S : Finset (Fin (n + 1))) (t : Fin (n + 1))
    (ht : t ∉ S) (hcard : S.card ≤ 2) : CircuitBudget (mcNotWireEvolution (n + 1) S t ht) 1 0 := by
  rw [← Evolution.congr_symm_congr (quditPowTower n) (mcNotWireEvolution (n + 1) S t ht),
    quditPowTower_congr_mcNotWireEvolution]
  exact CircuitBudget.congr (quditPowTower n).symm
    (mcNotTowerGate_circuitBudget _ t.rev _ (by rw [Finset.card_map]; exact hcard))

/-- **The collector `Z`-rotation on a register wire is one single-qubit gate.** For every wire
`t : Fin (n+1)` and angle `θ`, the `R_z(θ)` rotation on wire `t` of the `2ⁿ⁺¹`-level register has
budget `CircuitBudget (rotZWireEvolution (n+1) t θ) 0 1` — one single-qubit gate and no
`≤ 2`-control gates. The `R_z`-instance of the per-wire single-qubit tower budget: transport along
`quditPowTower_congr_rotZWireEvolution` makes the transported gate the tower single-wire gate
`qtowerSingleWire n t.rev (rotZGate θ)`, whose budget is `qtowerSingleWire_circuitBudget`, then
`CircuitBudget.congr` carries the budget back off the tower. This is Figure 4.19's collector
`Z`-rotation `exp(-i h_g Δ Z_c)` counted as its one single-qubit gate (the angle irrelevant to the
count). The reachable-rotation analogue of `pauliDiagWireEvolution_circuitBudget`. -/
theorem rotZWireEvolution_circuitBudget {n : ℕ} (t : Fin (n + 1)) (θ : ℝ) :
    CircuitBudget (rotZWireEvolution (n + 1) t θ) 0 1 := by
  rw [← Evolution.congr_symm_congr (quditPowTower n) (rotZWireEvolution (n + 1) t θ),
    quditPowTower_congr_rotZWireEvolution]
  exact CircuitBudget.congr (quditPowTower n).symm
    (qtowerSingleWire_circuitBudget n t.rev (rotZGate θ))

/-- **A single register `CNOT` (distinct control `a`, target `b`) is one `≤ 2`-control gate.**
For `b ≠ a`, `cnotWireEvolution (n+1) a b` reduces to `mcNotWireEvolution (n+1) {a} b` (the
`dif_neg` branch), a single control (`card {a} = 1 ≤ 2`), budgeted `1 0` by
`mcNotWireEvolution_circuitBudget`. The per-`CNOT` leaf folded by
`cnotFanIntoEvolution_circuitBudget`; the `≤ 2`-control twin of `rotZWireEvolution_circuitBudget`,
restoring the file's symmetry where every atomic register gate it touches carries its own named
`_circuitBudget`. -/
theorem cnotWireEvolution_circuitBudget {n : ℕ} (a b : Fin (n + 1)) (h : b ≠ a) :
    CircuitBudget (cnotWireEvolution (n + 1) a b) 1 0 := by
  rw [cnotWireEvolution, dite_eq_right h]
  exact mcNotWireEvolution_circuitBudget {a} b _ (by rw [Finset.card_singleton]; omega)

/-- **Problem 4.3(3)'s Figure-4.19 parity `CNOT` fan is `ts.length` two-qubit gates.** For a
collector `c ∉ ts` (a duplicate-free control list `ts`), the reverse `CNOT` fan into `c` has budget

  `CircuitBudget (cnotFanIntoEvolution (n+1) c ts) ts.length 0`

— at most `ts.length` `≤ 2`-control gates (its `CNOT`s) and no single-qubit gates. Together with the
uncomputation `V†` this is the `2(|S| − 1) = O(n)` two-qubit gates of Figure 4.19 (here
`ts` is the support minus the collector, so `ts.length = |S| − 1`).

Proof — the `≤ 2`-control analogue of `pauliDiagLayer_circuitBudget`: transport the fan onto the
`(n+1)`-qubit control tower (`Evolution.congr_symm_congr` + `Evolution.congr_prod` + `List.map_map`
push the transport through the `List.prod`), where it is the ordered product of the transported
per-`CNOT` gates; fold their budgets with `CircuitBudget.listProd_twoControl`
(`Core/McNotCircuitBudget`, base `CircuitBudget.id_qtower`); then `CircuitBudget.congr` carries the
budget back off the tower. Each factor `cnotWireEvolution (n+1) t c` for `t ∈ ts` is a genuine
`CNOT` — `c ≠ t` from `c ∉ ts` — budgeted `1 0` by `cnotWireEvolution_circuitBudget`, and the
transported list has length `ts.length` (`List.length_map`). -/
theorem cnotFanIntoEvolution_circuitBudget {n : ℕ} (c : Fin (n + 1)) (ts : List (Fin (n + 1)))
    (hc : c ∉ ts) : CircuitBudget (cnotFanIntoEvolution (n + 1) c ts) ts.length 0 := by
  rw [← Evolution.congr_symm_congr (quditPowTower n) (cnotFanIntoEvolution (n + 1) c ts)]
  refine CircuitBudget.congr (quditPowTower n).symm ?_
  rw [cnotFanIntoEvolution, Evolution.congr_prod, List.map_map]
  have h := CircuitBudget.listProd_twoControl (CircuitBudget.id_qtower n)
    (ts.map fun t => Evolution.congr (quditPowTower n) (cnotWireEvolution (n + 1) t c))
    (by
      intro E hE
      simp only [List.mem_map] at hE
      obtain ⟨t, htmem, rfl⟩ := hE
      exact CircuitBudget.congr (quditPowTower n)
        (cnotWireEvolution_circuitBudget t c (by rintro rfl; exact hc htmem)))
  rwa [List.length_map] at h

end

end AxQM
