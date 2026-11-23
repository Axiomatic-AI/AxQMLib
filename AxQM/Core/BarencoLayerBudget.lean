/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudget
import AxQM.Core.BarencoBlockReduction

/-!
# Every `barencoNCircuit` layer has a `CircuitBudget` (N&C Ex 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`): a `comp`-chain whose
pieces are one Barenco tail layer `barencoTail j W = Cʲ(X) · C(W†) · Cʲ(X) · C(W)` per block index
`j = k, k-1, …, 1`, plus the innermost base `barencoReductionCircuit 0 W`
(`barencoNCircuit_succ` / `barencoNCircuit_zero`, Exercise 4.30). The file
`AxQM/Core/CircuitBudget.lean` gives the compositional gate-count abstraction `CircuitBudget` and
the **per-layer budget for the large layers**, `barencoTail_unCtrl_circuitBudget`: for block index
`≥ 3`, one tail is at most `16 j = O(j)` `≤ 2`-control gates and two single-qubit-controlled gates.

## What is formalised

This file completes the per-piece budgets so that **every** piece of the recursion — every tail
layer *and* the base — is accounted for, as the whole-circuit fold requires.

* `barencoTail_small_circuitBudget` — the **small-block** tail budget. For block index `m ≤ 2` the
  block `Cᵐ(X)` is already a single elementary gate (`NOT`/`CNOT`/`Toffoli`), so the block
  reduction `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` (which needs only a spare wire, at
  **any** index) bottoms it to a gate list of length `≤ mcNotGateBound m = 1`. Hence
  `CircuitBudget (barencoTail m (unCtrl d g)) 2 2` — at most two `≤ 2`-control gates (the two
  blocks) and exactly two single-qubit-controlled gates `C(W)`, `C(W†)`.

* `barencoTail_circuitBudget` — the **uniform** per-layer tail budget, for **every** block index
  `m ≥ 1`: `CircuitBudget (barencoTail m (unCtrl d g)) (16 m) 2`. It is `barencoTail_small_…`
  weakened for `m ≤ 2` and `barencoTail_unCtrl_circuitBudget` for `m ≥ 3`; the common
  bound `16 m` (linear) is what makes the summed count over the `O(n)` layers `Σⱼ 16 j = O(n²)`.

* `barencoReductionCircuit_zero_circuitBudget` — the **base** budget:
  `CircuitBudget (barencoReductionCircuit 0 (unCtrl d g)) 2 3`. The base splits as its leading
  multiplexer `C⁰(V) = V` (`barencoReductionCircuit_eq_mux_comp_tail`) composed with the tail
  `barencoTail 0 W`; the multiplexer is the bare uncontrolled single-qubit gate the `single`
  leaf accounts for, and the tail is `barencoTail_small_…` at `m = 0`.

## Whole-circuit count

`barencoNCircuit V k 0` is a `comp`-chain of `k` tail layers plus the base
(`barencoNCircuit_succ`), so folding `barencoTail_circuitBudget` (per tail) and
`barencoReductionCircuit_zero_circuitBudget` (the base) over the recursion — via
`CircuitBudget.comp` and `CircuitBudget.cast_congr` — and summing the counts `Σⱼ 16 j = 8 k (k+1)`
gives the whole circuit a `CircuitBudget` with `O(n²)` `≤ 2`-control gates and `O(n)` single-qubit
gates, on exactly the `n + 1`-wire register. Every internal `Cᵏ(X)` block is bottomed linearly by
the split reduction `mcCtrl_pauliXGate_onLeft_eq_splitLinearToffoliCircuit` (in
`AxQM/Core/BarencoSplitLinearBlockReduction.lean`) that the large-layer budget consumes; the small
blocks and base cost `O(1)`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **N&C Exercise 4.29: the small-block tail budget.** For block index `m ≤ 2` and any
single-qubit root `g : Evolution qubit`, one Barenco tail layer `barencoTail m (unCtrl d g)` — on
the control tower `qtower m (qubit ⊗ qtower d qubit)` — has

`CircuitBudget (barencoTail m (unCtrl d g)) 2 2`,

i.e. at most two `≤ 2`-control gates (the two `Cᵐ(X)` blocks, each already a single
`NOT`/`CNOT`/`Toffoli`) and exactly two single-qubit-controlled gates `C(unCtrl d g)`,
`C((unCtrl d g)†)`. For `m ≤ 2` the block `Cᵐ(X)` is elementary, so the block reduction
`mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` bottoms it to a gate list of length
`≤ mcNotGateBound m = 1` (`Concrete.mcNotGateBound_of_le`): the two transported blocks
`B = Evolution.congr (barencoBlockFlatten m d).symm U` each get `block` + `congr`, the two
single-qubit-controlled gates get `ctrlGateAdj` / `ctrlGate`, and `comp` sums the counts
(`2 · 1 = 2` block gates, `2` controlled gates). This is the `m ≤ 2` counterpart of
`barencoTail_unCtrl_circuitBudget` (`m ≥ 3`, linear), completing the per-layer budget at every
index. -/
theorem barencoTail_small_circuitBudget (m d : ℕ) (hm : m ≤ 2) (g : Evolution qubit) :
    CircuitBudget (barencoTail m (unCtrl d g)) 2 2 := by
  obtain ⟨gs, U, hgs, hlen, hUc, hblock⟩ := mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit m d
  rw [Concrete.mcNotGateBound_of_le hm] at hlen
  unfold barencoTail
  rw [hblock]
  have hB : CircuitBudget (Evolution.congr (barencoBlockFlatten m d).symm U) gs.length 0 :=
    CircuitBudget.congr _ (CircuitBudget.block gs U hgs hUc)
  refine (hB.comp ((CircuitBudget.ctrlGateAdj (n := m) (d := d) g).comp
    (hB.comp (CircuitBudget.ctrlGate (n := m) (d := d) g)))).mono ?_ ?_
  · omega
  · omega

/-- **N&C Exercise 4.29: the uniform per-layer tail budget.** For **every** block index
`m ≥ 1` and any single-qubit root `g : Evolution qubit`, one Barenco tail layer
`barencoTail m (unCtrl d g)` has

`CircuitBudget (barencoTail m (unCtrl d g)) (16 * m) 2`,

i.e. at most `16 m = O(m)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and exactly two
single-qubit-controlled gates. The common **linear** bound `16 m` is what lets the per-layer counts
be summed to the exercise's `O(n²)` over the `O(n)` layers of `barencoNCircuit` (`Σⱼ 16 j = O(n²)`).
It weakens the small-block budget `barencoTail_small_circuitBudget` (`2 ≤ 16 m`) for `m ≤ 2`, and is
`barencoTail_unCtrl_circuitBudget` verbatim for `m ≥ 3`. -/
theorem barencoTail_circuitBudget (m d : ℕ) (hm : 1 ≤ m) (g : Evolution qubit) :
    CircuitBudget (barencoTail m (unCtrl d g)) (16 * m) 2 := by
  by_cases h : m ≤ 2
  · exact (barencoTail_small_circuitBudget m d h g).mono (by omega) le_rfl
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    exact barencoTail_unCtrl_circuitBudget (k + 2) d (by omega) g

/-- **N&C Exercise 4.29: the base budget.** The innermost Barenco reduction layer
`barencoReductionCircuit 0 (unCtrl d g)` — the `k = 0` base of the `barencoNCircuit` recursion — has

`CircuitBudget (barencoReductionCircuit 0 (unCtrl d g)) 2 3`,

i.e. at most two `≤ 2`-control gates and three single-qubit gates. The base splits as its leading
multiplexer `C⁰(unCtrl d g) = (unCtrl d g).onRight qubit` composed with the tail `barencoTail 0`
(`barencoReductionCircuit_eq_mux_comp_tail`): the multiplexer is a **bare uncontrolled single-qubit
gate** — the one gate of the recursion accounted for by the `single` leaf, not by any `≤ 2`-control
or *controlled* single-qubit leaf — and the tail contributes `barencoTail_small_circuitBudget` at
`m = 0` (two `NOT` blocks + `C(W)`, `C(W†)`), giving `(0 + 2, 1 + 2) = (2, 3)`. -/
theorem barencoReductionCircuit_zero_circuitBudget (d : ℕ) (g : Evolution qubit) :
    CircuitBudget (barencoReductionCircuit 0 (unCtrl d g)) 2 3 := by
  rw [barencoReductionCircuit_eq_mux_comp_tail, mcCtrl_zero]
  exact (CircuitBudget.single (d := d) g).comp (barencoTail_small_circuitBudget 0 d (by norm_num) g)

end AxQM
