/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.BarencoTailReduction
import AxQM.Core.BorrowedMcNotEvolution

/-!
# A `barencoNCircuit` block/layer is a **linear** Toffoli circuit (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`): a nested stack of
reduction layers, each `barencoTail k W = Cᵏ(X) · C(W†) · Cᵏ(X) · C(W)` composed under a leading
multiplexer, whose distinctive content is bottoming its internal multiply-controlled
`NOT` blocks `Cᵏ(X)` to genuine `Toffoli`s.

The block and layer reductions are available **structurally**, but at the `Θ(k²)` per-block count of
the **halving** construction `Concrete.exists_mcNotCircuit` (`Concrete.mcNotGateBound`):

* `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` — one block on its control tower;
* `barencoTail_pauliXGate_onLeft_eq_toffoliBlocks` — one whole reduction layer.

Summed over `barencoNCircuit`'s `O(n)` internal blocks that `Θ(k²)` per-block bound is `Θ(n³)` —
overshooting the exercise's `O(n²)`. The **linear-cascade** construction fixes the per-block count:
`tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit` exhibits, for the contiguous front-block
placement `(Evolution.tensorPowMcCtrlX k).onBlock b`, a genuine `Evolution` circuit of `≤ 2`-control
gates with the **linear** count `≤ 4 (k - 2) + 1 = O(k)` — provided the register carries at least
`k - 2` idle ambient wires to borrow (`k - 2 ≤ b`, the honest cost of Barenco *Elementary gates*
Lemma 7.2's `k - 2` dirty ancillas).

This file is the linear counterpart of `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` and
`barencoTail_pauliXGate_onLeft_eq_toffoliBlocks`: it carries the linear circuit of
`tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit` up to the `barencoNCircuit` block on its own
control tower, and then to one whole reduction layer, by reusing the structural bridges — the
transport identity `barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft` and the definitional
unfolding of `barencoTail` / `barencoReductionCircuit_eq_mux_comp_tail`. Only the per-block circuit
`U` (hence the count) is swapped `Θ(k²) → O(k)`; the identities are route-independent, so the
proofs are verbatim those of the `Θ(k²)` versions with the linear circuit and its honest wire
budget.

## What is formalised

* `mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit` — the **per-block linear reduction on the
  tower**. For `2 ≤ k` and the wire budget `k - 2 ≤ d + 1`, the internal `Cᵏ(X)` block
  `mcCtrl k (pauliXGate.onLeft (qtower d qubit))` — as it sits in `barencoNCircuit` on the control
  tower `qtower k (qubit ⊗ qtower d qubit)`, with its `d + 1` idle module wires the borrowed dirty
  ancillas — **is**, as an `Evolution`, a genuine circuit `U` of `≤ 2`-control gates
  (`Toffoli`/`CNOT`/`NOT`) with the **linear** count `≤ 4 (k - 2) + 1`, transported onto that tower
  register through the flattening bridge:
  `mcCtrl k (pauliXGate.onLeft (qtower d qubit))
  = Evolution.congr (barencoBlockFlatten k d).symm U`. The linear counterpart of
  `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit`; obtained from the linear circuit and the transport
  identity by the gate-transport roundtrip `Evolution.congr_symm_congr`.

* `barencoTail_pauliXGate_onLeft_eq_linearToffoliBlocks` /
  `barencoReductionCircuit_pauliXGate_onLeft_eq_linearToffoliBlocks` — the **per-layer linear
  reduction**. For `1 ≤ k` and the budget `k - 1 ≤ d + 1`, one Barenco tail layer
  `barencoTail (k+1) W` (resp. the full Figure-4.8 layer `barencoReductionCircuit (k+1) W`) is the
  `Evolution` composition `B · C(W†) · B · C(W)` (resp. with the leading multiplexer `Cᵏ⁺¹(W)`
  kept), where the two `Cᵏ⁺¹(X)` blocks are **both** the single transported linear circuit
  `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U` of the per-block reduction — of length
  `≤ 4 (k + 1 - 2) + 1`. The linear counterpart of
  `barencoTail_pauliXGate_onLeft_eq_toffoliBlocks`; immediate from the per-block reduction
  and the definitional unfolding of `barencoTail` (`barencoReductionCircuit_eq_mux_comp_tail`).

## The wire budget — an honest scoping note

The budget `k - 2 ≤ d + 1` (per block) / `k - 1 ≤ d + 1` (per layer at level `k+1`) is Lemma 7.2's
requirement of `k - 2` borrowed **dirty** ancillas among the block's `d + 1` idle module wires. In
`barencoNCircuit V (n-1) 0` an internal `Cʲ(X)` block sits at recursion depth `d = (n-1) - j`, so it
has `d + 1 = n - j` idle module wires; the budget `j - 2 ≤ n - j` holds exactly for the smaller
blocks `j ≤ n/2 + 1`. The larger blocks (down to the top `C^{n-1}(X)` with a single idle wire) carry
too few module ancillas for Lemma 7.2 directly, and are the regime of Barenco's one-dirty-ancilla
Lemma 7.3 (splitting a `Cᵐ(X)` into two `≈ Cᵐ/²(X)` sub-blocks, each satisfying Lemma 7.2 on the
other half). That budget-free version is in `AxQM/Core/BarencoSplitLinearBlockReduction.lean`; this
file uses only the Lemma 7.2 double cascade `Concrete.borrowedMcNot`, and delivers the linear
per-block / per-layer reduction wherever the module-wire budget suffices. The parity obstruction
still forbids a permutation-only circuit on exactly `n + 1` wires, so the `√X`
single-qubit-controlled gates `C(W)`/`C(W†)` remain essential and stay intact here.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **N&C Exercise 4.29: a `barencoNCircuit` block is a bounded **linear** `O(k)` Toffoli
circuit on its tower register.** For `2 ≤ k` and the wire budget `k - 2 ≤ d + 1`, the internal
`Cᵏ(X)` block `mcCtrl k (pauliXGate.onLeft (qtower d qubit))` — as it sits in `barencoNCircuit` on
the control tower `qtower k (qubit ⊗ qtower d qubit)`, with its `d + 1` idle module wires available
as borrowed **dirty** ancillas — **is**, as an `Evolution`, a genuine circuit `U` of `≤ 2`-control
gates (`Toffoli`/`CNOT`/`NOT`, target never a control) with the **linear** count `≤ 4 (k - 2) + 1`,
transported onto that tower register through the flattening bridge:

`mcCtrl k (pauliXGate.onLeft (qtower d qubit)) = Evolution.congr (barencoBlockFlatten k d).symm U`,

where the circuit `gs` satisfies:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — the gate set is `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ 4 * (k - 2) + 1` — the **linear** `O(k)` gate count (versus the `Θ(k²)` of
  `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit`),
  the count the `O(n²)` assembly needs;
* `U` acts on every computational basis state `|⨂ᵢ c i⟩` as the classical circuit denotation
  `Concrete.mcNotDenote gs`.

The linear counterpart of `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit`: identical proof,
with the **linear** circuit `tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit` in place of
the `Θ(k²)` one `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`, its wire budget `k - 2 ≤ b = d + 1`
threaded through. Immediate from that circuit, the transport identity
`barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft`, and the
gate-transport roundtrip `Evolution.congr_symm_congr`. -/
theorem mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit (k d : ℕ) (hk : 2 ≤ k)
    (hb : k - 2 ≤ d + 1) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 4 * (k - 2) + 1 ∧
      (∀ c : Fin (k + 1 + (d + 1)) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      mcCtrl k (pauliXGate.onLeft (qtower d qubit))
        = Evolution.congr (barencoBlockFlatten k d).symm U := by
  obtain ⟨gs, U, hgs, hlen, hUc, hplaced⟩ :=
    tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit (k := k) (b := d + 1) hk hb
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  rw [← hplaced, ← barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft, Evolution.congr_symm_congr]

/-- **N&C Exercise 4.29: one Barenco reduction layer's `Cᵏ(X)` blocks are a bounded
**linear** Toffoli circuit.** For `1 ≤ k` and the wire budget `k - 1 ≤ d + 1`, and every
single-qubit-chain gate `W : Evolution (qtower d qubit)`, the Barenco tail layer
`barencoTail (k+1) W` — on the control tower `qtower (k+1) (qubit ⊗ qtower d qubit)` — is the
`Evolution` composition

`barencoTail (k+1) W = B · C(W†) · B · C(W)`,

where the two `Cᵏ⁺¹(X)` blocks `mcCtrl (k+1) (pauliXGate.onLeft (qtower d qubit))` are **both** the
single transported **linear** circuit `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U` of
the per-block reduction, and `C(W) = unCtrl (k+1) (controlledUnitary W)`,
`C(W†) = unCtrl (k+1) (controlledUnitary W.adjoint)` are the single-qubit-controlled gates. The
transported block `B` carries the linear certificates for `gs`:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — every gate is a `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ 4 * (k + 1 - 2) + 1` — the **linear** per-block gate count;
* `U` acts on every computational basis state `⨂ᵢ |c i⟩` as the classical circuit `mcNotDenote gs`.

So one layer's whole `≤ 2`-control content is `2 · gs.length ≤ 2 · (4 (k+1-2) + 1)` (the same `gs`
twice), plus two single-qubit-controlled gates. The linear counterpart of
`barencoTail_pauliXGate_onLeft_eq_toffoliBlocks`; immediate from the per-block linear reduction
`mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit` (at index `k+1`, whence the budget
`k - 1 ≤ d + 1`) and the definition of `barencoTail`. -/
theorem barencoTail_pauliXGate_onLeft_eq_linearToffoliBlocks (k d : ℕ) (hk : 1 ≤ k)
    (hb : k - 1 ≤ d + 1) (W : Evolution (qtower d qubit)) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 4 * (k + 1 - 2) + 1 ∧
      (∀ c : Fin (k + 1 + 1 + (d + 1)) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      barencoTail (k + 1) W
        = (Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
            ((unCtrl (k + 1) (controlledUnitary W.adjoint)).comp
              ((Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
                (unCtrl (k + 1) (controlledUnitary W)))) := by
  obtain ⟨gs, U, hgs, hlen, hUc, hblock⟩ :=
    mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit (k + 1) d (by omega) (by omega)
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  unfold barencoTail
  rw [hblock]

/-- **N&C Exercise 4.29: one full Figure-4.8 reduction layer, with its `Cᵏ(X)` blocks
bottomed to **linear** Toffolis.** For `1 ≤ k` and the wire budget `k - 1 ≤ d + 1`, and
single-qubit-chain gate `W : Evolution (qtower d qubit)`, the whole Figure-4.8 reduction circuit
`barencoReductionCircuit (k+1) W` (= `Cᵏ⁺¹(W) · barencoTail (k+1) W`,
`barencoReductionCircuit_eq_mux_comp_tail`) is the `Evolution` composition

`barencoReductionCircuit (k+1) W = Cᵏ⁺¹(W) · B · C(W†) · B · C(W)`,

with the leading multiplexer `Cᵏ⁺¹(W) = mcCtrl (k+1) (W.onRight qubit)` left as is (it is what the
`barencoNCircuit` recursion expands next), the two `Cᵏ⁺¹(X)` blocks replaced by the single
transported **linear** `≤ 2`-control circuit
`B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U`
(certificates as in `barencoTail_pauliXGate_onLeft_eq_linearToffoliBlocks`, length
`≤ 4 (k + 1 - 2) + 1`), and the two single-qubit-controlled gates `C(W)`, `C(W†)` kept. This is the
reduction layer exactly as it appears in `barencoNCircuit`, with its multiply-controlled `NOT`s
bottomed to a linear Toffoli count. The linear counterpart of
`barencoReductionCircuit_pauliXGate_onLeft_eq_toffoliBlocks`; immediate from
`barencoReductionCircuit_eq_mux_comp_tail` and the tail reduction. -/
theorem barencoReductionCircuit_pauliXGate_onLeft_eq_linearToffoliBlocks (k d : ℕ) (hk : 1 ≤ k)
    (hb : k - 1 ≤ d + 1) (W : Evolution (qtower d qubit)) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 4 * (k + 1 - 2) + 1 ∧
      (∀ c : Fin (k + 1 + 1 + (d + 1)) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      barencoReductionCircuit (k + 1) W
        = (mcCtrl (k + 1) (W.onRight qubit)).comp
            ((Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
              ((unCtrl (k + 1) (controlledUnitary W.adjoint)).comp
                ((Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
                  (unCtrl (k + 1) (controlledUnitary W))))) := by
  obtain ⟨gs, U, hgs, hlen, hUc, htail⟩ :=
    barencoTail_pauliXGate_onLeft_eq_linearToffoliBlocks k d hk hb W
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  rw [barencoReductionCircuit_eq_mux_comp_tail, htail]

end AxQM
