/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.BarencoTailReduction
import AxQM.Core.SplitMcNotOnBlock

/-!
# A `barencoNCircuit` block/layer is a budget-free linear Toffoli circuit (N&C Ex 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`): a nested stack of
reduction layers, each `barencoTail k W = Cᵏ(X) · C(W†) · Cᵏ(X) · C(W)` composed under a leading
multiplexer, whose distinctive content is bottoming its internal multiply-controlled
`NOT` blocks `Cᵏ(X)` to genuine `Toffoli`s at a **linear** `O(k)` per-block count (so the summed
count over `barencoNCircuit`'s `O(n)` blocks is the exercise's `O(n²)`, not `O(n³)`).

The file `AxQM/Core/BarencoLinearBlockReduction.lean` carries a **linear** `O(k)` per-block /
per-layer circuit up to the `barencoNCircuit` block on its own control tower, but through the
Lemma-7.2 dirty cascade (`tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit`), which needs
`k - 2` idle ambient wires to borrow — the honest wire budget `k - 2 ≤ d + 1` (per block) /
`k - 1 ≤ d + 1` (per layer at level `k+1`). That budget is met only by the **smaller** blocks of
`barencoNCircuit` (`j ≤ n/2 + 1`); the **larger** blocks — down to the top `C^{n-1}(X)` with a
single idle module wire — carry too few module ancillas for Lemma 7.2 directly, so that
reduction does **not** cover them.

The file `AxQM/Core/SplitMcNotOnBlock.lean` closes that gap at the block level: through Barenco's
**Lemma 7.3** control split (`tensorPowMcCtrlX_onBlock_eq_splitLinearToffoliCircuit`) the contiguous
front-block `Cᵏ(X)` `(Evolution.tensorPowMcCtrlX k).onBlock b` is a linear `≤ 8 k = O(k)` Toffoli
circuit needing just **one** borrowed dirty wire (`1 ≤ b`, `k ≥ 3`) — the two control halves
supplying each other's Lemma-7.2 ancillas.

## What is formalised

This file is the split-route, budget-free counterpart of
`AxQM/Core/BarencoLinearBlockReduction.lean`. It carries the
one-borrowed-wire linear circuit of `tensorPowMcCtrlX_onBlock_eq_splitLinearToffoliCircuit` up to
the `barencoNCircuit` block on its own control tower, and then to one whole reduction layer, by
reusing the structural bridges — the transport identity
`barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft` and the definitional unfolding of
`barencoTail` / `barencoReductionCircuit_eq_mux_comp_tail`. Only the per-block circuit `U` (hence
the count `≤ 8 k`) and its **wire budget** change: the condition `1 ≤ b = d + 1` holds for
**every** `d` (`d + 1 ≥ 1` always), so the reductions here carry **no wire-budget hypothesis at
all** — they apply uniformly to every internal block of `barencoNCircuit`, including the largest.
The identities themselves are route-independent, so the proofs are verbatim those of
`BarencoLinearBlockReduction` with the split circuit in place of the `k - 2`-borrowed one.

* `mcCtrl_pauliXGate_onLeft_eq_splitLinearToffoliCircuit` — the **per-block** reduction on the
  tower. For `3 ≤ k` and **no** wire budget, the internal `Cᵏ(X)` block
  `mcCtrl k (pauliXGate.onLeft (qtower d qubit))` — as it sits in `barencoNCircuit` on the control
  tower `qtower k (qubit ⊗ qtower d qubit)`, with its `d + 1` idle module wires supplying the single
  borrowed dirty ancilla — **is**, as an `Evolution`, a genuine circuit `U` of `≤ 2`-control gates
  (`Toffoli`/`CNOT`/`NOT`) with the **linear** count `≤ 8 k`, transported onto that tower register:
  `mcCtrl k (pauliXGate.onLeft (qtower d qubit)) = Evolution.congr (barencoBlockFlatten k d).symm U`
  (no borrowed-wire hypothesis).

* `barencoTail_pauliXGate_onLeft_eq_splitLinearToffoliBlocks` /
  `barencoReductionCircuit_pauliXGate_onLeft_eq_splitLinearToffoliBlocks` — the **per-layer**
  reduction. For `2 ≤ k` (so the block index `k + 1 ≥ 3`) and **no** wire budget, one Barenco tail
  layer `barencoTail (k+1) W` (resp. the full Figure-4.8 layer `barencoReductionCircuit (k+1) W`)
  is the `Evolution` composition `B · C(W†) · B · C(W)` (resp. with the leading multiplexer
  `Cᵏ⁺¹(W)` kept), where the two `Cᵏ⁺¹(X)` blocks are **both** the single transported linear circuit
  `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U` of the per-block reduction — of length
  `≤ 8 (k + 1)`.

## The count for the whole circuit

This removes the `k - 2 ≤ d + 1` wire budget of `BarencoLinearBlockReduction` entirely: a single
idle module wire — which **every** internal `barencoNCircuit` block has — now suffices to bottom
**any** block linearly. Applied uniformly across the `O(n)` internal `Cᵏ(X)` blocks of
`barencoNCircuit`, the linear `O(k)` per-block count gives the exercise's `O(n²)` total on exactly
the `n + 1`-wire register, with no cubic count and no gap for the large blocks. The parity
obstruction still forbids a permutation-only circuit on exactly `n + 1` wires, so the `√X`
single-qubit-controlled gates `C(W)`/`C(W†)` remain essential; the one borrowed ancilla here is an
idle tower module wire, staying within the `n + 1`-wire register (Barenco *Elementary gates for
quantum computation*, Lemma 7.3).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **N&C Exercise 4.29: a `barencoNCircuit` block is a budget-free bounded **linear**
`O(k)` Toffoli circuit on its tower register.** For `3 ≤ k` and **no** wire budget, the internal
`Cᵏ(X)` block `mcCtrl k (pauliXGate.onLeft (qtower d qubit))` — as it sits in `barencoNCircuit` on
the control tower `qtower k (qubit ⊗ qtower d qubit)`, with its `d + 1` idle module wires supplying
the single borrowed **dirty** ancilla — **is**, as an `Evolution`, a genuine circuit `U` of
`≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`, target never a control) with the **linear** count
`≤ 8 k`, transported onto that tower register through the flattening bridge:

`mcCtrl k (pauliXGate.onLeft (qtower d qubit)) = Evolution.congr (barencoBlockFlatten k d).symm U`,

where the circuit `gs` satisfies:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — the gate set is `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ 8 * k` — the **linear** `O(k)` gate count, the count the `O(n²)` assembly needs;
* `U` acts on every computational basis state `|⨂ᵢ c i⟩` as the classical circuit denotation
  `Concrete.mcNotDenote gs`.

The split-route counterpart of `mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit`:
identical proof, with the one-borrowed-wire circuit
`tensorPowMcCtrlX_onBlock_eq_splitLinearToffoliCircuit` in place of the `k - 2`-borrowed
`tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit`,
whose wire budget `1 ≤ b = d + 1` holds for every `d` — so, unlike that one, this reduction carries
**no** wire budget and applies to every internal block. Immediate from that circuit, the transport
identity `barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft`, and the gate-transport roundtrip
`Evolution.congr_symm_congr`. -/
theorem mcCtrl_pauliXGate_onLeft_eq_splitLinearToffoliCircuit (k d : ℕ) (hk : 3 ≤ k) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 8 * k ∧
      (∀ c : Fin (k + 1 + (d + 1)) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      mcCtrl k (pauliXGate.onLeft (qtower d qubit))
        = Evolution.congr (barencoBlockFlatten k d).symm U := by
  obtain ⟨gs, U, hgs, hlen, hUc, hplaced⟩ :=
    tensorPowMcCtrlX_onBlock_eq_splitLinearToffoliCircuit (k := k) (b := d + 1) hk (by omega)
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  rw [← hplaced, ← barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft, Evolution.congr_symm_congr]

/-- **N&C Exercise 4.29: one Barenco reduction layer's `Cᵏ(X)` blocks are a budget-free
bounded **linear** Toffoli circuit.** For `2 ≤ k` (so the block index `k + 1 ≥ 3`), **no** wire
budget, and every single-qubit-chain gate `W : Evolution (qtower d qubit)`, the Barenco tail layer
`barencoTail (k+1) W` — on the control tower `qtower (k+1) (qubit ⊗ qtower d qubit)` — is the
`Evolution` composition

`barencoTail (k+1) W = B · C(W†) · B · C(W)`,

where the two `Cᵏ⁺¹(X)` blocks `mcCtrl (k+1) (pauliXGate.onLeft (qtower d qubit))` are **both** the
single transported **linear** circuit `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U` of
the per-block reduction, and `C(W) = unCtrl (k+1) (controlledUnitary W)`,
`C(W†) = unCtrl (k+1) (controlledUnitary W.adjoint)` are the single-qubit-controlled gates. The
transported block `B` carries the linear certificates for `gs`:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — every gate is a `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ 8 * (k + 1)` — the **linear** per-block gate count;
* `U` acts on every computational basis state `⨂ᵢ |c i⟩` as the classical circuit `mcNotDenote gs`.

So one layer's whole `≤ 2`-control content is `2 · gs.length ≤ 2 · 8 (k+1)` (the same `gs` twice),
plus two single-qubit-controlled gates. The split-route counterpart of
`barencoTail_pauliXGate_onLeft_eq_linearToffoliBlocks`, but **budget-free**; immediate from the
per-block split reduction `mcCtrl_pauliXGate_onLeft_eq_splitLinearToffoliCircuit` (at index `k+1`,
whence `3 ≤ k + 1` from `2 ≤ k`) and the definition of `barencoTail`. -/
theorem barencoTail_pauliXGate_onLeft_eq_splitLinearToffoliBlocks (k d : ℕ) (hk : 2 ≤ k)
    (W : Evolution (qtower d qubit)) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 8 * (k + 1) ∧
      (∀ c : Fin (k + 1 + 1 + (d + 1)) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      barencoTail (k + 1) W
        = (Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
            ((unCtrl (k + 1) (controlledUnitary W.adjoint)).comp
              ((Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
                (unCtrl (k + 1) (controlledUnitary W)))) := by
  obtain ⟨gs, U, hgs, hlen, hUc, hblock⟩ :=
    mcCtrl_pauliXGate_onLeft_eq_splitLinearToffoliCircuit (k + 1) d (by omega)
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  unfold barencoTail
  rw [hblock]

/-- **N&C Exercise 4.29: one full Figure-4.8 reduction layer, with its `Cᵏ(X)` blocks
bottomed to budget-free **linear** Toffolis.** For `2 ≤ k` (so the block index `k + 1 ≥ 3`), **no**
wire budget, and single-qubit-chain gate `W : Evolution (qtower d qubit)`, the whole Figure-4.8
reduction circuit `barencoReductionCircuit (k+1) W` (= `Cᵏ⁺¹(W) · barencoTail (k+1) W`,
`barencoReductionCircuit_eq_mux_comp_tail`) is the `Evolution` composition

`barencoReductionCircuit (k+1) W = Cᵏ⁺¹(W) · B · C(W†) · B · C(W)`,

with the leading multiplexer `Cᵏ⁺¹(W) = mcCtrl (k+1) (W.onRight qubit)` left as is (it is what the
`barencoNCircuit` recursion expands next), the two `Cᵏ⁺¹(X)` blocks replaced by the single
transported **linear** `≤ 2`-control circuit
`B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U`
(certificates as in `barencoTail_pauliXGate_onLeft_eq_splitLinearToffoliBlocks`, length
`≤ 8 (k + 1)`), and the two single-qubit-controlled gates `C(W)`, `C(W†)` kept. This is the
reduction layer exactly as it appears in `barencoNCircuit`, with its multiply-controlled `NOT`s
bottomed to a budget-free linear Toffoli count. The split-route counterpart of
`barencoReductionCircuit_pauliXGate_onLeft_eq_linearToffoliBlocks`; immediate from
`barencoReductionCircuit_eq_mux_comp_tail` and the tail reduction. -/
theorem barencoReductionCircuit_pauliXGate_onLeft_eq_splitLinearToffoliBlocks (k d : ℕ) (hk : 2 ≤ k)
    (W : Evolution (qtower d qubit)) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 8 * (k + 1) ∧
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
    barencoTail_pauliXGate_onLeft_eq_splitLinearToffoliBlocks k d hk W
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  rw [barencoReductionCircuit_eq_mux_comp_tail, htail]

end AxQM
