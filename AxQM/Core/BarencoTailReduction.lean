/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.BarencoBlockReduction

/-!
# One Barenco reduction layer's `Cᵏ(X)` blocks are bounded Toffoli circuits (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`): a nested stack of
**reduction layers**, each layer being a `barencoTail k W` composed under a leading multiplexer
(`barencoReductionCircuit_eq_mux_comp_tail`). Every `barencoTail k W` is, by definition,

`barencoTail k W = Cᵏ(X) · C(W†) · Cᵏ(X) · C(W)`

— **two** multiply-controlled `NOT` blocks `Cᵏ(X) = mcCtrl k (pauliXGate.onLeft M)` and two
single-qubit-controlled gates `C(W)`, `C(W†)` (`unCtrl k (controlledUnitary …)`), where in
`barencoNCircuit` the target module is `M = qtower d qubit` (the `d` already-peeled controls, idle).
The exercise's distinctive content is bottoming those `Cᵏ(X)` blocks to genuine `Toffoli`s.

`mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` does this for **one** block on its control
tower. This file lifts that to one whole layer: it replaces both `Cᵏ(X)` blocks of a
`barencoTail (k+1) W` (`W : Evolution (qtower d qubit)`) by the transported bounded
`≤ 2`-control (`Toffoli`/`CNOT`/`NOT`) circuit of that theorem, leaving the two
single-qubit-controlled gates `C(W)`, `C(W†)` intact. It is the per-layer object that is folded over
the recursion of `barencoNCircuit`.

## What is formalised

`barencoTail_pauliXGate_onLeft_eq_toffoliBlocks` — for every `k`, `d` and every single-qubit-chain
gate `W : Evolution (qtower d qubit)`, one Barenco tail layer is an honest `Evolution` composition

`barencoTail (k+1) W = B · C(W†) · B · C(W)`,

where `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U` is the transported circuit of
`mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` —
a genuine circuit `gs` of `≤ 2`-control gates (`∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1`), of length
`gs.length ≤ mcNotGateBound (k+1)`, acting on every computational basis state as `mcNotDenote gs` —
and `C(W)`, `C(W†)` are the single-qubit-controlled gates (`unCtrl (k+1) (controlledUnitary …)`).
The **same** block circuit `B` serves both `Cᵏ⁺¹(X)` occurrences (they are the identical gate), so
the layer's whole `≤ 2`-control content is `2 · gs.length ≤ 2 · mcNotGateBound (k+1)` plus the two
single-qubit-controlled gates. Immediate from `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` and the
definitional unfolding of `barencoTail`.

## The gate count — an honest scoping note

This file gives property **(ii)** of the exercise (each block is a genuine
`Toffoli`/`CNOT`/`NOT` circuit) at the layer level; it does **not** by itself give the
exercise's **(iii)** `O(n²)` count for the whole `barencoNCircuit`. `barencoNCircuit V k 0` has one
layer for each `j = 1, …, k`, contributing two `Cʲ(X)` blocks; summing the per-block bound
over the layers gives `Σⱼ 2·mcNotGateBound j`, and `mcNotGateBound` is `Θ(j²)`, so the
sum is `Θ(k³) = O(n³)`, **not** the exercise's `O(n²)`. Barenco's `O(n²)` needs each `Cʲ(X)` block
bottomed in `O(j)` **linear** `Toffoli`s using an available idle wire as a borrowed (dirty) ancilla
(Barenco *Elementary gates*, Lemma 7.2 / 7.3); that construction is in
`AxQM/Core/BarencoLinearBlockReduction.lean` and `AxQM/Core/BarencoSplitLinearBlockReduction.lean`
(the `Θ(k²)` halving used here is `Concrete.exists_mcNotCircuit`). This layer reduction stays valid
for it (it is a **structural** identity — only the per-block length bound `B` carries is replaced).
The structure given here (`2` bounded blocks + `2` single-qubit-controlled gates per layer) is
route-independent.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **N&C Exercise 4.29: one Barenco reduction layer's `Cᵏ(X)`
blocks are a bounded Toffoli circuit.** For every `k`, `d` and every single-qubit-chain gate
`W : Evolution (qtower d qubit)`, the Barenco tail layer `barencoTail (k+1) W` — on the control
tower `qtower (k+1) (qubit ⊗ qtower d qubit)` — is the `Evolution` composition

`barencoTail (k+1) W = B · C(W†) · B · C(W)`,

where the two `Cᵏ⁺¹(X)` blocks `mcCtrl (k+1) (pauliXGate.onLeft (qtower d qubit))` are **both** the
single transported circuit `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U` of
`mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit`,
and `C(W) = unCtrl (k+1) (controlledUnitary W)`, `C(W†) = unCtrl (k+1) (controlledUnitary
W.adjoint)` are the two single-qubit-controlled gates. The transported block `B` carries the
certificates of that theorem for the circuit `gs : List (McNotGate (k+1+1+(d+1)))`:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — every gate is a `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ mcNotGateBound (k+1)` — the per-block gate count;
* `U` acts on every computational basis state `⨂ᵢ |c i⟩` as the classical circuit `mcNotDenote gs`.

So one layer's whole `≤ 2`-control content is `2 · gs.length` (the same `gs` twice), plus two
single-qubit-controlled gates. This is the per-layer object that the full `barencoNCircuit`
assembly folds over; see the file docstring for the honest `O(n²)`-vs-`O(n³)` count scoping.
Immediate from `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` and the definition of
`barencoTail`. -/
theorem barencoTail_pauliXGate_onLeft_eq_toffoliBlocks (k d : ℕ)
    (W : Evolution (qtower d qubit)) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ Concrete.mcNotGateBound (k + 1) ∧
      (∀ c : Fin (k + 1 + 1 + (d + 1)) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      barencoTail (k + 1) W
        = (Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
            ((unCtrl (k + 1) (controlledUnitary W.adjoint)).comp
              ((Evolution.congr (barencoBlockFlatten (k + 1) d).symm U).comp
                (unCtrl (k + 1) (controlledUnitary W)))) := by
  obtain ⟨gs, U, hgs, hlen, hUc, hblock⟩ :=
    mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit (k + 1) d
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  unfold barencoTail
  rw [hblock]

/-- **N&C Exercise 4.29: one full Figure-4.8 reduction layer, with
its `Cᵏ(X)` blocks bottomed to Toffolis.** For every `k`, `d` and single-qubit-chain gate
`W : Evolution (qtower d qubit)`, the whole Figure-4.8 reduction circuit `barencoReductionCircuit
(k+1) W` (= `Cᵏ⁺¹(W) · barencoTail (k+1) W`, `barencoReductionCircuit_eq_mux_comp_tail`) is the
`Evolution` composition

`barencoReductionCircuit (k+1) W = Cᵏ⁺¹(W) · B · C(W†) · B · C(W)`,

with the leading multiplexer `Cᵏ⁺¹(W) = mcCtrl (k+1) (W.onRight qubit)` left as is (it is what the
`barencoNCircuit` recursion expands next), the two `Cᵏ⁺¹(X)` blocks replaced by the single
transported bounded `≤ 2`-control circuit `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U`
(certificates as in `barencoTail_pauliXGate_onLeft_eq_toffoliBlocks`), and the two
single-qubit-controlled gates `C(W)`, `C(W†)` kept. This is the reduction layer exactly as it
appears in `barencoNCircuit`, with its multiply-controlled `NOT`s bottomed. Immediate from
`barencoReductionCircuit_eq_mux_comp_tail` and the tail reduction. -/
theorem barencoReductionCircuit_pauliXGate_onLeft_eq_toffoliBlocks (k d : ℕ)
    (W : Evolution (qtower d qubit)) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ Concrete.mcNotGateBound (k + 1) ∧
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
    barencoTail_pauliXGate_onLeft_eq_toffoliBlocks k d W
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  rw [barencoReductionCircuit_eq_mux_comp_tail, htail]

end AxQM
