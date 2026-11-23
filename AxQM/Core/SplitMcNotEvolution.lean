/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.McNotCircuitDecomposition
import AxQM.Concrete.MultiControlledNotSplit

/-!
# The one-borrowed-wire `Cᵐ(X)` split is a **linear** `Evolution` circuit (N&C Ex 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. The `O(n²)` count is
reached by bottoming each internal `Cᵏ(X)` block of `barencoNCircuit` in a **linear** `O(k)` number
of `Toffoli`s, borrowing the register's idle wires as **dirty** ancillas.

The Lemma-7.2 dirty cascade `Concrete.borrowedMcNot` is lifted to the `Evolution` level in
`AxQM/Core/BorrowedMcNotEvolution.lean` (`exists_borrowedCircuitEvolution_eq_placedMcNot`): a placed
`Cᵏ(X)` **is** a linear `≤ 4|as| + 1` `Toffoli`/`CNOT`/`NOT` `Evolution` circuit — but consuming
`|as| = |cs| - 2` **dirty borrowed ancillas**. That budget is met by the **small** blocks of
`barencoNCircuit V (n-1) 0` (a `Cʲ(X)` block sits with `n - j` idle module wires, so the `j - 2`
needed ancillas fit iff `j ≤ n/2 + 1`), but the **large** blocks — up to the top `C^{n-1}(X)` with
a *single* idle module wire — carry too few ancillas for Lemma 7.2 directly (the per-block
reduction `mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit` therefore carries the wire budget
`k - 2 ≤ d + 1`).

`AxQM/Concrete/MultiControlledNotSplit.lean` closes that gap at the *classical* level with
Barenco's **Lemma 7.3**: `Concrete.splitMcNot asA A asB B a t = W · V · W · V`, a `Cᵐ(X)`
(`m = |A| + |B|`) needing only **one** borrowed dirty wire `a`, by splitting the controls into two
halves `A`, `B` that supply each other's Lemma-7.2 dirty ancillas (`asA ⊆ B`, `asB ⊆ A`). It is a
genuine `Cᵐ(X)` restoring every wire (`Concrete.mcNotDenote_splitMcNot`), of `≤ 2`-control gates
(`Concrete.splitMcNot_gate_mem`), in a **linear** `≤ 8|asA| + 8|asB| + 4 = O(m)` count
(`Concrete.splitMcNot_length_le`). This file lifts that one-borrowed-wire classical circuit to the
closed-system `Evolution` level — the split-route counterpart of the abstract lift
`exists_borrowedCircuitEvolution_eq_placedMcNot`.

## What is formalised

* `exists_splitCircuitEvolution_eq_placedMcNot` — the **abstract one-borrowed-wire linear lift**.
  For control halves `A`, `B` with cross-borrowed dirty ancillas `asA`, `asB`
  (`|A| = |asA| + 2`, `|B| = |asB| + 1`), one borrowed dirty wire `a`, and target `t`, all wires
  suitably distinct (the same disjointness bundle Lemma 7.3 needs), the placed multiply-controlled
  `NOT` `Evolution.placedMcNot (A.toFinset ∪ B.toFinset) t` **equals**, as an `Evolution` on
  `qubit ^⊗ₛ m`, a genuine circuit `gs` of `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`, target never
  a control) with the **linear** count `gs.length ≤ 8|asA| + 8|asB| + 4 = O(|A| + |B|)`. The
  `Evolution`-level counterpart of `Concrete.splitMcNot`: feed `Concrete.splitMcNot asA A asB B a t`
  (gate set by
  `Concrete.splitMcNot_gate_mem`, length by `Concrete.splitMcNot_length_le`, denotation
  `= Concrete.mcNot (A.toFinset ∪ B.toFinset) t` by `Concrete.mcNotDenote_splitMcNot`) to the
  whole-circuit lift `exists_mcNotCircuitEvolution`, then identify the result with the placed gate
  by computational-basis extensionality (`Evolution.ext_qubitBasis`, both act as
  `Concrete.mcNot (A.toFinset ∪ B.toFinset) t`).

## Role in the `O(n²)` construction

The borrowed-wire lift consumes `|cs| - 2` borrowed ancillas; this one consumes just **one** (`a`) —
`asA`, `asB` are among the controls themselves. So it is the `Evolution`-level per-block reduction
the **large** `barencoNCircuit` blocks need, where only a single idle module wire remains. Applying
it to a `barencoNCircuit` block means choosing a half-split of the block's `k` front control wires
(`A`, `B`, `asA ⊆ B`, `asB ⊆ A`, `a` = one ambient wire), instantiating this lift, and identifying
`Evolution.placedMcNot (A.toFinset ∪ B.toFinset) t` with the contiguous front-block
`(Evolution.tensorPowMcCtrlX k).onBlock b` (the split-route counterpart of
`tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit`) — removing the `k - 2 ≤ d + 1` wire budget of
`mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit` and giving the uniform `O(n²)` count over all
blocks. The parity obstruction still forbids a permutation-only circuit on exactly `n + 1` wires, so
the `√X` single-qubit-controlled gates of `barencoNCircuit` remain essential; the linear per-block
ancillas here are borrowed from the tower's idle module wires, staying within the `n + 1`-wire
register (Barenco *Elementary gates for quantum computation*, Lemma 7.3).
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

/-- **N&C Exercise 4.29: the one-borrowed-wire `Cᵐ(X)` split is a linear `Evolution`
circuit.** For the two control halves `A`, `B` with cross-borrowed dirty ancillas `asA ⊆ B`,
`asB ⊆ A` (`|A| = |asA| + 2`, `|B| = |asB| + 1`), one borrowed dirty wire `a`, and target `t`, all
wires suitably distinct (`A.Nodup`, `asA.Nodup`, `B.Nodup`, `asB.Nodup`, the cross-disjointness
`A.Disjoint asA`, `B.Disjoint asB`, `a` outside `A`/`asA`/`B`/`asB`, `t` outside `A`/`B`/`asB`,
`a ≠ t`), there is a circuit `gs` of gates each with at most two controls (a `Toffoli`/`CNOT`/`NOT`,
target never a control) and a single closed-system `Evolution U` on `qubit ^⊗ₛ m` with:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — the gate set is `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ 8 * asA.length + 8 * asB.length + 4` — the **linear** `O(|A| + |B|)` gate count (four
  half-size Lemma-7.2 cascades), versus the `Θ(k²)` halving bound `Concrete.mcNotGateBound`, using
  just **one** borrowed dirty wire (`a`) rather than the `|cs| - 2` of
  `exists_borrowedCircuitEvolution_eq_placedMcNot`;
* `U` acts on every computational basis state `|⨂ᵢ c i⟩` as the classical circuit denotation
  `Concrete.mcNotDenote gs`; and
* `Evolution.placedMcNot (A.toFinset ∪ B.toFinset) t = U` — the placed multiply-controlled `NOT` on
  the wires `(A ∪ B, t)` **is** that linear circuit, as an `Evolution`.

The `Evolution`-level lift of `Concrete.mcNotDenote_splitMcNot`: the classical circuit is
`Concrete.splitMcNot asA A asB B a t` (gate set by `Concrete.splitMcNot_gate_mem`, length by
`Concrete.splitMcNot_length_le`, denotation `= Concrete.mcNot (A.toFinset ∪ B.toFinset) t` by
`Concrete.mcNotDenote_splitMcNot`); `exists_mcNotCircuitEvolution` lifts it to `U`, and
computational-basis extensionality (`Evolution.ext_qubitBasis`) identifies it with the placed gate
(`Evolution.placedMcNot_evolvePure_qubitBasis`). The split-route counterpart of
`exists_borrowedCircuitEvolution_eq_placedMcNot`. -/
theorem exists_splitCircuitEvolution_eq_placedMcNot {m : ℕ}
    (asA A asB B : List (Fin m)) (a t : Fin m)
    (hAlen : A.length = asA.length + 2) (hBlen : B.length = asB.length + 1)
    (hA : A.Nodup) (hasA : asA.Nodup) (hB : B.Nodup) (hasB : asB.Nodup)
    (hAasA : A.Disjoint asA) (hBasB : B.Disjoint asB)
    (haA : a ∉ A) (haasA : a ∉ asA) (haB : a ∉ B) (haasB : a ∉ asB)
    (htA : t ∉ A) (htB : t ∉ B) (htasB : t ∉ asB) (hat : a ≠ t) :
    ∃ (gs : List (Concrete.McNotGate m)) (U : Evolution (qubit.tensorPow m)),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 8 * asA.length + 8 * asB.length + 4 ∧
      (∀ c : Fin m → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      Evolution.placedMcNot (A.toFinset ∪ B.toFinset) t
          (fun h => (Finset.mem_union.mp h).elim
            (mt List.mem_toFinset.mp htA) (mt List.mem_toFinset.mp htB)) = U := by
  have hgate := Concrete.splitMcNot_gate_mem asA A asB B a t hAlen hBlen hA hasA hB hasB
    hAasA hBasB haA haasA haB haasB htB htasB hat
  obtain ⟨U, hU⟩ := exists_mcNotCircuitEvolution (Concrete.splitMcNot asA A asB B a t)
    (fun g hg => (hgate g hg).2)
  refine ⟨Concrete.splitMcNot asA A asB B a t, U, hgate,
    Concrete.splitMcNot_length_le asA A asB B a t, hU, ?_⟩
  refine Evolution.ext_qubitBasis fun c => ?_
  rw [Evolution.placedMcNot_evolvePure_qubitBasis, hU,
    Concrete.mcNotDenote_splitMcNot asA A asB B a t hAlen hBlen hA hasA hB hasB
      hAasA hBasB haA haasA haB haasB htA htB htasB hat]

end AxQM
