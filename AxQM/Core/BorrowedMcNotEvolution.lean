/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.McNotCircuitDecomposition
import AxQM.Concrete.MultiControlledNotBorrowedMcNot

/-!
# The dirty-ancilla `Cᵏ(X)` is a **linear** `Evolution` circuit (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The per-block decomposition
`exists_mcNotCircuitEvolution_eq_placedMcNot` realises a placed `Cᵏ(X)` as a genuine `Evolution`
circuit, but only through the **halving** classical construction
`Concrete.exists_mcNotCircuit`, whose gate count is `Θ(k²)` (`Concrete.mcNotGateBound`). Summed over
`barencoNCircuit`'s `O(n)` internal blocks that is `Θ(n³)` — overshooting the exercise's `O(n²)`.

The file `AxQM/Concrete/MultiControlledNotBorrowedMcNot.lean` fixes the *classical* count: the
double borrowed-wire cascade `Concrete.borrowedMcNot as cs tgt` is a genuine `Cᵏ(X)` in a **linear**
`≤ 4|as| + 1` `Toffoli`/`CNOT`/`NOT` gates (`|as| = |cs| - 2` **dirty** borrowed ancillas,
`Concrete.mcNotDenote_borrowedMcNot`; Barenco *Elementary gates*, Lemma 7.2/7.3). This file lifts
that linear classical circuit to the closed-system `Evolution` level.

## What is formalised

* `exists_borrowedCircuitEvolution_eq_placedMcNot` — the **abstract linear lift**. For control and
  borrowed-ancilla wire lists `cs`, `as` with `|cs| = |as| + 2` (all distinct, target `tgt` off
  both), the placed multiply-controlled `NOT` `Evolution.placedMcNot cs.toFinset tgt` **equals**, as
  an `Evolution` on `qubit ^⊗ₛ m`, a genuine circuit `gs` of `≤ 2`-control gates with the **linear**
  count `gs.length ≤ 4 |as| + 1 = O(|cs|)` — not the `Θ(k²)` of
  `exists_mcNotCircuitEvolution_eq_placedMcNot`. The `Evolution`-level
  counterpart of the classical statement: feed `Concrete.borrowedMcNot as cs tgt` (whose gates are
  `≤ 2`-control by `borrowedMcNot_gate_mem` and whose denotation is `Concrete.mcNot cs.toFinset tgt`
  by `mcNotDenote_borrowedMcNot`) to the whole-circuit lift `exists_mcNotCircuitEvolution`, then
  identify the result with the placed gate by computational-basis extensionality
  (`Evolution.ext_qubitBasis`, both act as `Concrete.mcNot cs.toFinset tgt`).

* `tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit` — the **contiguous front-block** form the
  Barenco assembly consumes. Whenever the register carries at least `k - 2` idle ambient wires to
  borrow (`k - 2 ≤ b`, the honest wire budget of Lemma 7.2's `k - 2` dirty ancillas), the
  block-embedded `Cᵏ(X)` `(Evolution.tensorPowMcCtrlX k).onBlock b` on `qubit ^⊗ₛ (k+1+b)` equals a
  genuine `Evolution` circuit of `≤ 2`-control gates with the **linear** count
  `≤ 4 (k - 2) + 1 = O(k)`. The linear-count counterpart of
  `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`, obtained by instantiating the abstract lift at
  `cs =` the `k` front control wires `(cnxControls k).image (Fin.castAdd b)` and `as =` the first
  `k - 2` ambient wires `Fin.natAdd (k+1) ·`, then matching to `onBlock` through the block truth
  table `tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis`.

## The count for `barencoNCircuit`

This replaces the `Θ(k²)` per-block bound of `exists_mcNotCircuitEvolution_eq_placedMcNot` and
`tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` by the `O(k)` linear one. Summed over the
`O(n)` internal `Cᵏ(X)` blocks of the no-work-qubit `Cⁿ(X)` circuit (`barencoNCircuit`), the
linear per-block count gives the exercise's `O(n²)` rather than `O(n³)`. The
wire budget `k - 2 ≤ b` is the honest cost of the Lemma 7.2 construction (`k - 2` borrowed dirty
ancillas); it is discharged from `barencoNCircuit`'s idle-wire register in
`AxQM/Core/BarencoLinearBlockReduction.lean`, and the one-borrowed-ancilla Lemma 7.3 route where the
budget is tighter is in `AxQM/Core/BarencoSplitLinearBlockReduction.lean`.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

/-- **N&C Exercise 4.29: the dirty-ancilla `Cᵏ(X)` is a linear `Evolution` circuit.**
Given a control wire list `cs`, a borrowed dirty-ancilla wire list `as` with `|cs| = |as| + 2`, a
target `tgt`, all wires distinct (`cs.Nodup`, `as.Nodup`, `cs.Disjoint as`, `tgt ∉ cs`, `tgt ∉ as`),
there is a circuit `gs` of gates each with at most two controls (a `Toffoli`/`CNOT`/`NOT`, target
never a control) and a single closed-system `Evolution U` on `qubit ^⊗ₛ m` with:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — the gate set is `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ 4 * as.length + 1` — the **linear** `O(|cs|)` gate count (`|as| = |cs| - 2`), the
  count the `O(n²)` assembly needs, versus the `Θ(k²)` halving bound of
  `exists_mcNotCircuitEvolution_eq_placedMcNot`;
* `U` acts on every computational basis state `|⨂ᵢ c i⟩` as the classical circuit denotation
  `Concrete.mcNotDenote gs` — so `U` *is* the placed gate sequence of `gs`; and
* `Evolution.placedMcNot cs.toFinset tgt = U` — the placed multiply-controlled `NOT` on the wires
  `(cs.toFinset, tgt)` **is** that linear circuit, as an `Evolution`.

The `Evolution`-level lift of the classical `Concrete.mcNotDenote_borrowedMcNot`: the classical
circuit is `Concrete.borrowedMcNot as cs tgt` (gate set by `Concrete.borrowedMcNot_gate_mem`, length
by `Concrete.borrowedMcNot_length_le`, denotation `= Concrete.mcNot cs.toFinset tgt` by
`Concrete.mcNotDenote_borrowedMcNot`); `exists_mcNotCircuitEvolution` lifts it to `U`,
and computational-basis extensionality (`Evolution.ext_qubitBasis`) identifies it with the placed
gate (`Evolution.placedMcNot_evolvePure_qubitBasis`). -/
theorem exists_borrowedCircuitEvolution_eq_placedMcNot {m : ℕ}
    (as cs : List (Fin m)) (tgt : Fin m)
    (hlen : cs.length = as.length + 2) (hcs : cs.Nodup) (has : as.Nodup)
    (hdisj : cs.Disjoint as) (htcs : tgt ∉ cs) (htas : tgt ∉ as) :
    ∃ (gs : List (Concrete.McNotGate m)) (U : Evolution (qubit.tensorPow m)),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 4 * as.length + 1 ∧
      (∀ c : Fin m → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      Evolution.placedMcNot cs.toFinset tgt (mt List.mem_toFinset.mp htcs) = U := by
  have hgate := Concrete.borrowedMcNot_gate_mem as cs tgt hlen hcs has hdisj htcs htas
  obtain ⟨U, hU⟩ := exists_mcNotCircuitEvolution (Concrete.borrowedMcNot as cs tgt)
    (fun g hg => (hgate g hg).2)
  refine ⟨Concrete.borrowedMcNot as cs tgt, U, hgate,
    Concrete.borrowedMcNot_length_le as cs tgt, hU, ?_⟩
  refine Evolution.ext_qubitBasis fun c => ?_
  rw [Evolution.placedMcNot_evolvePure_qubitBasis, hU,
    Concrete.mcNotDenote_borrowedMcNot as cs tgt hlen hcs has hdisj htcs htas]

/-- **N&C Exercise 4.29: the block-embedded `Cᵏ(X)` is a linear Toffoli circuit.** The
contiguous front-block placement `(Evolution.tensorPowMcCtrlX k).onBlock b` — the grounded `Cᵏ(X)`
(`k` controls, one target = the leading `k + 1` wires) acting as the identity on the trailing `b`
ambient wires of `qubit ^⊗ₛ (k+1+b)` — is, **as an `Evolution`**, a genuine circuit of `≤ 2`-control
gates (`Toffoli`/`CNOT`/`NOT`) with the **linear** count `≤ 4 (k - 2) + 1 = O(k)`, provided the
register carries at least `k - 2` idle ambient wires to borrow (`k - 2 ≤ b`).

The linear-count counterpart of `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` (which uses
the `Θ(k²)` halving circuit). Instantiates `exists_borrowedCircuitEvolution_eq_placedMcNot` at the
`k` front control wires `cs = ((cnxControls k).image (Fin.castAdd b)).toList` and the first `k - 2`
ambient wires `as = ((Fin.natAdd (k+1)) <$> List.finRange b).take (k - 2)`, then identifies the
resulting `Evolution.placedMcNot cs.toFinset (Fin.castAdd b (Fin.last k))` with the block
`onBlock` through the block truth table `tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis` and the
placed-gate truth table `Evolution.placedMcNot_evolvePure_qubitBasis`
(`Evolution.ext_qubitBasis`). The wire budget `k - 2 ≤ b` is the honest cost of the Lemma 7.2
construction's `k - 2` borrowed dirty ancillas; it is discharged from
`barencoNCircuit`'s idle-wire register in `AxQM/Core/BarencoLinearBlockReduction.lean`. -/
theorem tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit {k b : ℕ} (hk : 2 ≤ k) (hb : k - 2 ≤ b) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + b))) (U : Evolution (qubit.tensorPow (k + 1 + b))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 4 * (k - 2) + 1 ∧
      (∀ c : Fin (k + 1 + b) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      (Evolution.tensorPowMcCtrlX k).onBlock b = U := by
  -- The `k` front control wires and the target wire `k`.
  set S : Finset (Fin (k + 1 + b)) := (cnxControls k).image (Fin.castAdd b) with hS
  set cs : List (Fin (k + 1 + b)) := S.toList with hcs_def
  set tgt : Fin (k + 1 + b) := Fin.castAdd b (Fin.last k) with htgt
  -- The first `k - 2` ambient wires (all with value `≥ k + 1`) as borrowed dirty ancillas.
  set as : List (Fin (k + 1 + b)) :=
    ((List.finRange b).map (Fin.natAdd (k + 1))).take (k - 2) with has_def
  -- Wire-value bounds separating controls (`≤ k`) from ambient ancillas (`≥ k + 1`).
  have hcs_val : ∀ x ∈ cs, (x : ℕ) < k + 1 := by
    intro x hx
    rw [hcs_def, Finset.mem_toList, hS, Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    simpa using j.2
  have has_val : ∀ x ∈ as, k + 1 ≤ (x : ℕ) := by
    intro x hx
    have hx' : x ∈ (List.finRange b).map (Fin.natAdd (k + 1)) :=
      (List.take_subset _ _) hx
    rw [List.mem_map] at hx'
    obtain ⟨j, _, rfl⟩ := hx'
    simp [Fin.natAdd]
  -- Distinctness bookkeeping.
  have hcs_nodup : cs.Nodup := by rw [hcs_def]; exact Finset.nodup_toList _
  have has_nodup : as.Nodup := by
    rw [has_def]
    exact (((List.nodup_finRange b).map (Fin.natAdd_injective _ _)).sublist
      (List.take_sublist _ _))
  have hcs_len : cs.length = k := by
    rw [hcs_def, Finset.length_toList, hS,
      Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
      cnxControls_eq_image_castSucc, Finset.card_image_of_injective _ (Fin.castSucc_injective k),
      Finset.card_univ, Fintype.card_fin]
  have has_len : as.length = k - 2 := by
    rw [has_def, List.length_take, List.length_map, List.length_finRange]
    exact Nat.min_eq_left hb
  have hlen : cs.length = as.length + 2 := by rw [hcs_len, has_len]; omega
  have hdisj : cs.Disjoint as := fun x hxcs hxas =>
    absurd (has_val x hxas) (by have := hcs_val x hxcs; omega)
  have htcs : tgt ∉ cs := by
    intro h
    rw [hcs_def, Finset.mem_toList, hS, Finset.mem_image] at h
    obtain ⟨j, hj, hje⟩ := h
    rw [htgt] at hje
    exact last_notMem_cnxControls k ((Fin.castAdd_injective _ _ hje) ▸ hj)
  have htas : tgt ∉ as := fun h => by
    have := has_val tgt h
    rw [htgt] at this
    simp only [Fin.val_castAdd, Fin.val_last] at this
    omega
  obtain ⟨gs, U, hgate, hglen, hUc, hplaced⟩ :=
    exists_borrowedCircuitEvolution_eq_placedMcNot as cs tgt hlen hcs_nodup has_nodup hdisj htcs
      htas
  refine ⟨gs, U, hgate, has_len ▸ hglen, hUc, ?_⟩
  rw [← hplaced]
  refine Evolution.ext_qubitBasis fun c => ?_
  rw [tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis, Evolution.placedMcNot_evolvePure_qubitBasis]
  refine congrArg PureState.piTensor ?_
  funext i
  refine congrArg qubitBasis ?_
  rw [hcs_def, Finset.toList_toFinset, hS, htgt]

end AxQM
