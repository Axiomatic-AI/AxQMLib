/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.SplitMcNotEvolution

/-!
# Block-embedded `Cᵏ(X)` is a one-borrowed-wire linear `Evolution` circuit (N&C Ex 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. `barencoNCircuit` reduces `Cⁿ(X)` to a
sequence of internal multiply-controlled `NOT` blocks `Cᵏ(X)`; bottoming each block to a
**linear** `O(k)` Toffoli circuit makes the summed count `O(n²)`.

`AxQM/Core/BorrowedMcNotEvolution.lean` gives a linear `Evolution` circuit for the
contiguous front-block `(Evolution.tensorPowMcCtrlX k).onBlock b`
(`tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit`), but through the Lemma-7.2 dirty cascade — so
it needs `k - 2` idle ambient wires to borrow (`k - 2 ≤ b`). That budget is met by the **small**
blocks of `barencoNCircuit` but fails for the **large** ones (up to `C^{n-1}(X)` with a single idle
module wire). `AxQM/Core/SplitMcNotEvolution.lean` lifts Barenco's **Lemma 7.3** split
(`Concrete.splitMcNot`, `W·V·W·V`) to the `Evolution` level
(`exists_splitCircuitEvolution_eq_placedMcNot`): a placed `Cᵐ(X)` **is** a linear circuit needing
just **one** borrowed dirty wire, the two control halves supplying each other's Lemma-7.2 ancillas.

## What is formalised

* `tensorPowMcCtrlX_onBlock_eq_splitLinearToffoliCircuit` — the **split-route** contiguous
  front-block reduction for the *large* blocks of the Barenco construction. For `k ≥ 3` and just
  **one** idle ambient wire (`1 ≤ b`), the block-embedded `Cᵏ(X)`
  `(Evolution.tensorPowMcCtrlX k).onBlock b` on `qubit ^⊗ₛ (k+1+b)` equals a genuine `Evolution`
  circuit of `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) with the **linear** count `≤ 8 k = O(k)` —
  the split-route counterpart of `tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit`, but
  replacing its wire budget `k - 2 ≤ b` by `1 ≤ b`.

  Obtained by instantiating the abstract lift `exists_splitCircuitEvolution_eq_placedMcNot` at the
  **balanced half-split** of the `k` front control wires `cs = ((cnxControls k).image (Fin.castAdd
  b)).toList`: `A = cs.take p`, `B = cs.drop p` with `p = k - k/2 = ⌈k/2⌉`, `q = k/2 = ⌊k/2⌋`,
  cross-borrowed dirty ancillas `asA = B.take (p-2)`, `asB = A.take (q-1)` (each half supplies the
  other's ancillas: `asA ⊆ B`, `asB ⊆ A`), and one borrowed ambient wire `a = ⟨k+1, _⟩`. The split's
  control set is exactly the front controls (`A.toFinset ∪ B.toFinset = (cnxControls k).image
  (Fin.castAdd b)`, from `take ++ drop = cs`), so the resulting `Evolution.placedMcNot (A.toFinset ∪
  B.toFinset) t` matches the block `onBlock` through the block truth table
  `tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis` and the placed-gate truth table
  `Evolution.placedMcNot_evolvePure_qubitBasis` (`Evolution.ext_qubitBasis`).

## Role in the `O(n²)` construction

This removes the `k - 2 ≤ d + 1` wire budget of `mcCtrl_pauliXGate_onLeft_eq_linearToffoliCircuit`:
a single idle module wire now suffices to bottom **any** internal block linearly. Applied uniformly
across the `O(n)` internal `Cᵏ(X)` blocks of `barencoNCircuit`, the linear `O(k)` per-block count
gives the exercise's `O(n²)` total. The parity obstruction still forbids a permutation-only circuit
on exactly `n + 1` wires, so the `√X` single-qubit-controlled gates of `barencoNCircuit` remain
essential; the one borrowed ancilla here is an idle tower module wire, staying within the
`n + 1`-wire register (Barenco *Elementary gates for quantum computation*, Lemma 7.3).
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

/-- **N&C Exercise 4.29: the block-embedded `Cᵏ(X)` is a one-borrowed-wire linear
Toffoli circuit.** The contiguous front-block placement `(Evolution.tensorPowMcCtrlX k).onBlock b` —
the grounded `Cᵏ(X)` (`k` controls, one target = the leading `k + 1` wires) acting as the identity
on the trailing `b` ambient wires of `qubit ^⊗ₛ (k+1+b)` — is, **as an `Evolution`**, a genuine
circuit of `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) with the **linear** count `≤ 8 k = O(k)`,
provided the register carries **one** idle ambient wire to borrow (`1 ≤ b`, `k ≥ 3`).

The split-route counterpart of `tensorPowMcCtrlX_onBlock_eq_linearToffoliCircuit` (which
needs `k - 2 ≤ b` borrowed wires). Instantiates `exists_splitCircuitEvolution_eq_placedMcNot`
(Barenco Lemma 7.3) at the balanced half-split of the `k` front control wires
`cs = ((cnxControls k).image (Fin.castAdd b)).toList`: `A = cs.take (k - k/2)`,
`B = cs.drop (k - k/2)`, cross-borrowed dirty ancillas `asA = B.take (k - k/2 - 2)`,
`asB = A.take (k/2 - 1)`, and one borrowed ambient wire `a = ⟨k+1, _⟩`. Since
`A.toFinset ∪ B.toFinset` is exactly the front control set (`take ++ drop = cs`), the resulting
`Evolution.placedMcNot (A.toFinset ∪ B.toFinset) t` is identified with the block `onBlock` by
computational-basis extensionality (`Evolution.ext_qubitBasis`, both act as
`Concrete.mcNot ((cnxControls k).image (Fin.castAdd b)) (Fin.castAdd b (Fin.last k))`). The `1 ≤ b`
wire budget is the cost of the Lemma 7.3 construction's single borrowed dirty ancilla; it is met
by `barencoNCircuit`'s idle-wire register even for the largest blocks. -/
theorem tensorPowMcCtrlX_onBlock_eq_splitLinearToffoliCircuit {k b : ℕ}
    (hk : 3 ≤ k) (hb : 1 ≤ b) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + b))) (U : Evolution (qubit.tensorPow (k + 1 + b))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ 8 * k ∧
      (∀ c : Fin (k + 1 + b) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      (Evolution.tensorPowMcCtrlX k).onBlock b = U := by
  -- The `k` front control wires as a list, and the register's half-split.
  set cs : List (Fin (k + 1 + b)) := ((cnxControls k).image (Fin.castAdd b)).toList with hcs_def
  set p : ℕ := k - k / 2 with hp
  set q : ℕ := k / 2 with hq
  set A : List (Fin (k + 1 + b)) := cs.take p with hA_def
  set B : List (Fin (k + 1 + b)) := cs.drop p with hB_def
  set asA : List (Fin (k + 1 + b)) := B.take (p - 2) with hasA_def
  set asB : List (Fin (k + 1 + b)) := A.take (q - 1) with hasB_def
  set a : Fin (k + 1 + b) := ⟨k + 1, by omega⟩ with ha_def
  set t : Fin (k + 1 + b) := Fin.castAdd b (Fin.last k) with htgt
  -- Basic facts about the control list `cs`.
  have hcs_nodup : cs.Nodup := by rw [hcs_def]; exact Finset.nodup_toList _
  have hcs_len : cs.length = k := by
    rw [hcs_def, Finset.length_toList,
      Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
      cnxControls_eq_image_castSucc, Finset.card_image_of_injective _ (Fin.castSucc_injective k),
      Finset.card_univ, Fintype.card_fin]
  have hcs_val : ∀ x ∈ cs, (x : ℕ) < k := by
    intro x hx
    rw [hcs_def, Finset.mem_toList, Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [Fin.val_castAdd]
    exact (mem_cnxControls j).mp hj
  -- Lengths of the four split lists.
  have hA_len : A.length = p := by
    rw [hA_def, List.length_take, hcs_len, Nat.min_eq_left (by omega)]
  have hB_len : B.length = q := by rw [hB_def, List.length_drop, hcs_len]; omega
  have hasA_len : asA.length = p - 2 := by
    rw [hasA_def, List.length_take, hB_len, Nat.min_eq_left (by omega)]
  have hasB_len : asB.length = q - 1 := by
    rw [hasB_def, List.length_take, hA_len, Nat.min_eq_left (by omega)]
  have hAlen : A.length = asA.length + 2 := by rw [hA_len, hasA_len]; omega
  have hBlen : B.length = asB.length + 1 := by rw [hB_len, hasB_len]; omega
  -- Nodups.
  have hA_nodup : A.Nodup := by rw [hA_def]; exact hcs_nodup.sublist (List.take_sublist _ _)
  have hB_nodup : B.Nodup := by rw [hB_def]; exact hcs_nodup.sublist (List.drop_sublist _ _)
  have hasA_nodup : asA.Nodup := by rw [hasA_def]; exact hB_nodup.sublist (List.take_sublist _ _)
  have hasB_nodup : asB.Nodup := by rw [hasB_def]; exact hA_nodup.sublist (List.take_sublist _ _)
  -- Cross-disjointness of the halves and their borrowed ancillas.
  have hAasA : A.Disjoint asA := by
    rw [hA_def, hasA_def, hB_def]
    exact fun x hx hx' => List.disjoint_take_drop hcs_nodup le_rfl hx (List.take_subset _ _ hx')
  have hBasB : B.Disjoint asB := by
    rw [hB_def, hasB_def, hA_def]
    exact fun x hx hx' =>
      (List.disjoint_take_drop hcs_nodup le_rfl).symm hx (List.take_subset _ _ hx')
  -- Subset facts locating every split wire inside `cs`.
  have hA_sub : A ⊆ cs := by rw [hA_def]; exact List.take_subset _ _
  have hB_sub : B ⊆ cs := by rw [hB_def]; exact List.drop_subset _ _
  have hasA_sub : asA ⊆ cs := by
    rw [hasA_def]; exact List.Subset.trans (List.take_subset _ _) hB_sub
  have hasB_sub : asB ⊆ cs := by
    rw [hasB_def]; exact List.Subset.trans (List.take_subset _ _) hA_sub
  -- The borrowed ambient wire `a` (value `k+1`) and the target `t` (value `k`) miss every control.
  have ha_val : (a : ℕ) = k + 1 := by rw [ha_def]
  have ht_val : (t : ℕ) = k := by rw [htgt]; simp only [Fin.val_castAdd, Fin.val_last]
  have ha_cs : a ∉ cs := fun h => by have := hcs_val a h; omega
  have ht_cs : t ∉ cs := fun h => by have := hcs_val t h; omega
  have haA : a ∉ A := fun h => ha_cs (hA_sub h)
  have haB : a ∉ B := fun h => ha_cs (hB_sub h)
  have haasA : a ∉ asA := fun h => ha_cs (hasA_sub h)
  have haasB : a ∉ asB := fun h => ha_cs (hasB_sub h)
  have htA : t ∉ A := fun h => ht_cs (hA_sub h)
  have htB : t ∉ B := fun h => ht_cs (hB_sub h)
  have htasB : t ∉ asB := fun h => ht_cs (hasB_sub h)
  have hat : a ≠ t := Fin.ne_of_val_ne (by rw [ha_val, ht_val]; omega)
  -- The split's control set is exactly the front controls.
  have hAB : A.toFinset ∪ B.toFinset = (cnxControls k).image (Fin.castAdd b) := by
    rw [hA_def, hB_def, ← List.toFinset_append, List.take_append_drop, hcs_def,
      Finset.toList_toFinset]
  -- Feed the half-split into the abstract one-borrowed-wire lift.
  obtain ⟨gs, U, hgate, hglen, hUc, hplaced⟩ :=
    exists_splitCircuitEvolution_eq_placedMcNot asA A asB B a t hAlen hBlen
      hA_nodup hasA_nodup hB_nodup hasB_nodup hAasA hBasB haA haasA haB haasB htA htB htasB hat
  refine ⟨gs, U, hgate, le_trans hglen ?_, hUc, ?_⟩
  · rw [hasA_len, hasB_len]; omega
  · rw [← hplaced]
    refine Evolution.ext_qubitBasis fun c => ?_
    rw [tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis, Evolution.placedMcNot_evolvePure_qubitBasis,
      hAB, htgt]

end AxQM
