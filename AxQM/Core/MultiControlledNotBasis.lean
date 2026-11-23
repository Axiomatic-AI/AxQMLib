/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction
import AxQM.Concrete.MultiControlledNot

/-!
# The multiply-controlled `NOT` `Cⁿ(X)` acts on the computational basis as the classical `mcNot`
(N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)`-gate no-work-qubit circuit of Toffoli,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. Every such gate is a
permutation of the computational basis, and `AxQM/Concrete/MultiControlledNot*.lean` builds
the whole construction — the dirty-borrow reduction `mcNot_union_borrow`, the recursive circuit
`exists_mcNotCircuit`, and its `O(n²)` gate-count bound `mcNotGateBound_isBigO_sq` — at the level of
the **classical** reversible model: bit-strings `Fin m → Fin 2` and the multiply-controlled `NOT`
`Concrete.mcNot S t`.

This file is the **bridge** that ties that classical model to the quantum gate.
The quantum `Cⁿ(X)` is `mcCtrl n pauliXGate : Evolution (qtower n qubit)` — the Pauli-`X` gate
wrapped by `n` control qubits (`Core/MultiControlledReduction`), acting on the `(n+1)`-qubit
register `qtower n qubit` with **no work qubit**. We prove it acts on the computational basis
exactly as the classical `mcNot` with controls the first `n` wires and target the last:

`(mcCtrl n pauliXGate).evolvePure (towerKet n b)`
`  = towerKet n (mcNot (cnxControls n) (Fin.last n) b)`
  (`mcCtrl_pauliXGate_evolvePure_towerKet`),

where `towerKet n : (Fin (n+1) → Fin 2) → PureState (qtower n qubit)` is the `(n+1)`-qubit
computational basis (wire `0` the outermost control, wire `n` the target). So the *quantum* `Cⁿ(X)`
**is** the *classical* `Cⁿ(X)` on basis states: the reversible permutation whose `O(n²)`
no-work-qubit circuit the `Concrete/` development exhibits. The statement of Exercise 4.29
is in `AxQM/NC/Ch4/Exercise4_29.lean`.

## The proof

Induction on `n`, peeling one control at a time. `mcCtrl (n+1) E = C(mcCtrl n E)` and
`towerKet (n+1) b = |b 0⟩ ⊗ towerKet n (b ∘ succ)`, so the control-`|0⟩`/`|1⟩` action of
`controlledUnitary` (`controlledUnitary_evolvePure_ketZero` / `_ketOne`) splits the step: on
`b 0 = 0` the gate is the identity and `mcNot` fixes `b` (the outer control is unset, so
`ctrlBit = 0`); on `b 0 = 1` it recurses on the tail, matched to the tail `mcNot` by
`ctrlBit_cnxControls_succ` (the outer control being set makes the `(n+1)`-control condition collapse
to the `n`-control one on the shifted wires). The base case is `pauliXGate_evolvePure_qubitBasis`
(`X|i⟩ = |i+1⟩`) against `ctrlBit ∅ = 1` (the empty-control `NOT` always flips).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

open AxQM.Concrete

/-- **The `(n+1)`-qubit computational basis** `towerKet n b` of the control register
`qtower n qubit = qubitⁿ ⊗ qubit`, indexed by a bit-string `b : Fin (n+1) → Fin 2` with wire `0` the
outermost control and wire `n` the target: the product state `|b 0⟩ ⊗ |b 1⟩ ⊗ … ⊗ |b n⟩`. -/
def towerKet : (n : ℕ) → (Fin (n + 1) → Fin 2) → PureState (qtower n qubit)
  | 0, b => qubitBasis (b 0)
  | n + 1, b => (qubitBasis (b 0)).tmul (towerKet n (fun i => b i.succ))

/-- Base unfolding of `towerKet`: a single-qubit register is the basis state of its one wire. -/
@[simp] theorem towerKet_zero (b : Fin 1 → Fin 2) : towerKet 0 b = qubitBasis (b 0) := rfl

/-- Step unfolding of `towerKet`: peel the outermost control wire as a left tensor factor. -/
theorem towerKet_succ (n : ℕ) (b : Fin (n + 2) → Fin 2) :
    towerKet (n + 1) b = (qubitBasis (b 0)).tmul (towerKet n (fun i => b i.succ)) := rfl

/-- **The `n` control wires** `{0, 1, …, n-1}` of the aligned `Cⁿ(X)` on `qtower n qubit`; the
target is the last wire `Fin.last n`. Defined so that
`cnxControls (n+1) = insert 0 (image succ (cnxControls n))` holds by `rfl`, matching how `mcCtrl`
adds one control on the left. -/
def cnxControls : (n : ℕ) → Finset (Fin (n + 1))
  | 0 => ∅
  | n + 1 => insert 0 ((cnxControls n).image Fin.succ)

/-- **Membership in the control-wire set** `cnxControls k` (`= {0, 1, …, k-1} ⊆ Fin (k+1)`): a wire
`j : Fin (k+1)` is a control iff its value is below `k` (equivalently, iff it is not the target
wire `Fin.last k`). Proved by induction on `k`, unfolding
`cnxControls (k+1) = insert 0 (image succ …)`. -/
theorem mem_cnxControls {k : ℕ} (j : Fin (k + 1)) : j ∈ cnxControls k ↔ (j : ℕ) < k := by
  induction k with
  | zero => simp [cnxControls]
  | succ k ih =>
    simp only [cnxControls, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | ⟨a, ha, rfl⟩)
      · simp
      · have := (ih a).mp ha; simp only [Fin.val_succ]; omega
    · intro hj
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨j', (ih j').mpr ?_, rfl⟩
        simp only [Fin.val_succ] at hj; omega

/-- **The control-wire set as the image of `Fin.castSucc`.** The `k` front control wires
`cnxControls k` of `Fin (k+1)` are exactly the images `Fin.castSucc i` of the `k` wires
`i : Fin k` — the front `k` of the `k+1` wires. Lets an image over `cnxControls k` be reindexed to
an image over `Finset.univ : Finset (Fin k)`. -/
theorem cnxControls_eq_image_castSucc (k : ℕ) :
    cnxControls k = Finset.univ.image Fin.castSucc := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_cnxControls]
  constructor
  · intro hj; exact ⟨⟨(j : ℕ), hj⟩, by ext; simp⟩
  · rintro ⟨i, rfl⟩; simp only [Fin.val_castSucc]; exact i.isLt

/-- The target wire `Fin.last n` is never one of the controls `cnxControls n` (so the aligned
`Cⁿ(X)` is a genuine `mcNot` with `target ∉ controls`). -/
theorem last_notMem_cnxControls (n : ℕ) : Fin.last n ∉ cnxControls n := by
  induction n with
  | zero => simp [cnxControls]
  | succ n ih =>
    simp only [cnxControls, Finset.mem_insert, Finset.mem_image, not_or]
    refine ⟨Fin.last_pos.ne', ?_⟩
    rintro ⟨j, hj, hji⟩
    exact ih (by simpa using (Fin.succ_injective _ (hji.trans (Fin.succ_last n).symm)) ▸ hj)

/-- The control bit of the `(n+1)`-control set factors through the outermost control `0` and the
`n`-control set on the shifted wires: every wire in `cnxControls (n+1)` is set iff wire `0` is set
and every wire in `cnxControls n` is set after shifting by `Fin.succ`. -/
theorem ctrlBit_cnxControls_succ (n : ℕ) (b : Fin (n + 2) → Fin 2) :
    ctrlBit (cnxControls (n + 1)) b
      = if b 0 = 1 ∧ ∀ j ∈ cnxControls n, b j.succ = 1 then 1 else 0 := by
  rw [cnxControls, ctrlBit_insert]
  simp only [Finset.forall_mem_image]

/-- **Nielsen & Chuang, Exercise 4.29 (the quantum–classical bridge).** The postulate-grounded
`n`-controlled `NOT` `mcCtrl n pauliXGate` acts on the `(n+1)`-qubit computational basis exactly as
the classical multiply-controlled `NOT` `Concrete.mcNot` with controls the first `n` wires
(`cnxControls n`) and target the last wire (`Fin.last n`):
`Cⁿ(X)|b⟩ = |mcNot (controls) (target) b⟩`. Thus the quantum `Cⁿ(X)` **is** the reversible
bit-string permutation whose `O(n²)` no-work-qubit circuit of Toffoli/`CNOT`/single-qubit gates the
`Concrete/MultiControlledNot*` development exhibits (`exists_mcNotCircuit`,
`mcNotGateBound_isBigO_sq`).

Proof by induction on `n`, peeling one control at a time with `controlledUnitary`'s basis action. -/
theorem mcCtrl_pauliXGate_evolvePure_towerKet (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    (mcCtrl n pauliXGate).evolvePure (towerKet n b)
      = towerKet n (mcNot (cnxControls n) (Fin.last n) b) := by
  induction n with
  | zero =>
    -- Force the register `qtower 0 qubit` to reduce to `qubit` and `mcCtrl 0` to `pauliXGate`.
    change pauliXGate.evolvePure (towerKet 0 b) = towerKet 0 (mcNot (cnxControls 0) (Fin.last 0) b)
    rw [towerKet_zero, pauliXGate_evolvePure_qubitBasis, towerKet_zero]
    -- `ctrlBit ∅ = 1`: the empty-control `NOT` always flips, matching `X|b 0⟩ = |b 0 + 1⟩`, so the
    -- two basis indices agree definitionally.
    congr 1
  | succ n ih =>
    -- Force `qtower (n+1) qubit ≡ qubit ⊗ qtower n qubit` and `mcCtrl (n+1) ≡ C(mcCtrl n)`, so the
    -- control-branch lemmas below match on the `qubit ⊗ _` register. (A bare
    -- `rw [mcCtrl_succ, towerKet_succ]` leaves `evolvePure`'s implicit *system* index as the
    -- unreduced `qtower (n+1) qubit`, so `controlledUnitary_evolvePure_ketOne/ketZero` fail to
    -- match — the displayed goal looks identical because that index is not printed.)
    change (controlledUnitary (mcCtrl n pauliXGate)).evolvePure (towerKet (n + 1) b)
        = towerKet (n + 1) (mcNot (cnxControls (n + 1)) (Fin.last (n + 1)) b)
    rw [towerKet_succ]
    by_cases h0 : b 0 = 1
    · -- Outer control set: the gate recurses on the tail; the `(n+1)`-control `mcNot` collapses to
      -- the `n`-control one on the shifted wires.
      rw [h0, controlledUnitary_evolvePure_ketOne, ih, towerKet_succ]
      have key : mcNot (cnxControls n) (Fin.last n) (fun i => b i.succ)
          = fun i => mcNot (cnxControls (n + 1)) (Fin.last (n + 1)) b i.succ := by
        funext i
        by_cases hi : i = Fin.last n
        · subst hi
          rw [mcNot_apply_self, Fin.succ_last, mcNot_apply_self, ctrlBit_cnxControls_succ, ctrlBit]
          simp only [h0, true_and]
        · have hne : i.succ ≠ Fin.last (n + 1) := by
            rw [← Fin.succ_last]; exact fun h => hi (Fin.succ_injective _ h)
          rw [mcNot_apply_of_ne _ _ _ hi, mcNot_apply_of_ne _ _ _ hne]
      rw [key]
      congr 1
      rw [mcNot_apply_of_ne _ _ _ Fin.last_pos.ne, h0]
    · -- Outer control unset: the gate is the identity, and `mcNot` fixes `b`.
      have h0' : b 0 = 0 := by omega
      rw [h0', controlledUnitary_evolvePure_ketZero]
      have hc : ctrlBit (cnxControls (n + 1)) b = 0 := by
        rw [ctrlBit_cnxControls_succ]; simp [h0']
      rw [mcNot_of_ctrlBit_eq_zero _ _ _ hc, towerKet_succ, h0']

end AxQM
