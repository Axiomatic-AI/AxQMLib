/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.BarencoBlockFlatten
import AxQM.Core.McNotCircuitDecomposition

/-!
# A `barencoNCircuit` internal `Cᵏ(X)` block is a bounded Toffoli circuit on its tower register
(N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`), whose distinctive content is
bottoming its internal multiply-controlled `NOT` blocks `Cᵏ(X)` to genuine `Toffoli`s. Each such
block is `mcCtrl k (pauliXGate.onLeft (qtower d qubit))` acting on the control tower
`qtower k (qubit ⊗ qtower d qubit)` — `k` outer control qubits, the `X`-target the head of the inner
`qubit ⊗ (qtower d qubit)`, and `d + 1` idle target-module wires.

Three results describe the reduction of one such block, but on **different registers** and only
up to a register bridge:

* `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower` reads the block's computational-basis
  action on the **tower** `qtower k (qubit ⊗ qtower d qubit)`;
* `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` exhibits the bounded `O(k²)` `Toffoli`
  circuit for `(tensorPowMcCtrlX k).onBlock (d+1)` on the **flattened** register
  `qubit ^⊗ₛ (k + 1 + (d + 1))`;
* `barencoBlockFlatten` is the isomorphism `qtower k (qubit ⊗ qtower d qubit) ≃ₛ
  qubit ^⊗ₛ (k + 1 + (d + 1))` bridging the two, with its basis dictionary
  `barencoBlockFlatten_congr_ctrlTower`.

This file makes the reduction an honest `Evolution` identity, matching the tower truth table of
`mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower` to the flattened circuit of
`tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` across the bridge `barencoBlockFlatten` by
computational-basis extensionality (`Evolution.ext_qubitBasis`).

## What is formalised

* `barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft` — the **transport identity**: carrying the
  block through the flattening bridge lands exactly on the contiguous front-block placement,
  `Evolution.congr (barencoBlockFlatten k d) (mcCtrl k (pauliXGate.onLeft (qtower d qubit)))
  = (Evolution.tensorPowMcCtrlX k).onBlock (d + 1)`.
  Both sides act on a computational product state `⨂ᵢ |c i⟩` as the classical multiply-controlled
  `NOT` on the front `k + 1` wires; the left via the block tower truth table
  (`mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower`) read through the bridge dictionary
  (`barencoBlockFlatten_congr_ctrlTower`), the right via the flattened block truth table
  (`tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis`).
* `mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit` — the **per-block reduction on the tower**: the block
  `mcCtrl k (pauliXGate.onLeft (qtower d qubit))`, *on its own control-tower register*, **is** a
  genuine circuit `U` of `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) of `O(k²)` count, transported
  back onto that register through the flattening bridge:
  `mcCtrl k (pauliXGate.onLeft (qtower d qubit))
  = Evolution.congr (barencoBlockFlatten k d).symm U`.
  Combines the transport identity with the circuit of
  `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` (`= U`) and the gate-transport roundtrip
  `Evolution.congr_symm_congr`. This is the per-block decomposition by which every internal `Cᵏ(X)`
  block of the no-work-qubit `Cⁿ(X)` circuit is replaced; summed over the `O(n)` blocks it is the
  exercise's `O(n²)` gate count.

## The proof of the transport identity

`Evolution.ext_qubitBasis` reduces the identity to agreement on every computational product basis
state `⨂ᵢ |c i⟩` of the flattened register `qubit ^⊗ₛ (k + 1 + (d + 1))`. Any such bit-string `c`
splits as `Fin.append (Fin.snoc ctrl tgt) mod` — the front `k` control wires `ctrl`, the target wire
`tgt`, and the trailing `d + 1` idle module wires `mod`. On that input:

* the **left** side, transported, is computed by the transport law
  `Evolution.congr_evolvePure_congr`
  and the bridge dictionary `barencoBlockFlatten_congr_ctrlTower` (both directions): it feeds the
  input back to the tower state `ctrlTower k ctrl (|tgt⟩ ⊗ towerKet d mod)`, applies the block truth
  table `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower` flipping the target
  `tgt ↦ tgt + [∀ j, ctrl j = 1]`, and folds the result forward
  to `⨂ᵢ |Fin.append (Fin.snoc ctrl (tgt + …)) mod i⟩`;
* the **right** side is the flattened block truth table
  `tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis`,
  `⨂ᵢ |mcNot (front controls) (front target) c i⟩`.

The two land on the same bit-string: `Concrete.ctrlBit` of the front control image equals the tower
guard `∀ j, ctrl j = 1` (`Concrete.ctrlBit_image` + `cnxControls_eq_image_castSucc` +
`Fin.snoc_castSucc`), and `mcNot` flips exactly the target wire, matching the `Fin.snoc` update.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **N&C Exercise 4.29: a `barencoNCircuit` block flattens onto
its front-block placement.** Carrying the internal `Cᵏ(X)` block `mcCtrl k (pauliXGate.onLeft
(qtower d qubit))` — on the control tower `qtower k (qubit ⊗ qtower d qubit)` — through the
block-flattening bridge `barencoBlockFlatten k d` lands exactly on the contiguous
front-block placement `(Evolution.tensorPowMcCtrlX k).onBlock (d + 1)` on the symmetric register
`qubit ^⊗ₛ (k + 1 + (d + 1))` (whose bounded `O(k²)` `Toffoli` circuit
`tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` exhibits):

`Evolution.congr (barencoBlockFlatten k d) (mcCtrl k (pauliXGate.onLeft (qtower d qubit)))
  = (Evolution.tensorPowMcCtrlX k).onBlock (d + 1)`.

Proved by computational-basis extensionality (`Evolution.ext_qubitBasis`): on `⨂ᵢ |c i⟩` (`c` split
into the `k` controls, the target, and the `d + 1` idle module wires) the left side, transported via
`Evolution.congr_evolvePure_congr` and the bridge dictionary `barencoBlockFlatten_congr_ctrlTower`,
is the block tower truth table `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower`, and the right side
is the flattened block truth table `tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis`; both flip the
target wire iff every
control is set. -/
theorem barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft (k d : ℕ) :
    Evolution.congr (barencoBlockFlatten k d) (mcCtrl k (pauliXGate.onLeft (qtower d qubit)))
      = (Evolution.tensorPowMcCtrlX k).onBlock (d + 1) := by
  refine Evolution.ext_qubitBasis fun x => ?_
  -- Split the flattened bit-string `x` into the `k` controls, the target, and the `d+1` idle wires.
  set ctrl : Fin k → Fin 2 := fun j => x (Fin.castAdd (d + 1) j.castSucc) with hctrl
  set tgt : Fin 2 := x (Fin.castAdd (d + 1) (Fin.last k)) with htgt
  set mod : Fin (d + 1) → Fin 2 := fun j => x (Fin.natAdd (k + 1) j) with hmod
  have hx : x = Fin.append (Fin.snoc ctrl tgt) mod := by
    funext w
    refine Fin.addCases (fun j => ?_) (fun j => ?_) w
    · rw [Fin.append_left]
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, htgt]
      | cast j => rw [Fin.snoc_castSucc, hctrl]
    · rw [Fin.append_right, hmod]
  rw [hx]
  -- Right side: the flattened block truth table.
  rw [tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis]
  -- Left side: feed the input to the tower, apply the block truth table, fold back.
  rw [← barencoBlockFlatten_congr_ctrlTower k d ctrl tgt mod, Evolution.congr_evolvePure_congr,
    mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower, barencoBlockFlatten_congr_ctrlTower]
  -- Both sides are `⨂` over a bit-string; reconcile the two front-target flips wire by wire.
  refine congrArg PureState.piTensor (funext fun w => ?_)
  refine congrArg qubitBasis ?_
  -- `ctrlBit` of the front control image is the tower guard `∀ j, ctrl j = 1`.
  have hguard : Concrete.ctrlBit ((cnxControls k).image (Fin.castAdd (d + 1)))
      (Fin.append (Fin.snoc ctrl tgt) mod) = if ∀ j, ctrl j = 1 then (1 : Fin 2) else 0 := by
    rw [Concrete.ctrlBit_image]
    have hpull : (fun j : Fin (k + 1) =>
        Fin.append (Fin.snoc ctrl tgt) mod (Fin.castAdd (d + 1) j)) = Fin.snoc ctrl tgt :=
      funext fun j => Fin.append_left _ _ j
    rw [hpull, Concrete.ctrlBit, cnxControls_eq_image_castSucc]
    simp only [Finset.forall_mem_image, Finset.mem_univ, forall_const, Fin.snoc_castSucc]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) w
  · rw [Fin.append_left]
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Concrete.mcNot_apply_self, hguard, Fin.append_left, Fin.snoc_last]
    | cast j =>
      have hne : Fin.castAdd (d + 1) (Fin.castSucc j)
          ≠ Fin.castAdd (d + 1) (Fin.last k) := by
        simp only [ne_eq, Fin.castAdd_inj]
        exact Fin.castSucc_ne_last j
      rw [Fin.snoc_castSucc, Concrete.mcNot_apply_of_ne _ _ _ hne, Fin.append_left,
        Fin.snoc_castSucc]
  · have hne : Fin.natAdd (k + 1) j ≠ Fin.castAdd (d + 1) (Fin.last k) := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]
      omega
    rw [Fin.append_right, Concrete.mcNot_apply_of_ne _ _ _ hne, Fin.append_right]

/-- **N&C Exercise 4.29: a `barencoNCircuit` block is a bounded
`O(k²)` Toffoli circuit on its tower register.** The internal `Cᵏ(X)` block
`mcCtrl k (pauliXGate.onLeft (qtower d qubit))` — as it sits in `barencoNCircuit` on the control
tower `qtower k (qubit ⊗ qtower d qubit)` — **is**, as an `Evolution`, a genuine circuit `U` of
`≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`, target never a control) with `O(k²)` count, transported
onto that tower register through the flattening bridge:

`mcCtrl k (pauliXGate.onLeft (qtower d qubit)) = Evolution.congr (barencoBlockFlatten k d).symm U`,

where the circuit `gs` satisfies:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — the gate set is `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ Concrete.mcNotGateBound k` — the `O(k²)` gate count
  (`Concrete.mcNotGateBound_isBigO_sq`);
* `U` acts on every computational basis state `|⨂ᵢ c i⟩` as the classical circuit denotation
  `Concrete.mcNotDenote gs`.

This is the per-block decomposition by which every internal `Cᵏ(X)` block (`k < n`, always with the
idle module wires as spare) of the no-work-qubit `Cⁿ(X)` circuit is replaced by. Immediate from the
transport identity `barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft`, the flattened
circuit `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` (`= U`), and the gate-transport roundtrip
`Evolution.congr_symm_congr`. -/
theorem mcCtrl_pauliXGate_onLeft_eq_toffoliCircuit (k d : ℕ) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + (d + 1))))
      (U : Evolution (qubit ^⊗ₛ (k + 1 + (d + 1)))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ Concrete.mcNotGateBound k ∧
      (∀ c : Fin (k + 1 + (d + 1)) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      mcCtrl k (pauliXGate.onLeft (qtower d qubit))
        = Evolution.congr (barencoBlockFlatten k d).symm U := by
  obtain ⟨gs, U, hgs, hlen, hUc, hplaced⟩ :=
    tensorPowMcCtrlX_onBlock_eq_toffoliCircuit (k := k) (b := d + 1) (by omega)
  refine ⟨gs, U, hgs, hlen, hUc, ?_⟩
  rw [← hplaced, ← barencoBlockFlatten_congr_mcCtrl_pauliXGate_onLeft, Evolution.congr_symm_congr]

end AxQM
