/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerComposeRight
import AxQM.Core.TensorPowMultiControlledX
import AxQM.Postulates.API.BlockGatePlacement

/-!
# Flattening a `barencoNCircuit` block's register onto the symmetric power (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`), whose distinctive content is
bottoming its internal multiply-controlled `NOT` blocks `Cᵏ(X)` to genuine `Toffoli`s. Each such
block is `mcCtrl k (pauliXGate.onLeft (qtower d qubit))` acting on the control tower
`qtower k (qubit ⊗ qtower d qubit)` — `k` outer control qubits, the `X`-target the head of the
inner `qubit ⊗ (qtower d qubit)`, and `d + 1` idle target-module wires (`M = qtower d qubit`, the
already-peeled controls that this block does not touch, `Exercise4_30.barencoNCircuit`).

The block's reduction is described from opposite ends, but on **different registers**:

* `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower` reads the block's computational-basis
  action on the **tower** `qtower k (qubit ⊗ qtower d qubit)`, on inputs
  `ctrlTower k c (|i⟩ ⊗ towerKet d e)` (controls `c`, target `i`, idle module `e`);
* `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` exhibits the bounded `O(k²)` `Toffoli`
  circuit for `(tensorPowMcCtrlX k).onBlock (d+1)` on the **flattened symmetric register**
  `qubit ^⊗ₛ (k + 1 + (d + 1))`.

The isomorphism `qtowerComposeRight` pulls the idle module out of the tower,
`qtower k (qubit ⊗ M) ≃ₛ (qtower k qubit) ⊗ M`. This file composes it with the
`qtower ↔ tensor-power` bridge `qtowerQubitTensorPow` on each factor and the block-split
`QSystem.tensorPowAdd` to land exactly on the flattened register
`qubit ^⊗ₛ (k + 1 + (d + 1))` of `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`, and reads off the
induced computational dictionary. Matching the block's tower truth table
(`mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower`) to the flattened circuit across this bridge
gives the per-block `Toffoli` reduction, an `Evolution`-level equality by computational-basis
extensionality.

## What is formalised

* `barencoBlockFlatten k d` — the **block-flattening bridge**
  `qtower k (qubit ⊗ qtower d qubit) ≃ₛ qubit ^⊗ₛ (k + 1 + (d + 1))`, the three-step composite
  `(qtowerComposeRight k).trans ((qtowerQubitTensorPow k).tmul (qtowerQubitTensorPow d)) |>.trans
  (tensorPowAdd qubit (k+1) (d+1)).symm`: factor the idle module out of the tower, flatten each
  `qtower` factor to its symmetric power, then merge the two symmetric powers into one. The block's
  `k` controls and its `X`-target become the leading `k + 1` wires; the `d + 1` idle module wires
  the trailing block — exactly the shape `(tensorPowMcCtrlX k).onBlock (d + 1)` acts on.
* `barencoBlockFlatten_congr_ctrlTower` — the **basis dictionary**: the bridge carries a block tower
  input `ctrlTower k c (|i⟩ ⊗ towerKet d e)` (controls `c`, target `i`, idle module bits `e`) to the
  symmetric product basis state over the concatenated bit-string `Fin.append (Fin.snoc c i) e`:
  `barencoBlockFlatten k d (ctrlTower k c (|i⟩ ⊗ towerKet d e))`
  ` = ⨂_w |Fin.append (Fin.snoc c i) e w⟩`.
  So the `k + 1 + (d + 1)` wires of the flattened register carry, in order, the controls `c`, the
  target `i`, and the idle module `e` — the correspondence on which the block reduction is read.
* `barencoBlockFlatten_symm_congr_piTensor` — the **backward** dictionary (its `.symm` companion via
  `PureState.congr_symm_congr`), used when a gate computed on the flattened register is transported
  back onto the block's tower.

Supporting fact:

* `ctrlTower_qubitBasis_eq_towerKet` — a control tower over a single target basis vector is a
  computational tower ket, `ctrlTower k c |i⟩ = towerKet k (Fin.snoc c i)`.

The general transport lemmas the dictionary chains through — `PureState.congr_trans` /
`PureState.congr_tmul` (functoriality of `PureState.congr` in `Iso.trans` / `Iso.tmul`) and
`QSystem.tensorPowAdd_symm_congr_piTensor` (the backward block-split product dictionary,
`(tensorPowAdd S a b).symm ((⨂ P) ⊗ (⨂ Q)) = ⨂ (Fin.append P Q)`) — are in
`AxQM/Postulates/API/` (`SystemIsoComm` beside `PureState.congr_symm_congr`, and
`BlockGatePlacement` beside the forward `QSystem.tensorPowAdd_congr_piTensor`).

## Design notes

* **Why this exact three-step composite.** The block lives on the right-nested tower
  `qtower k (qubit ⊗ qtower d qubit)` while the `O(k²)` `Toffoli` circuit lives on the symmetric
  register `qubit ^⊗ₛ (k + 1 + (d + 1))`, split as `(k+1) + (d+1)` by `onBlock (d+1)`.
  `qtowerComposeRight` first isolates the idle module as a right factor, so the remaining tower over
  the controls-and-target and the tower over the idle module can each be flattened by the
  bridge `qtowerQubitTensorPow`; `tensorPowAdd` then fuses the two flat powers into one at the
  `(k+1) + (d+1)` split point. Every leg is an existing isomorphism.
* **Why the dictionary chains cleanly.** With `PureState.congr_trans`/`_tmul` the transport of the
  composite factors through each sub-dictionary (`qtowerComposeRight_congr_ctrlTower`,
  `qtowerQubitTensorPow_congr_towerKet` twice, and the backward `tensorPowAdd` product dictionary)
  reduces the proof to a `Fin.append` bookkeeping on the final bit-string.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### `ctrlTower` over a single target basis vector as a `towerKet` -/

/-- **A control tower over a single target basis vector is a computational tower ket.**
`ctrlTower k c |i⟩ = towerKet k (Fin.snoc c i)`: prepending `k` control qubits
`|c 0⟩ ⊗ … ⊗ |c (k-1)⟩` to the target `|i⟩` yields the `(k+1)`-qubit computational basis state whose
wires are the controls `c` followed by the target `i`. Proved by induction on `k`: the head control
peels off through `towerKet_succ`, using `Fin.snoc_apply_zero` for the head wire and a per-wire
`Fin.lastCases` for the shifted tail `(Fin.snoc c i) ∘ Fin.succ = Fin.snoc (tail c) i`. -/
theorem ctrlTower_qubitBasis_eq_towerKet (k : ℕ) (c : Fin k → Fin 2) (i : Fin 2) :
    ctrlTower k c (qubitBasis i) = towerKet k (Fin.snoc c i) := by
  induction k with
  | zero =>
    rw [ctrlTower_zero, towerKet_zero]
    rfl
  | succ k ih =>
    rw [ctrlTower_succ, ih (fun j => c j.succ), towerKet_succ, Fin.snoc_apply_zero]
    congr 2
    funext j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]

/-! ### The block-register flattening bridge -/

/-- **The `barencoNCircuit`-block flattening bridge**
`qtower k (qubit ⊗ qtower d qubit) ≃ₛ qubit ^⊗ₛ (k + 1 + (d + 1))`: the system isomorphism carrying
one internal `Cᵏ(X)` block's control-tower register onto the flattened symmetric register its
bounded `Toffoli` circuit lives on (`tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`). Built as the
three-step composite — factor the idle target module out of the tower (`qtowerComposeRight k`),
flatten each `qtower` factor to its symmetric power (`qtowerQubitTensorPow`, tensored), then merge
the two symmetric powers into one at the `(k+1) + (d+1)` split (`QSystem.tensorPowAdd`). Its basis
action is `barencoBlockFlatten_congr_ctrlTower`. -/
def barencoBlockFlatten (k d : ℕ) :
    (qtower k (qubit ⊗ qtower d qubit)).Iso (qubit ^⊗ₛ (k + 1 + (d + 1))) :=
  ((qtowerComposeRight (S := qubit) (M := qtower d qubit) k).trans
      (QSystem.Iso.tmul (qtowerQubitTensorPow k) (qtowerQubitTensorPow d))).trans
    (QSystem.tensorPowAdd qubit (k + 1) (d + 1)).symm

/-- **Basis dictionary for the block-flattening bridge.** The bridge
`barencoBlockFlatten k d` carries a block control-tower input — `k` control qubits `c`, one target
`|i⟩`, and an idle module state `towerKet d e` — to the symmetric product basis state over the
concatenated bit-string `Fin.append (Fin.snoc c i) e`:

`barencoBlockFlatten k d (ctrlTower k c (|i⟩ ⊗ towerKet d e))`
`  = ⨂_w |Fin.append (Fin.snoc c i) e w⟩`.

So the flattened register's `k + 1 + (d + 1)` wires carry, in order, the block's controls `c`, its
target `i`, and the idle module bits `e` — the correspondence on which the per-block `Toffoli`
reduction (matching the tower action of `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower` to the
flattened circuit of `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`) is read. Proved by
chaining the three factors' dictionaries through `PureState.congr_trans`/`_tmul`
(`qtowerComposeRight_congr_ctrlTower`, `qtowerQubitTensorPow_congr_towerKet` on each factor via
`ctrlTower_qubitBasis_eq_towerKet`, and the backward `QSystem.tensorPowAdd_symm_congr_piTensor`),
closing on a `Fin.append` bit-string bookkeeping. -/
theorem barencoBlockFlatten_congr_ctrlTower (k d : ℕ) (c : Fin k → Fin 2) (i : Fin 2)
    (e : Fin (d + 1) → Fin 2) :
    PureState.congr (barencoBlockFlatten k d)
        (ctrlTower k c ((qubitBasis i).tmul (towerKet d e)))
      = PureState.piTensor (fun w => qubitBasis (Fin.append (Fin.snoc c i) e w)) := by
  rw [barencoBlockFlatten, PureState.congr_trans, PureState.congr_trans,
    qtowerComposeRight_congr_ctrlTower, PureState.congr_tmul,
    ctrlTower_qubitBasis_eq_towerKet, qtowerQubitTensorPow_congr_towerKet,
    qtowerQubitTensorPow_congr_towerKet, QSystem.tensorPowAdd_symm_congr_piTensor]
  refine congrArg PureState.piTensor (funext fun w => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) w
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-- **Backward basis dictionary for the block-flattening bridge.** The *inverse* bridge
`(barencoBlockFlatten k d).symm` folds the symmetric product state over
`Fin.append (Fin.snoc c i) e`
back into the block control-tower input `ctrlTower k c (|i⟩ ⊗ towerKet d e)` — the direction used
when a gate computed on the flattened register (the `Toffoli` circuit of
`tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`) is transported back onto the block's tower. The
`.symm` companion of `barencoBlockFlatten_congr_ctrlTower` via
`PureState.congr_symm_congr`. -/
theorem barencoBlockFlatten_symm_congr_piTensor (k d : ℕ) (c : Fin k → Fin 2) (i : Fin 2)
    (e : Fin (d + 1) → Fin 2) :
    PureState.congr (barencoBlockFlatten k d).symm
        (PureState.piTensor (fun w => qubitBasis (Fin.append (Fin.snoc c i) e w)))
      = ctrlTower k c ((qubitBasis i).tmul (towerKet d e)) := by
  rw [← barencoBlockFlatten_congr_ctrlTower, PureState.congr_symm_congr]

end AxQM
