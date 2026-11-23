/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliGateTeleport
import AxQM.Postulates.API.ToffoliAncilla
import AxQM.Postulates.API.Interchange

/-!
# AxQM.Postulates.API — the Toffoli gate-teleportation reshape (N&C Exercise 10.68)

The **register reshape** connecting the physical layout of the fault-tolerant Toffoli circuit of
Nielsen & Chuang Exercise 10.68 (the ancilla block prepared offline beside the data block) to the
*coupled-pairs* register on which the data↔ancilla coupling `toffoliTeleportCoupling` acts. It is
the Toffoli analogue of the CNOT gate-teleportation reshape `gateTeleportProtocolReshape`
(Problem 4.6).

## Role in Exercise 10.68

After "moving the final Toffoli all the way back to the left side" (part (2)), the ancilla block is
prepared offline in the AND-magic resource state `toffoliAncilla = |Θ_T⟩ = ½ Σ_{a,b} |a, b, a·b⟩`
(the leftmost dotted box) and sits *beside* the data `|xyz⟩`: the physical register is
`(a₁ ⊗ (a₂ ⊗ a₃)) ⊗ (x ⊗ (y ⊗ z))` — ancilla block on the left, data block on the right. The three
data↔ancilla coupling `CNOT`s of the Figure, however, each act on an *ancilla–data pair* `(aᵢ, dᵢ)`,
one from each block; to place them as ordinary two-qubit gates the register must be **regrouped so
each ancilla qubit sits beside its data partner**, `(a₁ ⊗ x) ⊗ ((a₂ ⊗ y) ⊗ (a₃ ⊗ z))` — exactly
the coupled-pairs register of `toffoliTeleportCoupling`. That regrouping is
`toffoliTeleportReshape`, and applied to the resource-consuming input `|Θ_T⟩ ⊗ |xyz⟩` it produces
the vector
`toffoliTeleportReshapedInput` that the coupling then transforms into the pre-measurement
gate-teleportation state.

## What is formalised

* `toffoliTeleportReshape` — the reshape system isomorphism
  `(qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit)) ≃ₛ
     (qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))` interleaving the ancilla and data
  three-qubit blocks into the three coupled pairs. Assembled from the transport backbone only: an
  outer `QSystem.Iso.interchange` pulls the two head qubits `(a₁, x)` together into the first pair
  and leaves the two tails `(a₂ ⊗ a₃)`, `(y ⊗ z)` blocked on the right, and an inner
  `QSystem.Iso.interchange` (under `QSystem.Iso.tmul` a `refl`) interleaves those tails into the
  second and third pairs.
* `toffoliTeleportReshape_toIsometry_tmul` — its pure-tensor action
  `(a₁ ⊗ (a₂ ⊗ a₃)) ⊗ (x ⊗ (y ⊗ z)) ↦ (a₁ ⊗ x) ⊗ ((a₂ ⊗ y) ⊗ (a₃ ⊗ z))`.
* `toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul` — **the reshape realises
  `toffoliTeleportReshapedInput`**:
  `toffoliTeleportReshape (|Θ_T⟩ ⊗ |xyz⟩) = ½ Σ_{a,b} |a, x⟩ |b, y⟩ |a·b, z⟩`. This is the
  key identity — it identifies the coupling's abstract input `toffoliTeleportReshapedInput`
  with the honest reshape of the offline resource `toffoliAncilla` tensored with the data `|xyz⟩`,
  so the pre-measurement state `toffoliTeleportCoupling_op_toffoliTeleportReshapedInput` is
  genuinely the output of coupling the *prepared* resource to the data.

## Design notes

* **Interleave, don't re-bracket.** `QSystem.assoc`/`QSystem.Iso.tmul` only re-bracket a fixed
  order; the reshape must *interleave* two blocks, so it is built from `QSystem.Iso.interchange`
  (which swaps the two interior factors of a fourfold composite) — twice, exactly as
  `gateTeleportProtocolReshape` does for the two-pair CNOT case. The pure-tensor action is then the
  chain of the two `interchange_toIsometry_tmul_tmul` action lemmas with a `refl` on the untouched
  first pair.
* **Sum form of the ancilla.** The realisation lemma consumes `toffoliAncilla_vec_sum`
  (`|Θ_T⟩ = ½ Σ_{a,b} |a, b, a·b⟩`), so the reshape distributes through the double sum by linearity
  (`map_smul`/`map_sum`, `TensorProduct.sum_tmul`/`smul_tmul'`) and each branch reduces by the
  pure-tensor action to the matching branch of `toffoliTeleportReshapedInput` — the summation index
  `(a, b)` is preserved as the branch label the data measurements will read out.

The statement of Exercise 10.68 is in `AxQM/NC/Ch10/Exercise10_68_FTToffoli.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

set_option maxHeartbeats 1000000 in
-- The type-check of this nested composite of transport-backbone isos over the 64-dimensional
-- register exceeds the default heartbeat budget; the elaboration is pure `QSystem.Iso` data.
/-- **The Toffoli gate-teleportation reshape** (Nielsen & Chuang, Exercise 10.68 part (2)): the
system isomorphism
`(qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit)) ≃ₛ
   (qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))` that interleaves the offline **ancilla
block** `a₁ ⊗ (a₂ ⊗ a₃)` and the **data block** `x ⊗ (y ⊗ z)` — laid side by side in the physical
register — into the three coupled ancilla–data pairs `(a₁ ⊗ x)`, `(a₂ ⊗ y)`, `(a₃ ⊗ z)` on which the
coupling `toffoliTeleportCoupling` acts. Built from the transport backbone: an outer
`QSystem.Iso.interchange` pairs the two head qubits `(a₁, x)` and blocks the tails
`(a₂ ⊗ a₃) ⊗ (y ⊗ z)` on the right, then an inner `QSystem.Iso.interchange` (kept off the first pair
by `QSystem.Iso.tmul (QSystem.Iso.refl _)`) interleaves those tails into `(a₂ ⊗ y) ⊗ (a₃ ⊗ z)`.
Applied to `toffoliAncilla ⊗ |xyz⟩` it yields `toffoliTeleportReshapedInput`
(`toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul`). -/
def toffoliTeleportReshape :
    ((qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit)))
      ≃ₛ ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  (QSystem.Iso.interchange qubit (qubit ⊗ qubit) qubit (qubit ⊗ qubit)).trans
    (QSystem.Iso.tmul (QSystem.Iso.refl (qubit ⊗ qubit))
      (QSystem.Iso.interchange qubit qubit qubit qubit))

set_option maxHeartbeats 800000 in
-- The reshape's `.toIsometry` on the 64-dimensional register exceeds the default heartbeat budget.
/-- **Pure-tensor action of the Toffoli-teleportation reshape**:
`toffoliTeleportReshape ((a₁ ⊗ (a₂ ⊗ a₃)) ⊗ (x ⊗ (y ⊗ z))) = (a₁ ⊗ x) ⊗ ((a₂ ⊗ y) ⊗ (a₃ ⊗ z))`.
Each ancilla qubit `aᵢ` is brought beside its data partner `dᵢ`. Proved by unfolding the reshape and
firing the outer `interchange` action lemma (`interchange_toIsometry_tmul_tmul`), then — under the
`tmul`/`refl` — the inner one, with `refl` leaving the already-formed first pair `(a₁ ⊗ x)`
untouched. -/
theorem toffoliTeleportReshape_toIsometry_tmul (a₁ a₂ a₃ x y z : qubit.space) :
    toffoliTeleportReshape.toIsometry
        ((a₁ ⊗ₜ[ℂ] (a₂ ⊗ₜ[ℂ] a₃)) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)))
      = (a₁ ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] ((a₂ ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a₃ ⊗ₜ[ℂ] z)) := by
  erw [toffoliTeleportReshape, QSystem.Iso.trans_toIsometry, LinearIsometryEquiv.trans_apply,
    QSystem.Iso.interchange_toIsometry_tmul_tmul]
  rfl

set_option maxHeartbeats 800000 in
-- Reducing the reshape over the double sum on the 64-dimensional register exceeds the default.
/-- **The reshape realises `toffoliTeleportReshapedInput`** (Nielsen & Chuang, Exercise 10.68 part
(2)): reshaping the offline resource `toffoliAncilla` tensored with the data `|xyz⟩`
gives exactly the coupling's abstract input,

  `toffoliTeleportReshape (|Θ_T⟩ ⊗ |xyz⟩) = ½ Σ_{a,b} |a, x⟩ |b, y⟩ |a·b, z⟩`
    (`= toffoliTeleportReshapedInput x y z`).

Together with `toffoliTeleportCoupling_op_toffoliTeleportReshapedInput` this shows the
pre-measurement gate-teleportation state is genuinely produced by coupling the *prepared* resource
to the data. Proved by expanding `|Θ_T⟩ ⊗ |xyz⟩` in the AND-magic sum form
(`toffoliAncilla_vec_sum`, `PureState.tmul_vec`), distributing the reshape through the scalar and
the double sum
(`TensorProduct.smul_tmul'`/`sum_tmul`, `map_smul`/`map_sum`), and reducing each branch by the
pure-tensor action `toffoliTeleportReshape_toIsometry_tmul` to the matching branch of
`toffoliTeleportReshapedInput`. -/
theorem toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul (x y z : Fin 2) :
    toffoliTeleportReshape.toIsometry (toffoliAncilla.tmul (qubitThreeBasis (x, y, z))).vec
      = toffoliTeleportReshapedInput x y z := by
  rw [PureState.tmul_vec, toffoliAncilla_vec_sum, ← TensorProduct.smul_tmul']
  simp only [TensorProduct.sum_tmul, toffoliTeleportReshapedInput]
  refine (map_smul _ _ _).trans ?_
  refine congrArg _ ?_
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun a _ => ?_)
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun b _ => ?_)
  exact toffoliTeleportReshape_toIsometry_tmul _ _ _ _ _ _

end AxQM
