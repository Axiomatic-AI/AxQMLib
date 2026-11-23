/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportMeasurement
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.Associator

/-!
# AxQM.Postulates.API — the gate-teleportation `CNOT` channel with an external reference

The gate-teleportation gadget of Nielsen & Chuang **Problem 4.6** (`GateTeleport{Measurement,
Correction,Channel}.lean`) implements `CNOT` on a *standalone* two-qubit input `ψ`.  For the
**universality** conclusion — that the resource set is universal on **every** register — one must
run the gadget on two *wires* of a larger `n`-qubit register, wires that are generally **entangled
with the other wires**.  That is the induced-operation-tensors-with-identity step: the gadget acts
on its two input wires and identity on everything else, correctly *even when the input is entangled
with a reference system* `R`.

This file threads an arbitrary reference system `R` through the *vector* core of the gadget — the
first, foundational step of that lift.  The two enabling facts are structural: the reduction-core
identity `cnotGateTeleportation_identity_general` is **linear** in the input, and the Bell-collapse
map is (up to the `¼` amplitude) an **isometry**, so both tensor cleanly with the identity on `R`.

## What is formalised

* `gateTeleportRegisterGenRef R Ψ` — the protocol register for an input pure state `Ψ` of the
  composite `R ⊗ (qubit ⊗ qubit)` (the two `CNOT` input wires together with an arbitrary reference
  `R`): the input beside the four-qubit resource `|χ⟩`, reshaped so that `R` rides on the left and
  the six-qubit gate-teleportation register sits on the right, ready for the two Bell measurements.
  With `R` trivial this is `gateTeleportRegisterGen`; the point is that `Ψ` may be **entangled**
  across `R` and the two input wires.

* `gateTeleportBranch p q` — the single Bell branch `|β_p⟩ ⊗ |β_q⟩ ⊗ (correction · CNOT ·)` of the
  collapse identity, as a continuous linear map of the two-qubit input; the `¼`-free content of
  `bellPairsMeasurement_op_gateTeleportRegisterGen`, packaged so it can be tensored with `1_R`
  (`TensorProduct.mapL 1 ·`).  `gateTeleportBranch_apply` unfolds its action.

* `bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef` — **the reference-generalised
  collapse identity**: measuring the two Bell pairs (embedded on the right of `R` via
  `Measurement.onRight`) sends the reference register to `¼ (1_R ⊗ gateTeleportBranch p q)(Ψ)`.
  Because the collapse is linear in `Ψ` and the branch tensors with `1_R`, the identity holds for a
  `Ψ` **entangled with the reference** `R` — exactly what an embedded `CNOT` on two wires of a
  larger register requires.  Proved by bundling both sides as linear maps in `Ψ.vec` and checking on
  the product vectors (which span, `TensorProduct.ext'`), where it is the raw-vector collapse
  `bellPairsMeasurement_op_reshape_tmul` (the `PureState`-wrapper-free form of
  `bellPairsMeasurement_op_gateTeleportRegisterGen`, stated beside the collapse family in
  `AxQM/Postulates/API/GateTeleportMeasurement.lean`).

This is one step toward Problem 4.6's register-general universality; the `State`-level
induced-operation reading (measure → correct → trace-out gives `(cnotGate.onRight R)` on the input)
is in `AxQM/Postulates/API/GateTeleportChannelRefMarginal.lean`, using the norm and correction
generalised the same way.
-/

open scoped TensorProduct

namespace AxQM

set_option maxHeartbeats 1000000 in
-- Elaboration of the reference-augmented reshape over the seven-way composite (`R` beside
-- the six-qubit register) is defeq-heavy; the default heartbeat budget is insufficient.
/-- **The gate-teleportation protocol register with an external reference** `R`.  For an input pure
state `Ψ` of `R ⊗ (qubit ⊗ qubit)` — the two `CNOT` input wires together with an arbitrary reference
`R` they may be entangled with — this is the input beside the four-qubit resource `|χ⟩`
(`cnotGateTeleportResource`), transported so that `R` rides on the left and the six-qubit
gate-teleportation register (two measured pairs on the left, the two output halves on the right)
sits on the right.  The reshape is `(assoc)⁻¹` (peel `R` off the input) followed by
`1_R ⊗ gateTeleportProtocolReshape` (reshape the six-qubit part exactly as
`gateTeleportRegisterGen`).  With `R` the trivial system this is `gateTeleportRegisterGen`; the
added generality is that `Ψ` may be entangled across `R` and the two input wires. -/
noncomputable def gateTeleportRegisterGenRef (R : QSystem)
    (Ψ : PureState (R ⊗ (qubit ⊗ qubit))) :
    PureState (R.compose (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit))) :=
  PureState.congr
    ((R.assoc (qubit ⊗ qubit) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).symm.trans
      ((QSystem.Iso.refl R).tmul gateTeleportProtocolReshape))
    (Ψ.tmul cnotGateTeleportResource)

set_option maxHeartbeats 1000000 in
-- The composite-iso `toIsometry` unfolding over the seven-way composite exceeds the default budget.
/-- **The reference reshape on a product input.**  The reference-augmented protocol reshape
`(assoc)⁻¹ ∘ (1_R ⊗ gateTeleportProtocolReshape)` sends the product vector `(r ⊗ v) ⊗ |χ⟩` to
`r ⊗ reshape (v ⊗ |χ⟩)` — `r` rides through on the left, the six-qubit part is reshaped by
`gateTeleportProtocolReshape`.  This is the pure-tensor action underlying
`gateTeleportRegisterGenRef` and the spanning-vector step of the reference collapse. -/
theorem gateTeleportRegisterGenRef_reshape_tmul (R : QSystem) (r : R.space)
    (v : (qubit ⊗ qubit).space) :
    ((R.assoc (qubit ⊗ qubit) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).symm.trans
        ((QSystem.Iso.refl R).tmul gateTeleportProtocolReshape)).toIsometry
        ((r ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] cnotGateTeleportResource.vec)
      = r ⊗ₜ[ℂ] gateTeleportProtocolReshape.toIsometry
          (v ⊗ₜ[ℂ] cnotGateTeleportResource.vec) := by
  erw [QSystem.Iso.trans_toIsometry, LinearIsometryEquiv.trans_apply,
    assoc_symm_toIsometry_tmul_tmul, QSystem.Iso.tmul_toIsometry]
  erw [TensorProduct.congrIsometry_tmul]; rfl

set_option maxHeartbeats 1000000 in
-- Building the branch as a `→L[ℂ]` over the six-qubit composite system is defeq-heavy.
/-- **The single Bell branch of the gate-teleportation collapse, as a continuous linear map** of the
two-qubit input.  For outcome `(p, q)` it is `v ↦ |β_p⟩ ⊗ |β_q⟩ ⊗ ((C_A ⊗ C_B)(CNOT v))`, with the
outcome-determined single-qubit Pauli corrections `C_A = pauliByproduct (p.1+q.1) p.2`,
`C_B = pauliByproduct q.1 (p.2+q.2)` — the `¼`-free content of
`bellPairsMeasurement_op_gateTeleportRegisterGen`, packaged as a `→L[ℂ]` so it can be tensored with
the identity on a reference system (`TensorProduct.mapL 1 ·`). -/
noncomputable def gateTeleportBranch (p q : Fin 2 × Fin 2) :
    (qubit ⊗ qubit).space →L[ℂ]
      (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)).space :=
  (TensorProduct.mk ℂ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space (qubit ⊗ qubit).space
        (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2)).toContinuousLinearMap.comp
    ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op.comp cnotGate.op)

/-- The action of `gateTeleportBranch p q` on an input vector `v`:
`|β_p⟩ ⊗ |β_q⟩ ⊗ ((C_A ⊗ C_B)(CNOT v))`. -/
theorem gateTeleportBranch_apply (p q : Fin 2 × Fin 2) (v : (qubit ⊗ qubit).space) :
    gateTeleportBranch p q v
      = (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
          ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
            (cnotGate.op v)) :=
  rfl

set_option maxHeartbeats 1000000 in
-- The `ext'` reduction over the reference-tensored composite exceeds the default budget.
/-- **The reference-generalised collapse identity** (Nielsen & Chuang Problem 4.6, the
induced-operation-tensors-with-identity core).  Bell-measuring the two co-located pairs of the
reference register `gateTeleportRegisterGenRef R Ψ` — the measurement embedded on the right of `R`
via `Measurement.onRight` — sends it, for outcome `(p, q)`, to
`¼ (1_R ⊗ gateTeleportBranch p q)(Ψ)`.  Since the collapse is `ℂ`-linear in `Ψ` and the branch
`gateTeleportBranch p q` tensors with the identity on `R`, this holds for an input `Ψ` **entangled
with the reference** `R` — the fact an embedded `CNOT` on two wires of a larger register needs, its
input generally entangled with the remaining wires.

Proof: bundle both sides as linear maps in `Ψ.vec` and check on the product vectors `r ⊗ v` (which
span, `TensorProduct.ext'`); there `Measurement.onRight_op_tmul` peels off `r` and the raw-vector
collapse `bellPairsMeasurement_op_reshape_tmul` computes the six-qubit factor. -/
theorem bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef (R : QSystem)
    (Ψ : PureState (R ⊗ (qubit ⊗ qubit))) (p q : Fin 2 × Fin 2) :
    ((bellPairsMeasurement.onRight R).op (p, q)) (gateTeleportRegisterGenRef R Ψ).vec
      = (4 : ℂ)⁻¹ •
          (TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportBranch p q)) Ψ.vec := by
  rw [gateTeleportRegisterGenRef, PureState.congr_vec, PureState.tmul_vec]
  suffices h : (((bellPairsMeasurement.onRight R).op (p, q)).toLinearMap ∘ₗ
      (((R.assoc (qubit ⊗ qubit) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).symm.trans
        ((QSystem.Iso.refl R).tmul
          gateTeleportProtocolReshape)).toIsometry.toLinearEquiv.toLinearMap ∘ₗ
        ((TensorProduct.mk ℂ (R ⊗ (qubit ⊗ qubit)).space
          ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space).flip cnotGateTeleportResource.vec)))
      = ((4 : ℂ)⁻¹ • (TensorProduct.mapL (1 : R.space →L[ℂ] R.space)
          (gateTeleportBranch p q)).toLinearMap) by
    -- Every step from `h` to the goal (`comp_apply`, `flip_apply`, `mk_apply`, `smul_apply`) is
    -- definitional; `simpa` cannot see through the bundled composite spaces, `exact` can.
    exact LinearMap.congr_fun h Ψ.vec
  refine TensorProduct.ext' (fun r v => ?_)
  change ((bellPairsMeasurement.onRight R).op (p, q))
      (((R.assoc (qubit ⊗ qubit) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).symm.trans
        ((QSystem.Iso.refl R).tmul gateTeleportProtocolReshape)).toIsometry
          ((r ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] cnotGateTeleportResource.vec))
      = (4 : ℂ)⁻¹ • (TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportBranch p q))
          (r ⊗ₜ[ℂ] v)
  rw [gateTeleportRegisterGenRef_reshape_tmul, Measurement.onRight_op_tmul,
    bellPairsMeasurement_op_reshape_tmul, TensorProduct.mapL_tmul,
    one_apply_eq_self, gateTeleportBranch_apply]
  erw [TensorProduct.tmul_smul]

end AxQM
