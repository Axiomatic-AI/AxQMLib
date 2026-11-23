/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportChannelRef
import AxQM.Postulates.API.GateTeleportCorrection

/-!
# AxQM.Postulates.API — the reference-generalised deterministic `CNOT` collapse

The reference-generalised **collapse** identity
(`bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef`, `GateTeleportChannelRef.lean`) sends
the gate-teleportation register — with the two `CNOT` input wires entangled to an arbitrary
reference system `R` — to `¼ (1_R ⊗ gateTeleportBranch p q)(Ψ)`, where `gateTeleportBranch p q`
carries the two output qubits in `CNOT` up to the outcome-`(p, q)` single-qubit Pauli byproducts.
For the induced **operation** (the channel `measure → correct → trace-out`) one must undo those
byproducts and divide out the branch amplitude — exactly as the standalone development does in
`GateTeleportCorrection.lean` and `GateTeleportChannel.lean`, but now threaded through the reference
`R`.  This file supplies the two facts that step needs, reference-generalised:

## What is formalised

* `gateTeleportBranch_norm` — the branch map `gateTeleportBranch p q` is an **isometry**
  (`‖gateTeleportBranch p q v‖ = ‖v‖`): its output is a unit Bell pair (`bellBasisVec_norm`)
  tensored with the isometric image of `v` under the Paulis and `CNOT` (`Evolution.norm_op_apply`).
  The `¼`-free content of the branch's norm — the fact the reference measurement amplitude rests on.

* `norm_bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef` — **the reference measured
  branch has norm `¼`.**  Since the collapse is `¼ • (1_R ⊗ gateTeleportBranch p q)(Ψ)` and
  `1_R ⊗ (branch)` is an isometry (tensor of isometries, `TensorProduct.norm_map`), the branch has
  norm `¼ ‖Ψ‖ = ¼` — the amplitude normalisation divides out (Born probability `1/16`), holding for
  a `Ψ` entangled with `R`.  In particular it is nonzero, so the branch normalises.

* `gateTeleportCleanBranch p q` — the **correction-free** branch `v ↦ |β_p⟩ ⊗ |β_q⟩ ⊗ (CNOT v)`,
  the outcome-independent target of the correction; `gateTeleportCleanBranch_apply` unfolds it.

* `bellPairsMeasurement_onRight_corrected_op_gateTeleportRegisterGenRef` — **the
  reference-generalised deterministic `CNOT` collapse.**  Bell-measuring the two pairs and applying
  the outcome-determined single-qubit correction (`gateTeleportCorrection p q`, placed on the output
  wires beside `R` and the measured pairs) sends the register to
  `¼ (1_R ⊗ gateTeleportCleanBranch p q)(Ψ)`: the byproducts are undone, so the output factor is a
  clean `CNOT` on the input, **independent of the outcome** and **linear in `Ψ`** (hence correct for
  `Ψ` entangled with `R`).  This is the reference analogue of
  `bellPairsMeasurement_corrected_op_gateTeleportRegisterGen`, and the input to the reference
  channel (normalise + trace out the measured pairs) realising `CNOT` on two wires of a register.

The `State`-level channel reading (`reducedRight` after reshaping gives `cnotGate.onRight R` on the
input) is in `AxQM/Postulates/API/GateTeleportChannelRefMarginal.lean`, built on these two facts.
-/

open scoped TensorProduct

namespace AxQM

open ContinuousLinearMap

/-- **The single Bell branch is an isometry.**  `gateTeleportBranch p q` sends `v` to
`|β_p⟩ ⊗ |β_q⟩ ⊗ ((C_A ⊗ C_B)(CNOT v))`, whose norm is `‖β_p‖ ‖β_q‖ ‖(C_A ⊗ C_B)(CNOT v)‖`; the
Bell vectors are unit (`bellBasisVec_norm`) and the Paulis and `CNOT` are isometric
(`Evolution.norm_op_apply`), so `‖gateTeleportBranch p q v‖ = ‖v‖`.  This is what makes the
reference measured branch have amplitude `¼` independent of any entanglement with the reference. -/
theorem gateTeleportBranch_norm (p q : Fin 2 × Fin 2) (v : (qubit ⊗ qubit).space) :
    ‖gateTeleportBranch p q v‖ = ‖v‖ := by
  rw [gateTeleportBranch_apply]
  erw [TensorProduct.norm_tmul, TensorProduct.norm_tmul]
  rw [bellBasisVec_norm, bellBasisVec_norm, Evolution.norm_op_apply, Evolution.norm_op_apply]
  ring

set_option maxHeartbeats 1000000 in
-- Building the `LinearIsometry` package for the branch and the `TensorProduct.norm_map` defeq check
-- run over the six-qubit composite space; the default heartbeat budget is insufficient.
/-- **Tensoring the branch with the identity on `R` preserves norm.**
`‖(1_R ⊗ gateTeleportBranch p q)(x)‖ = ‖x‖`: the branch is an isometry (`gateTeleportBranch_norm`)
and the identity is an isometry, so their `TensorProduct.map` preserves norm
(`TensorProduct.norm_map`).  The reference-generalised isometry underlying the `¼` amplitude. -/
theorem norm_mapL_one_gateTeleportBranch (R : QSystem) (p q : Fin 2 × Fin 2)
    (x : (R ⊗ (qubit ⊗ qubit)).space) :
    ‖(TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportBranch p q)) x‖ = ‖x‖ := by
  let bᵢ : (qubit ⊗ qubit).space →ₗᵢ[ℂ]
      (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)).space :=
    ⟨(gateTeleportBranch p q).toLinearMap, gateTeleportBranch_norm p q⟩
  erw [TensorProduct.mapL_apply, ContinuousLinearMap.toLinearMap_one]
  exact TensorProduct.norm_map (LinearIsometry.id) bᵢ x

/-- **The reference measured branch has norm `¼`.**  Bell-measuring the two co-located pairs of the
reference register (embedded on the right of `R` via `Measurement.onRight`) sends it to
`¼ (1_R ⊗ gateTeleportBranch p q)(Ψ)` (the reference collapse identity),
a `¼` times a unit vector: `1_R ⊗ (branch)` is an isometry (`norm_mapL_one_gateTeleportBranch`) and
`Ψ` is a unit vector (`PureState.normalized`).  So the branch has norm `¼` — its amplitude, hence
Born probability `1/16` — **independent of `Ψ`'s entanglement with `R`**, and is in particular
nonzero, so it normalises.  The reference analogue of
`norm_bellPairsMeasurement_op_gateTeleportRegisterGen`. -/
theorem norm_bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef (R : QSystem)
    (Ψ : PureState (R ⊗ (qubit ⊗ qubit))) (p q : Fin 2 × Fin 2) :
    ‖(bellPairsMeasurement.onRight R).op (p, q) (gateTeleportRegisterGenRef R Ψ).vec‖ = 4⁻¹ := by
  rw [bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef]
  -- The `¼ • …` from the collapse identity carries `TensorProduct`'s `SMul` instance, which has no
  -- `NormSMulClass`; `set`+`change` re-elaborates the scalar action to the canonical one.
  set X := (TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportBranch p q)) Ψ.vec with hX
  change ‖(4 : ℂ)⁻¹ • X‖ = 4⁻¹
  rw [norm_smul, hX, norm_mapL_one_gateTeleportBranch, Ψ.normalized, mul_one]
  simp

set_option maxHeartbeats 1000000 in
-- Building the branch `→L[ℂ]` over the six-qubit composite space is defeq-heavy; the default
-- heartbeat budget is insufficient.
/-- **The correction-free single Bell branch** for outcome `(p, q)`: the continuous linear map
`v ↦ |β_p⟩ ⊗ |β_q⟩ ⊗ (CNOT v)`.  It is `gateTeleportBranch p q` with the single-qubit Pauli
byproducts already undone — the outcome-independent target the correction
`gateTeleportCorrection p q` drives the measured branch to.  Packaged as a `→L[ℂ]` (like
`gateTeleportBranch`) so it can be tensored with the identity on the reference (`mapL 1 ·`). -/
noncomputable def gateTeleportCleanBranch (p q : Fin 2 × Fin 2) :
    (qubit ⊗ qubit).space →L[ℂ]
      (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)).space :=
  (TensorProduct.mk ℂ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space (qubit ⊗ qubit).space
        (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2)).toContinuousLinearMap.comp cnotGate.op

/-- The action of `gateTeleportCleanBranch p q` on an input vector `v`:
`|β_p⟩ ⊗ |β_q⟩ ⊗ (CNOT v)`. -/
theorem gateTeleportCleanBranch_apply (p q : Fin 2 × Fin 2) (v : (qubit ⊗ qubit).space) :
    gateTeleportCleanBranch p q v
      = (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ] cnotGate.op v :=
  rfl

/-- **The correction undoes the byproducts on the output wire.**  Composing the byproduct-carrying
branch `gateTeleportBranch p q` with the correction on the output wire
(`1_M ⊗ gateTeleportCorrection`, identity on the two measured pairs `M`) yields the correction-free
branch `gateTeleportCleanBranch p q`: on `|β_p⟩ ⊗ |β_q⟩ ⊗ ((C_A ⊗ C_B)(CNOT v))` the correction acts
only on the output factor, where it is the adjoint of the byproduct pair
(`gateTeleportCorrection_op_output_apply`), leaving `CNOT v`.  The
`→L[ℂ]` fact fused into the reference collapse below. -/
theorem gateTeleportBranch_corrected_comp (p q : Fin 2 × Fin 2) :
    (TensorProduct.mapL (1 : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →L[ℂ]
          ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space) (gateTeleportCorrection p q).op).comp
        (gateTeleportBranch p q)
      = gateTeleportCleanBranch p q := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  erw [ContinuousLinearMap.comp_apply]
  erw [gateTeleportBranch_apply, TensorProduct.mapL_tmul]
  erw [one_apply_eq_self, gateTeleportCorrection_op_output_apply]
  rfl

set_option maxHeartbeats 1000000 in
-- Composing the reference-augmented correction (`1_R ⊗ 1_M ⊗ correction`) with the reference
-- collapse over the seven-way composite space is defeq-heavy; the default heartbeat budget is
-- insufficient.
/-- **The reference-generalised deterministic `CNOT` collapse** (Nielsen & Chuang Problem 4.6).
Bell-measuring the two co-located pairs of the reference register `gateTeleportRegisterGenRef R Ψ`
(outcome `(p, q)`) and then applying the outcome-determined single-qubit correction
`gateTeleportCorrection p q` — placed on the two output wires, i.e. on the right of both the
reference `R` and the two measured pairs — sends the register to
`¼ (1_R ⊗ gateTeleportCleanBranch p q)(Ψ)`.  The Pauli byproducts are undone, so the output factor
is a clean `CNOT` on the input, **independent of the outcome** `(p, q)` and **linear in `Ψ`** (so
correct for a `Ψ` entangled with `R`).

Proof: rewrite the inner measurement by the reference collapse
(`bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef`, `= ¼ • (1_R ⊗ branch)(Ψ)`), pull
the `¼` out of the linear correction (`map_smul`), turn the two nested `Evolution.onRight`
operators into `TensorProduct.mapL 1`s (`Evolution.onRight_op`), fuse them with the `mapL 1` by
`TensorProduct.mapL_comp`, and check on the branch that
`(1_M ⊗ correction) ∘ gateTeleportBranch = gateTeleportCleanBranch` — the correction undoes the
byproducts on the output wire (`gateTeleportCorrection_op_output_apply`), leaving `CNOT`.  The
reference analogue of `bellPairsMeasurement_corrected_op_gateTeleportRegisterGen`. -/
theorem bellPairsMeasurement_onRight_corrected_op_gateTeleportRegisterGenRef (R : QSystem)
    (Ψ : PureState (R ⊗ (qubit ⊗ qubit))) (p q : Fin 2 × Fin 2) :
    (((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).onRight R).op
        ((bellPairsMeasurement.onRight R).op (p, q) (gateTeleportRegisterGenRef R Ψ).vec)
      = (4 : ℂ)⁻¹ •
          (TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportCleanBranch p q)) Ψ.vec := by
  rw [bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef]
  erw [map_smul]
  rw [Evolution.onRight_op, Evolution.onRight_op]
  congr 1
  -- `(1_R ⊗ (1_M ⊗ correction)) ∘ (1_R ⊗ branch) = 1_R ⊗ cleanBranch`, applied to `Ψ.vec`.
  have key :
      (TensorProduct.mapL (1 : R.space →L[ℂ] R.space)
          (TensorProduct.mapL (1 : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →L[ℂ]
              ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space) (gateTeleportCorrection p q).op)).comp
        (TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportBranch p q))
      = TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportCleanBranch p q) := by
    have hone : (1 : R.space →L[ℂ] R.space).comp 1 = 1 := ContinuousLinearMap.ext fun x => rfl
    erw [← TensorProduct.mapL_comp, hone]
    exact congrArg (fun g => TensorProduct.mapL (1 : R.space →L[ℂ] R.space) g)
      (gateTeleportBranch_corrected_comp p q)
  exact DFunLike.congr_fun key Ψ.vec

end AxQM
