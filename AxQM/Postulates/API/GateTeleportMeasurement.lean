/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportationIdentity
import AxQM.Postulates.API.PhaseEstimationSuperposition
import ToMathlib.Topology.Algebra.Module.FinsetSum

/-!
# AxQM.Postulates.API — the Bell-measurement readout of gate teleportation

The **Bell-measurement readout** of the Gottesman–Chuang gate-teleportation identity for `CNOT`
(Nielsen & Chuang **Problem 4.6**).  The reduction core `cnotGateTeleportation_identity` is an
algebraic vector identity; this file reads it as a `Measurement`, so that
"`{single-qubit unitaries, Bell-basis measurement, four-qubit state preparation}` implements `CNOT`"
follows from the measurement postulates.

## What is formalised

* `gateTeleportResourceRegister qA qB` (`|χ⟩`-register) — the physical protocol register: the two
  input qubits `q_A, q_B` together with the four-qubit resource state `cnotGateTeleportResource`,
  reshaped by `gateTeleportProtocolReshape` so the two Bell-measured pairs `(q_A, a_in)`,
  `(q_B, b_in)` are the left `(q ⊗ q) ⊗ (q ⊗ q)` block and the two teleported output halves are the
  right `q ⊗ q` factor.

* `bellPairsMeasurement` — the **joint Bell measurement of the two co-located measured pairs**: the
  Bell-basis measurement of the left block (each pair measured in the Bell basis), tensored with the
  identity on the output pair.  It is a genuine `Measurement` (Postulate 3), assembled from
  `bellMeasurement` (resource #2 of Problem 4.6) by `Measurement.leftAndBasisRight` and
  `Measurement.onLeft`.

* `bellPairsMeasurement_op_gateTeleportResourceRegister` — **the collapse identity** (the
  Postulate 4, state update): the measurement operator for outcome `(p, q)` sends the protocol
  register to the single Bell branch
  `¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ ((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT (q_A ⊗ q_B)))`,
  `p = (x₁,y₁)`, `q = (x₂,y₂)`.  Bell orthonormality (`bellBasisVec_inner`, via
  `bellPairsMeasurement_op_bellTmul`) picks the `(p, q)` summand out of the double sum of
  `cnotGateTeleportation_identity`, so measuring the two pairs collapses the two output qubits to
  `CNOT (q_A ⊗ q_B)` up to the outcome-determined pair of **single-qubit** Pauli corrections.

* `bellPairsMeasurement_bornProb_pos` — **the Born rule (Postulate 3)**: every one of the sixteen
  outcomes `(p, q)` has *positive* probability, so each is a possible measurement result (cf.
  `bellMeasurement_bornProb_bellState` for a single pair).  The collapsed branch is nonzero (its
  output half is a unit vector, `norm_gateTeleport_output`), so `bornProb = ‖M|ψ⟩‖² > 0`.

Together these say: Bell-measuring the two pairs yields some outcome `(p, q)` (each possible), and
on that branch the two output qubits carry `CNOT (q_A ⊗ q_B)` up to a pair of outcome-determined
single-qubit Pauli corrections — the resource set implements `CNOT`, by the measurement
postulates.  The exact outcome probability `1/16` is in
`AxQM/Postulates/API/GateTeleportChannel.lean`, the deterministic *undoing* of the corrections
(applying `X^y Z^x` back) is in `AxQM/Postulates/API/GateTeleportCorrection.lean`, and the statement
of Problem 4.6 is in `AxQM/NC/Ch4/Problem4_6.lean`.
-/

namespace AxQM

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

/-- **The gate-teleportation protocol register.**  The two input qubits `q_A, q_B` beside the
four-qubit resource state `|χ⟩` (`cnotGateTeleportResource`), reshaped by
`gateTeleportProtocolReshape` into `((q_A ⊗ a_in) ⊗ (q_B ⊗ b_in)) ⊗ (a_out ⊗ b_out)`: the two
Bell-measured pairs blocked on the left, the two teleported output halves co-located right. -/
noncomputable def gateTeleportResourceRegister (qA qB : PureState qubit) :
    PureState (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)) :=
  PureState.congr gateTeleportProtocolReshape ((qA.tmul qB).tmul cnotGateTeleportResource)

/-- **The joint Bell measurement of the two co-located pairs** (Problem 4.6 resource #2, applied to
both measured pairs of the protocol register).  Each of the two pairs of the left block is measured
in the Bell basis, with the identity on the output pair; the joint outcome is the pair of Bell
outcomes `(p, q)`.  A genuine `Measurement` (Postulate 3). -/
noncomputable def bellPairsMeasurement :
    Measurement ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))
      (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)) :=
  (bellMeasurement.leftAndBasisRight bellBasis).onLeft (qubit ⊗ qubit)

/-- The measurement operator of `bellPairsMeasurement` for outcome `(p, q)`, applied to a pure
tensor `(|β_{p'}⟩ ⊗ |β_{q'}⟩) ⊗ w` of two Bell vectors with an arbitrary output vector `w`, projects
onto the `(p, q)` Bell branch: it returns `δ_{p,p'} δ_{q,q'} (|β_p⟩ ⊗ |β_q⟩) ⊗ w`.  This is the
Bell-orthonormality collapse (`bellBasisVec_inner`) at the level of a single summand. -/
theorem bellPairsMeasurement_op_bellTmul
    (p q p' q' : Fin 2 × Fin 2) (w : (qubit ⊗ qubit).space) :
    (bellPairsMeasurement.op (p, q))
        ((bellBasisVec p'.1 p'.2 ⊗ₜ[ℂ] bellBasisVec q'.1 q'.2) ⊗ₜ[ℂ] w)
      = (if p = p' then (1 : ℂ) else 0) • (if q = q' then (1 : ℂ) else 0) •
          ((bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ] w) := by
  rw [bellPairsMeasurement,
    Measurement.onLeft_op_tmul (bellMeasurement.leftAndBasisRight bellBasis) (qubit ⊗ qubit) (p, q)
      (bellBasisVec p'.1 p'.2 ⊗ₜ[ℂ] bellBasisVec q'.1 q'.2) w, Measurement.leftAndBasisRight,
    Measurement.cascade_op,
    ContinuousLinearMap.comp_apply
      (((Measurement.ofOrthonormalBasis bellBasis).onRight (qubit ⊗ qubit)).op q)
      ((bellMeasurement.onLeft (qubit ⊗ qubit)).op p)
      (bellBasisVec p'.1 p'.2 ⊗ₜ[ℂ] bellBasisVec q'.1 q'.2),
    Measurement.onLeft_op_tmul bellMeasurement (qubit ⊗ qubit) p (bellBasisVec p'.1 p'.2)
      (bellBasisVec q'.1 q'.2),
    Measurement.onRight_op_tmul (Measurement.ofOrthonormalBasis bellBasis) (qubit ⊗ qubit) q
      (bellMeasurement.op p (bellBasisVec p'.1 p'.2)) (bellBasisVec q'.1 q'.2),
    bellMeasurement_op, rankOne_apply,
    Measurement.ofOrthonormalBasis_op, bellBasis_apply, bellState_vec, rankOne_apply,
    bellBasisVec_inner, bellBasisVec_inner]
  simp only [Prod.mk.eta, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  rw [mul_comm]; rfl

/-- **The gate-teleportation protocol register for a general two-qubit input** `ψ`: the input state
`ψ` beside the four-qubit resource `|χ⟩`, reshaped by `gateTeleportProtocolReshape` exactly as
`gateTeleportResourceRegister`, but taking `ψ : PureState (qubit ⊗ qubit)` in place of a product
`q_A ⊗ q_B`.  The product register is the special case `ψ = q_A ⊗ q_B`
(`gateTeleportResourceRegister_eq_gen`).  This general-input register is the *workhorse*: the whole
teleportation chain is stated for it, and the product-input statements are `ψ = q_A ⊗ q_B`
corollaries — needed because a gate must act correctly on *every* input, and the (normalising,
nonlinear) induced operation does not extend from product to entangled inputs on its own. -/
noncomputable def gateTeleportRegisterGen (ψ : PureState (qubit ⊗ qubit)) :
    PureState (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)) :=
  PureState.congr gateTeleportProtocolReshape (ψ.tmul cnotGateTeleportResource)

/-- The product-input register is the special case of `gateTeleportRegisterGen` with the
input `ψ = q_A ⊗ q_B` (definitional). -/
theorem gateTeleportResourceRegister_eq_gen (qA qB : PureState qubit) :
    gateTeleportResourceRegister qA qB = gateTeleportRegisterGen (qA.tmul qB) := rfl

/-- **The `CNOT` gate-teleportation identity for an arbitrary two-qubit input** (Nielsen & Chuang
Problem 4.6).  For *every* input vector `v : (qubit ⊗ qubit).space` — not merely a product
`q_A ⊗ q_B` —
`reshape (v ⊗ |χ⟩) = ¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ ((C_A ⊗ C_B)(CNOT v))`,
with the same outcome-determined single-qubit corrections `C_A, C_B` as
`cnotGateTeleportation_identity`.  Both sides are ℂ-linear in `v` (the reshape isometry, and the
tensor placement of `CNOT v`), so — bundling each as a linear map — the identity extends off the
product vectors, on which it is `cnotGateTeleportation_identity`, to all of `(qubit ⊗ qubit).space`
by `TensorProduct.ext'` (product vectors span).  This is the step that upgrades the identity from
product inputs to every, possibly entangled, two-qubit input. -/
theorem cnotGateTeleportation_identity_general (v : (qubit ⊗ qubit).space) :
    gateTeleportProtocolReshape.toIsometry (v ⊗ₜ[ℂ] cnotGateTeleportResource.vec)
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
            ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
              (cnotGate.op v)) := by
  -- Bundle both sides as linear maps in `v` and check agreement on the product vectors `qA ⊗ qB`
  -- (which span), where the identity is `cnotGateTeleportation_identity`.
  suffices key :
      (gateTeleportProtocolReshape.toIsometry.toLinearEquiv.toLinearMap ∘ₗ
          (TensorProduct.mk ℂ (qubit ⊗ qubit).space _).flip cnotGateTeleportResource.vec)
        = ((4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
            (TensorProduct.mk ℂ _ (qubit ⊗ qubit).space
                (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2)).comp
              ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op.comp
                cnotGate.op).toLinearMap) by
    have := LinearMap.congr_fun key v
    -- `erw`: the bundled composite spaces block `rw`/`simp` from reading the applied sums.
    erw [LinearMap.smul_apply, LinearMap.sum_apply] at this
    refine this.trans (congrArg _ (Finset.sum_congr rfl fun d _ => ?_))
    erw [LinearMap.sum_apply]
    rfl
  -- On a product vector both maps unfold definitionally to the product-input identity.
  exact TensorProduct.ext' (fun qA qB => cnotGateTeleportation_identity qA qB)

set_option maxHeartbeats 1000000 in
-- `maxHeartbeats` bumped: elaboration over the six-qubit composite system (nested
-- `TensorProduct`s with `QSystem`-projected instances) is defeq-heavy.
/-- **The collapse identity for a raw input vector** (Nielsen & Chuang Problem 4.6, Postulate 4 read
of `cnotGateTeleportation_identity_general`).  For *every* two-qubit input vector `v` — not only a
unit `PureState` — the Bell-measurement operator for outcome `(p, q)` sends the reshaped register
`reshape (v ⊗ |χ⟩)` to the single Bell branch
`¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ ((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT v))`.  Reading the double sum of
`cnotGateTeleportation_identity_general`, Bell orthonormality (`bellBasisVec_inner`, via
`bellPairsMeasurement_op_bellTmul`) selects the `(p, q)` term; the `¼` prefactor is the branch
amplitude.  The general-input register collapse `bellPairsMeasurement_op_gateTeleportRegisterGen` is
its `v = ψ.vec` specialisation; stating it for a raw `v` (no `PureState` wrapper) lets it tensor
with the identity on a reference system in the register-embedded universality lift
(`AxQM/Postulates/API/GateTeleportChannelRef.lean`). -/
theorem bellPairsMeasurement_op_reshape_tmul (v : (qubit ⊗ qubit).space) (p q : Fin 2 × Fin 2) :
    (bellPairsMeasurement.op (p, q))
        (gateTeleportProtocolReshape.toIsometry (v ⊗ₜ[ℂ] cnotGateTeleportResource.vec))
      = (4 : ℂ)⁻¹ • ((bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
          ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
            (cnotGate.op v))) := by
  rw [cnotGateTeleportation_identity_general]
  -- The summand is ascribed to the bundled six-qubit space the measurement acts on.
  refine (ContinuousLinearMap.map_smul_double_sum (bellPairsMeasurement.op (p, q)) (4⁻¹ : ℂ)
    (fun (p' q' : Fin 2 × Fin 2) =>
      ((bellBasisVec p'.1 p'.2 ⊗ₜ[ℂ] bellBasisVec q'.1 q'.2) ⊗ₜ[ℂ]
        ((pauliByproduct (p'.1 + q'.1) p'.2 ⊗ pauliByproduct q'.1 (p'.2 + q'.2)).op
          (cnotGate.op v)) : (((qubit ⊗ qubit) ⊗ qubit ⊗ qubit) ⊗ qubit ⊗ qubit).space))).trans ?_
  congr 1
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · erw [bellPairsMeasurement_op_bellTmul]
      simp
      rfl
    · intro b _ hb
      erw [bellPairsMeasurement_op_bellTmul]; rw [ite_eq_right (Ne.symm hb), zero_smul,
          smul_zero]; rfl
    · intro h; exact absurd (Finset.mem_univ q) h
  · intro b _ hb
    refine Finset.sum_eq_zero (fun c _ => ?_)
    erw [bellPairsMeasurement_op_bellTmul]; rw [ite_eq_right (Ne.symm hb), zero_smul]; rfl
  · intro h; exact absurd (Finset.mem_univ p) h

set_option maxHeartbeats 1000000 in
-- `maxHeartbeats` bumped: elaboration over the six-qubit composite system (nested
-- `TensorProduct`s with `QSystem`-projected instances) is defeq-heavy.
/-- **The collapse identity of the gate-teleportation protocol for a general input** (Nielsen &
Chuang Problem 4.6, Postulate 4 read of `cnotGateTeleportation_identity_general`).  For input pure
state `ψ`, the Bell-measurement operator for outcome `(p, q)` sends the protocol register
`gateTeleportRegisterGen ψ` to the single Bell branch
`¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ ((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT ψ))`.  This is the `v = ψ.vec`
specialisation of the raw-vector collapse `bellPairsMeasurement_op_reshape_tmul` (after unfolding
`gateTeleportRegisterGen` to `reshape (ψ.vec ⊗ |χ⟩)`); the `¼` prefactor is the branch amplitude
(norm `¼`), so the outcome has probability `1/16`. -/
theorem bellPairsMeasurement_op_gateTeleportRegisterGen (ψ : PureState (qubit ⊗ qubit))
    (p q : Fin 2 × Fin 2) :
    (bellPairsMeasurement.op (p, q)) (gateTeleportRegisterGen ψ).vec
      = (4 : ℂ)⁻¹ • ((bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
          ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
            (cnotGate.op ψ.vec))) := by
  rw [gateTeleportRegisterGen, PureState.congr_vec, PureState.tmul_vec]
  exact bellPairsMeasurement_op_reshape_tmul ψ.vec p q

/-- **The collapse identity for a product input** (Nielsen & Chuang Problem 4.6): the
`ψ = q_A ⊗ q_B` special case of `bellPairsMeasurement_op_gateTeleportRegisterGen`, whose right
factor becomes `CNOT (q_A ⊗ q_B)`.  Definitional (`gateTeleportResourceRegister qA qB =
gateTeleportRegisterGen (qA.tmul qB)` and `(qA.tmul qB).vec = qA.vec ⊗ₜ qB.vec`, both `rfl`). -/
theorem bellPairsMeasurement_op_gateTeleportResourceRegister
    (qA qB : PureState qubit) (p q : Fin 2 × Fin 2) :
    (bellPairsMeasurement.op (p, q)) (gateTeleportResourceRegister qA qB).vec
      = (4 : ℂ)⁻¹ • ((bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
          ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
            (cnotGate.op (qA.vec ⊗ₜ[ℂ] qB.vec)))) :=
  bellPairsMeasurement_op_gateTeleportRegisterGen (qA.tmul qB) p q

/-- The output half of the general-input collapsed branch is a unit vector: the two single-qubit
Pauli byproducts and the `CNOT` are isometric, so they preserve the norm of the unit input `ψ`. -/
theorem norm_gateTeleport_output_gen (ψ : PureState (qubit ⊗ qubit)) (p q : Fin 2 × Fin 2) :
    ‖(pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
        (cnotGate.op ψ.vec)‖ = 1 := by
  rw [Evolution.norm_op_apply, Evolution.norm_op_apply]
  exact ψ.normalized

/-- The output half of the collapsed branch is a unit vector (product-input special case of
`norm_gateTeleport_output_gen`). -/
theorem norm_gateTeleport_output (qA qB : PureState qubit) (p q : Fin 2 × Fin 2) :
    ‖(pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
        (cnotGate.op (qA.vec ⊗ₜ[ℂ] qB.vec))‖ = 1 :=
  norm_gateTeleport_output_gen (qA.tmul qB) p q

set_option maxHeartbeats 1000000 in
-- `maxHeartbeats` bumped: the norm computation runs over the six-qubit composite system.
/-- **The Born rule for the gate-teleportation measurement (Postulate 3): every outcome is
possible.**  Each of the sixteen joint outcomes `(p, q)` has *positive* Born probability, so
Bell-measuring the two pairs does yield each `(p, q)`.  By `bornProb = ‖M|ψ⟩‖²`
(`bornProb_toState_eq_normSq`), positivity is `M|ψ⟩ ≠ 0`; the collapse identity gives
`M|ψ⟩ = ¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ (corrected CNOT)`, whose output half is a unit vector
(`norm_gateTeleport_output`), hence nonzero.  This is the measurement-postulate fact underlying the
`CNOT` implementation (cf. `bellMeasurement_bornProb_bellState` for a single pair). -/
theorem bellPairsMeasurement_bornProb_pos (qA qB : PureState qubit) (p q : Fin 2 × Fin 2) :
    0 < bellPairsMeasurement.bornProb (gateTeleportResourceRegister qA qB).toState (p, q) := by
  rw [Measurement.bornProb_toState_eq_normSq]
  refine pow_pos ?_ 2
  rw [norm_pos_iff, bellPairsMeasurement_op_gateTeleportResourceRegister]
  refine smul_ne_zero (by norm_num) ?_
  erw [← norm_ne_zero_iff]
  erw [TensorProduct.norm_tmul, TensorProduct.norm_tmul]
  rw [bellBasisVec_norm, bellBasisVec_norm, norm_gateTeleport_output]; norm_num

end AxQM
