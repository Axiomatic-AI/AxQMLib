/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportCorrection

/-!
# AxQM.Postulates.API — the induced `CNOT` operation as a pure state

The **deterministic `CNOT` of gate teleportation**
(`bellPairsMeasurement_corrected_op_gateTeleportResourceRegister`, Nielsen & Chuang **Problem 4.6**)
is a *vector* identity: Bell-measuring the two co-located pairs of the protocol register and
applying the outcome-`(p, q)` single-qubit correction sends the (unnormalised) branch to
`¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT(q_A ⊗ q_B)`.  This file lifts that vector identity to the **normalised
pure state** the `State`-level induced-operation theorem (`AxQM/NC/Ch4/Problem4_6.lean`)
consumes — the step turning "the corrected output *vector* is `CNOT(q_A ⊗ q_B)` up to the `¼`
amplitude" into "the corrected post-measurement *state* is the product
`(|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT(q_A ⊗ q_B)`".

## What is formalised

* `norm_bellPairsMeasurement_op_gateTeleportResourceRegister` — the measured branch
  `M_{(p,q)} |register⟩` has norm exactly `¼`: it is `¼` times a unit vector (the two Bell vectors
  are unit, `bellBasisVec_norm`, and the corrected output is unit, `norm_gateTeleport_output`).  In
  particular the branch is **nonzero**, so it normalises — and `‖branch‖ = ¼` is the amplitude the
  normalisation divides out (the branch has Born probability `1/16`).

* `gateTeleportCorrection_evolvePure_normalize` — the **corrected, normalised** post-measurement
  pure state.  Applying the single-qubit correction `gateTeleportCorrection p q` to the *normalised*
  branch `M_{(p,q)}|register⟩ / ‖·‖` yields exactly the product pure state
  `(|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT(q_A ⊗ q_B)`: the `¼` branch amplitude cancels against the `‖·‖⁻¹ = 4`
  normalisation (`norm_...`), and the outcome-determined single-qubit correction turns the
  Pauli-corrupted output into the clean `CNOT`.  This is the pure-state factorisation whose right
  marginal is the induced `CNOT` output.

The `State`-level induced-operation theorem these two statements feed (right marginal of the
corrected post-measurement state `= CNOT` output) is in `AxQM/NC/Ch4/Problem4_6.lean`.
-/

namespace AxQM

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

set_option maxHeartbeats 1000000 in
-- `maxHeartbeats` bumped: the norm computation runs over the six-qubit composite system.
/-- **The measured branch has norm `¼`, for a general input.**  The Bell-measurement operator for
outcome `(p, q)` sends the register `gateTeleportRegisterGen ψ` to
`¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ (corrected CNOT)` (`bellPairsMeasurement_op_gateTeleportRegisterGen`), a `¼`
times a unit vector: the Bell vectors are unit (`bellBasisVec_norm`) and the corrected output is
unit (`norm_gateTeleport_output_gen`, the Paulis and `CNOT` being isometric).  Hence the branch has
norm `¼` — the branch amplitude, so the outcome probability is `1/16` — and is in particular
nonzero, so it has a well-defined normalisation. -/
theorem norm_bellPairsMeasurement_op_gateTeleportRegisterGen (ψ : PureState (qubit ⊗ qubit))
    (p q : Fin 2 × Fin 2) :
    ‖(bellPairsMeasurement.op (p, q)) (gateTeleportRegisterGen ψ).vec‖ = 4⁻¹ := by
  rw [bellPairsMeasurement_op_gateTeleportRegisterGen]
  -- The `¼ • …` from the collapse identity carries `TensorProduct`'s `SMul` instance, which has no
  -- `NormSMulClass`; `set`+`change` re-elaborates the scalar action to the canonical one.
  set X : (((qubit ⊗ qubit) ⊗ qubit ⊗ qubit) ⊗ qubit ⊗ qubit).space :=
    (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
      ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
        (cnotGate.op ψ.vec)) with hX
  change ‖(4 : ℂ)⁻¹ • X‖ = 4⁻¹
  rw [norm_smul, hX]
  erw [TensorProduct.norm_tmul, TensorProduct.norm_tmul]
  rw [bellBasisVec_norm, bellBasisVec_norm, norm_gateTeleport_output_gen]
  simp

/-- **The measured branch has norm `¼`** (product-input special case of
`norm_bellPairsMeasurement_op_gateTeleportRegisterGen`).  The branch is nonzero, so it
normalises. -/
theorem norm_bellPairsMeasurement_op_gateTeleportResourceRegister
    (qA qB : PureState qubit) (p q : Fin 2 × Fin 2) :
    ‖(bellPairsMeasurement.op (p, q)) (gateTeleportResourceRegister qA qB).vec‖ = 4⁻¹ :=
  norm_bellPairsMeasurement_op_gateTeleportRegisterGen (qA.tmul qB) p q

set_option maxHeartbeats 1000000 in
-- `maxHeartbeats` bumped: elaboration over the six-qubit composite system is defeq-heavy.
/-- **The corrected, normalised measured branch is `(|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT ψ`, for a general
input.**  Applying the outcome-`(p, q)` single-qubit correction `gateTeleportCorrection p q` (on the
output pair) to the *normalised* post-measurement branch of `gateTeleportRegisterGen ψ` yields
exactly the product pure state `(|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT ψ`.  Reading the corrected vector identity
`bellPairsMeasurement_corrected_op_gateTeleportRegisterGen` (the corrected branch is
`¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT ψ`), the `¼` branch amplitude cancels against the `‖·‖⁻¹ = 4`
normalisation (`norm_bellPairsMeasurement_op_gateTeleportRegisterGen`).  So the corrected
post-measurement state is a *product*, whose output (right) factor is the clean `CNOT ψ` — the
pure-state input to the induced-operation theorem. -/
theorem gateTeleportCorrection_evolvePure_normalizeGen (ψ : PureState (qubit ⊗ qubit))
    (p q : Fin 2 × Fin 2)
    (hv : (bellPairsMeasurement.op (p, q)) (gateTeleportRegisterGen ψ).vec ≠ 0) :
    ((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).evolvePure
        (PureState.normalize
          ((bellPairsMeasurement.op (p, q)) (gateTeleportRegisterGen ψ).vec) hv)
      = ((bellState p.1 p.2).tmul (bellState q.1 q.2)).tmul (cnotGate.evolvePure ψ) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.normalize_vec, map_smul,
    bellPairsMeasurement_corrected_op_gateTeleportRegisterGen,
    norm_bellPairsMeasurement_op_gateTeleportRegisterGen, PureState.tmul_vec,
    PureState.tmul_vec, bellState_vec, bellState_vec, Evolution.evolvePure_vec]
  -- Both scalar actions carry `TensorProduct`'s `SMul`; `set W`+`change` canonicalises them so
  -- `smul_smul` fires and the `¼` amplitude cancels against the `‖·‖⁻¹ = 4` normalisation.
  set W : (((qubit ⊗ qubit) ⊗ qubit ⊗ qubit) ⊗ qubit ⊗ qubit).space :=
    bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2 ⊗ₜ[ℂ] cnotGate.op ψ.vec with hW
  change ((4⁻¹ : ℝ) : ℂ)⁻¹ • ((4 : ℂ)⁻¹ • W) = W
  rw [smul_smul, show ((4⁻¹ : ℝ) : ℂ)⁻¹ * (4 : ℂ)⁻¹ = 1 by push_cast; norm_num, one_smul]

/-- **The corrected, normalised measured branch is `(|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT(q_A ⊗ q_B)`**
(product-input special case of `gateTeleportCorrection_evolvePure_normalizeGen`), the pure-state
input to the product-input induced-operation theorem. -/
theorem gateTeleportCorrection_evolvePure_normalize
    (qA qB : PureState qubit) (p q : Fin 2 × Fin 2)
    (hv : (bellPairsMeasurement.op (p, q)) (gateTeleportResourceRegister qA qB).vec ≠ 0) :
    ((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).evolvePure
        (PureState.normalize
          ((bellPairsMeasurement.op (p, q)) (gateTeleportResourceRegister qA qB).vec) hv)
      = ((bellState p.1 p.2).tmul (bellState q.1 q.2)).tmul (cnotGate.evolvePure (qA.tmul qB)) :=
  gateTeleportCorrection_evolvePure_normalizeGen (qA.tmul qB) p q hv

end AxQM
