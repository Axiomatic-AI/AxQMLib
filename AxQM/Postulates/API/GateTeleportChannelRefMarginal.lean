/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportChannelRefCorrected
import AxQM.Postulates.API.SystemIsoComm

/-!
# AxQM.Postulates.API — the reference gate-teleportation channel: reshape + normalise

The reference-generalised **deterministic collapse**
(`bellPairsMeasurement_onRight_corrected_op_gateTeleportRegisterGenRef`,
`GateTeleportChannelRefCorrected.lean`) sends the gate-teleportation register — with the two `CNOT`
input wires entangled to an arbitrary reference `R` — to `¼ (1_R ⊗ gateTeleportCleanBranch p q)(Ψ)`,
where `gateTeleportCleanBranch p q : v ↦ |β_p⟩ ⊗ |β_q⟩ ⊗ (CNOT v)` carries the *clean*
(byproduct-free) `CNOT` on the two output wires.  This file turns that vector identity into the
**induced quantum operation** the `n`-wire universality lift consumes: normalise the corrected
branch and trace out the two measured Bell pairs, obtaining `(cnotGate.onRight R)` — `1_R ⊗ CNOT` —
on the input `Ψ`.  It is the reference analogue of `GateTeleportChannel.lean`, threaded through the
reference `R`.

The one structural novelty over the non-reference case is the **middle-factor marginal**.  In the
standalone gadget the corrected, normalised state is a *product* `(|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT ψ` on
`M ⊗ O` (`M` the two measured pairs, `O` the two outputs), so `State.reducedRight` reads off the
output directly.  With a reference the state lives on `R ⊗ (M ⊗ O)` and is *not* a product — the
constant measured-pair factor `|β_p⟩ ⊗ |β_q⟩` sits in the **middle**.  The reshape
`QSystem.Iso.leftComm R M O : R ⊗ (M ⊗ O) ≃ₛ M ⊗ (R ⊗ O)` brings that constant factor to the front,
where the state *does* factor as `(|β_p⟩ ⊗ |β_q⟩) ⊗ ((cnotGate.onRight R) Ψ)`; then
`State.reducedRight` traces the measured pairs and leaves `(cnotGate.onRight R) Ψ`.

## What is formalised

* `leftComm_mapL_one_gateTeleportCleanBranch` — **the reshape core.**  Applying
  `QSystem.Iso.leftComm R M O` to `(1_R ⊗ gateTeleportCleanBranch p q)(w)` yields
  `(|β_p⟩ ⊗ |β_q⟩) ⊗ ((cnotGate.onRight R) w)`: the constant Bell-pair factor is pulled to the front
  and the surviving `R ⊗ O` factor carries `1_R ⊗ CNOT` on `w`.  Linear in `w`, so proved on the
  product vectors `r ⊗ v` (which span, `TensorProduct.ext'`) from
  `QSystem.Iso.leftComm_toIsometry_tmul` and `Evolution.onRight_op_tmul`.

* `gateTeleportCorrection_evolvePure_normalizeRef` — **the corrected, normalised, reshaped pure
  state.**  Applying the outcome-`(p, q)` single-qubit correction to the *normalised* reference
  measured branch and reshaping by `QSystem.Iso.leftComm R M O` gives exactly the product pure state
  `(|β_p⟩ ⊗ |β_q⟩) ⊗ ((cnotGate.onRight R).evolvePure Ψ)`: the `¼` branch amplitude cancels against
  the `‖·‖⁻¹ = 4` normalisation
  (`norm_bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef`), the correction cleans the
  byproducts (`bellPairsMeasurement_onRight_corrected_op_gateTeleportRegisterGenRef`), and the
  reshape core factors out the measured pairs.  The reference analogue of
  `gateTeleportCorrection_evolvePure_normalizeGen`; its right marginal is the induced operation.

The `State`-level induced-operation reading built on it
(`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGenRef`, measure → correct →
reshape → trace-out gives `(cnotGate.onRight R)` on `Ψ`, for `Ψ` entangled with `R`) is stated in
`AxQM/NC/Ch4/Problem4_6.lean`, beside the non-reference form.
-/

open scoped TensorProduct

namespace AxQM

open ContinuousLinearMap

set_option maxHeartbeats 1000000 in
-- The `ext'` reduction and the pure-tensor rewrites run over the seven-way composite (`R`
-- beside the six-qubit register); the default heartbeat budget is insufficient.
/-- **The reshape core of the reference gate-teleportation channel.**  Applying the middle-factor
reshape `QSystem.Iso.leftComm R M O` (with `M = (qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)` the two measured
pairs and `O = qubit ⊗ qubit` the two outputs) to `(1_R ⊗ gateTeleportCleanBranch p q)(w)` sends it
to `(|β_p⟩ ⊗ |β_q⟩) ⊗ ((cnotGate.onRight R) w)`: the constant Bell-pair factor `|β_p⟩ ⊗ |β_q⟩` — the
`M` part of the clean branch, independent of `w` — is pulled to the front, and the surviving
`R ⊗ O` factor carries `1_R ⊗ CNOT` (`cnotGate.onRight R`) on `w`.  This is the identity that lets
`State.reducedRight` trace out the measured pairs after the reshape and read off the
`CNOT`-processed input.  Both sides are `ℂ`-linear in `w`, so it suffices to check on the product
vectors `r ⊗ v` (which span); there `TensorProduct.mapL_tmul` computes the clean branch on `v`
(`gateTeleportCleanBranch_apply`), `QSystem.Iso.leftComm_toIsometry_tmul` performs the reshape, and
`Evolution.onRight_op_tmul` matches the right-hand side. -/
theorem leftComm_mapL_one_gateTeleportCleanBranch (R : QSystem) (p q : Fin 2 × Fin 2)
    (w : (R ⊗ (qubit ⊗ qubit)).space) :
    (QSystem.Iso.leftComm R ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) (qubit ⊗ qubit)).toIsometry
        ((TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportCleanBranch p q)) w)
      = (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ] (cnotGate.onRight R).op w := by
  -- Both sides are `ℂ`-linear in `w`; check on `0`, on pure tensors `r ⊗ v` (where the reshape and
  -- `CNOT`-on-`R` steps are *definitional*, closed by `rfl`), and additively.  `map_add`/`map_zero`
  -- are supplied their map *explicitly* and run through `erw`, since over this seven-way composite
  -- the reshape isometry's coercion does not match `rw`'s pattern up to syntax.
  induction w using TensorProduct.inductionOn with
  | tmul r v =>
    rw [TensorProduct.mapL_tmul, one_apply_eq_self, gateTeleportCleanBranch_apply]
    rfl
  | add x y hx hy =>
    rw [map_add (TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportCleanBranch p q)) x y]
    erw [map_add (QSystem.Iso.leftComm R _ _).toIsometry]
    rw [hx, hy]
    erw [map_add (cnotGate.onRight R).op]
    rw [TensorProduct.tmul_add]
    rfl

set_option maxHeartbeats 1000000 in
-- The correction/normalisation chain and the reshape run over the seven-way composite space; the
-- default heartbeat budget is insufficient.
/-- **The corrected, normalised, reshaped reference measured branch is
`(|β_p⟩ ⊗ |β_q⟩) ⊗ ((cnotGate.onRight R).evolvePure Ψ)`** (Nielsen & Chuang, Problem 4.6).  Applying
the outcome-`(p, q)` single-qubit correction `gateTeleportCorrection p q` (on the output wires
beside `R` and the measured pairs) to the *normalised* reference measured branch of
`gateTeleportRegisterGenRef R Ψ`, and reshaping by `QSystem.Iso.leftComm R M O`, yields exactly the
product pure state `(|β_p⟩ ⊗ |β_q⟩) ⊗ ((cnotGate.onRight R).evolvePure Ψ)`, i.e. `1_R ⊗ CNOT` on the
input `Ψ` tensored with the two measured Bell pairs.

The `¼` branch amplitude cancels against the `‖·‖⁻¹ = 4` normalisation
(`norm_bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef`), the correction undoes the
byproducts (`bellPairsMeasurement_onRight_corrected_op_gateTeleportRegisterGenRef`, giving
`¼ (1_R ⊗ gateTeleportCleanBranch p q)(Ψ)`), and the reshape core
(`leftComm_mapL_one_gateTeleportCleanBranch`) pulls the constant measured-pair factor to the front.
The reference analogue of `gateTeleportCorrection_evolvePure_normalizeGen`; because it is linear in
`Ψ` it is correct for a `Ψ` entangled with `R`.  Its right marginal is the induced `CNOT` operation
tensored with the identity on `R`. -/
theorem gateTeleportCorrection_evolvePure_normalizeRef (R : QSystem)
    (Ψ : PureState (R ⊗ (qubit ⊗ qubit))) (p q : Fin 2 × Fin 2)
    (hv : (bellPairsMeasurement.onRight R).op (p, q) (gateTeleportRegisterGenRef R Ψ).vec ≠ 0) :
    ((((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).onRight
              R).evolvePure
            (PureState.normalize
              ((bellPairsMeasurement.onRight R).op (p, q) (gateTeleportRegisterGenRef R Ψ).vec)
              hv)).congr
        (QSystem.Iso.leftComm R ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) (qubit ⊗ qubit))
      = ((bellState p.1 p.2).tmul (bellState q.1 q.2)).tmul
          ((cnotGate.onRight R).evolvePure Ψ) := by
  apply PureState.ext
  rw [PureState.congr_vec, Evolution.evolvePure_vec, PureState.normalize_vec, map_smul,
    bellPairsMeasurement_onRight_corrected_op_gateTeleportRegisterGenRef,
    norm_bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef, PureState.tmul_vec,
    PureState.tmul_vec, bellState_vec, bellState_vec, Evolution.evolvePure_vec]
  -- The two scalars carry `TensorProduct`'s `SMul` instance, which lacks the `smul_smul` structure
  -- `rw` needs; `set`+`change` re-elaborates them to the canonical action so the `¼`
  -- amplitude cancels against the `‖·‖⁻¹ = 4` normalisation.
  set Y := (TensorProduct.mapL (1 : R.space →L[ℂ] R.space) (gateTeleportCleanBranch p q)) Ψ.vec
    with hY
  change (QSystem.Iso.leftComm R ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) (qubit ⊗ qubit)).toIsometry
      (((4⁻¹ : ℝ) : ℂ)⁻¹ • (4 : ℂ)⁻¹ • Y) = _
  rw [smul_smul, show (((4⁻¹ : ℝ) : ℂ)⁻¹ * (4 : ℂ)⁻¹) = 1 by push_cast; norm_num, one_smul, hY]
  exact leftComm_mapL_one_gateTeleportCleanBranch R p q Ψ.vec

end AxQM
