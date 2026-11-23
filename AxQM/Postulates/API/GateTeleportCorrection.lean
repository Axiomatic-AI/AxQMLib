/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportMeasurement

/-!
# AxQM.Postulates.API — the deterministic `CNOT` of gate teleportation

The **correction step** of the Gottesman–Chuang gate-teleportation protocol for `CNOT` (Nielsen &
Chuang **Problem 4.6**).  The collapse identity
`bellPairsMeasurement_op_gateTeleportResourceRegister` (`GateTeleportMeasurement`) leaves the two
output qubits in `CNOT (q_A ⊗ q_B)` *up to* the outcome-determined pair of single-qubit Pauli
byproducts.  This file discharges the piece left open there — **undoing those
byproducts** — so that the protocol implements `CNOT` **deterministically**: whatever the
Bell-measurement outcome `(p, q)`, applying the outcome-determined single-qubit correction to the
output pair recovers the *same* state `CNOT (q_A ⊗ q_B)`.

## What is formalised

* `gateTeleportCorrection p q` — the **correction gate** for outcome `(p, q) = ((x₁,y₁),(x₂,y₂))`:
  the adjoint (inverse) of the byproduct pair `(X^{y₁}Z^{x₁+x₂}) ⊗ (X^{y₁+y₂}Z^{x₂})` that appears
  on the output in the collapse identity.  `gateTeleportCorrection_eq_tmul` exhibits it as
  `(pauliByproduct (x₁+x₂) y₁)† ⊗ (pauliByproduct x₂ (y₁+y₂))†` — a tensor of **two single-qubit**
  gates, so it lies entirely in resource #1 of Problem 4.6 (single-qubit unitaries).

* `gateTeleportCorrection_op_output_apply` — **the recovery identity** (workhorse): applying the
  correction to a byproduct-corrupted output `(C_A ⊗ C_B) w` returns exactly `w`, for *any* output
  vector `w`.  The correction is the adjoint of the byproduct, and a gate followed by its adjoint is
  the identity (`Evolution.adjoint_comp_self`), so the byproduct is undone exactly (no residual
  phase — unlike the byproduct composed with *itself*, which would leave a global sign).
  `gateTeleportCorrection_op_output` is its `w := CNOT (q_A ⊗ q_B)` corollary.

* `bellPairsMeasurement_corrected_op_gateTeleportResourceRegister` — **the deterministic `CNOT`**
  (the headline).  Bell-measuring the two pairs (outcome `(p, q)`) and then applying the correction
  `gateTeleportCorrection p q` to the output pair sends the protocol register to
  `¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ (CNOT (q_A ⊗ q_B))`.  The output factor `CNOT (q_A ⊗ q_B)` is **independent
  of the outcome** `(p, q)`: measure, read off `(p, q)`, apply the corresponding single-qubit
  correction, and the two output qubits carry `CNOT (q_A ⊗ q_B)` on *every* branch.  This is
  precisely "the resource set `{single-qubit unitaries, Bell-basis measurement, four-qubit state
  preparation}` implements the `CNOT` gate", now as a deterministic operation rather than one up to
  a correction — the physics linchpin the measurement-based universality reduction consumes.
-/

namespace AxQM

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

/-- **The adjoint of a product gate is the product of the adjoints** `(U ⊗ V)† = U† ⊗ V†`:
inverting a tensor gate inverts each factor independently (no order reversal, unlike
`Evolution.adjoint_comp`).  Lifts `TensorProduct.adjoint_mapL` on linear maps to the `Evolution`
gate monoid via `Evolution.tmul_op`/`Evolution.adjoint_op`.  In particular the inverse of a
two-local gate is again two-local, keeping the teleportation correction single-qubit. -/
theorem Evolution.adjoint_tmul {S T : QSystem} (U : Evolution S) (V : Evolution T) :
    (U.tmul V).adjoint = U.adjoint.tmul V.adjoint := by
  apply Evolution.ext
  simp only [Evolution.adjoint_op, Evolution.tmul_op]
  exact TensorProduct.adjoint_mapL U.op V.op

/-- **The gate-teleportation correction gate** for Bell-measurement outcome
`(p, q) = ((x₁,y₁),(x₂,y₂))`: the inverse of the byproduct pair
`(X^{y₁}Z^{x₁+x₂}) ⊗ (X^{y₁+y₂}Z^{x₂})` that the collapse identity leaves on the two output qubits
(`bellPairsMeasurement_op_gateTeleportResourceRegister`).  Applying it to the output pair undoes the
Pauli byproducts, so the protocol implements `CNOT` deterministically.  It is built entirely from
single-qubit unitaries (`gateTeleportCorrection_eq_tmul`) — resource #1 of Problem 4.6. -/
noncomputable def gateTeleportCorrection (p q : Fin 2 × Fin 2) : Evolution (qubit ⊗ qubit) :=
  (pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).adjoint

/-- **The correction is a tensor of two single-qubit gates.**
`gateTeleportCorrection p q = (X^{y₁}Z^{x₁+x₂})† ⊗ (X^{y₁+y₂}Z^{x₂})†`: the inverse of the byproduct
pair distributes over the tensor (`Evolution.adjoint_tmul`), so the correction acts as an
independent single-qubit `pauliByproduct` adjoint on each output qubit.  This certifies that the
correction lies in resource #1 of Problem 4.6 (single-qubit unitaries), not just that it is some
two-qubit gate. -/
theorem gateTeleportCorrection_eq_tmul (p q : Fin 2 × Fin 2) :
    gateTeleportCorrection p q =
      (pauliByproduct (p.1 + q.1) p.2).adjoint ⊗ (pauliByproduct q.1 (p.2 + q.2)).adjoint := by
  rw [gateTeleportCorrection, Evolution.adjoint_tmul]

/-- **The correction adjoint undoes the byproduct pair on *any* output vector `w`** (the workhorse):
the correction is `(C_A ⊗ C_B)†` and `U† (U w) = w` (`Evolution.adjoint_comp_self`), for a general
(possibly entangled) two-qubit input.  `gateTeleportCorrection_op_output` is the
`w := CNOT (q_A ⊗ q_B)` corollary. -/
theorem gateTeleportCorrection_op_output_apply (p q : Fin 2 × Fin 2) (w : (qubit ⊗ qubit).space) :
    (gateTeleportCorrection p q).op
        ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op w) = w := by
  unfold gateTeleportCorrection
  rw [Evolution.adjoint_op, ← ContinuousLinearMap.comp_apply, Evolution.adjoint_comp_self,
    one_apply_eq_self]

/-- **The correction recovers `CNOT` exactly.**  Applying `gateTeleportCorrection p q` to the
byproduct-corrupted output `(C_A ⊗ C_B)(CNOT (q_A ⊗ q_B))` of the collapse identity returns exactly
`CNOT (q_A ⊗ q_B)` — the `w := CNOT (q_A ⊗ q_B)` special case of
`gateTeleportCorrection_op_output_apply`.  The correction is the adjoint of the byproduct pair
`C_A ⊗ C_B`, and a gate preceded by its adjoint is the identity (`Evolution.adjoint_comp_self`,
`U† U = 1`), so the byproduct is undone with no residual phase. -/
theorem gateTeleportCorrection_op_output (qA qB : PureState qubit) (p q : Fin 2 × Fin 2) :
    (gateTeleportCorrection p q).op
        ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
          (cnotGate.op (qA.vec ⊗ₜ[ℂ] qB.vec)))
      = cnotGate.op (qA.vec ⊗ₜ[ℂ] qB.vec) :=
  gateTeleportCorrection_op_output_apply p q (cnotGate.op (qA.vec ⊗ₜ[ℂ] qB.vec))

set_option maxHeartbeats 1000000 in
-- `maxHeartbeats` bumped: the correction acts on the six-qubit composite system of the collapsed
-- protocol register (nested `TensorProduct`s with `QSystem`-projected instances), defeq-heavy.
/-- **The deterministic `CNOT` of gate teleportation, for a general input** (Nielsen & Chuang
Problem 4.6).  Bell-measuring the two co-located pairs of the register `gateTeleportRegisterGen ψ`
(outcome `(p, q)`) and then applying the outcome-determined single-qubit correction
`gateTeleportCorrection p q` to the output pair sends the register to
`¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ (CNOT ψ)`.  The output factor `CNOT ψ` **does not depend on the outcome**
`(p, q)`: on every one of the sixteen branches the two output qubits carry the *same* `CNOT ψ` once
the correction is applied.  So the resource set implements the `CNOT` gate deterministically on
*every* input `ψ`, grounded in the measurement postulates (Postulates 3/4). -/
theorem bellPairsMeasurement_corrected_op_gateTeleportRegisterGen (ψ : PureState (qubit ⊗ qubit))
    (p q : Fin 2 × Fin 2) :
    ((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).op
        ((bellPairsMeasurement.op (p, q)) (gateTeleportRegisterGen ψ).vec)
      = (4 : ℂ)⁻¹ • ((bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
          cnotGate.op ψ.vec) := by
  rw [bellPairsMeasurement_op_gateTeleportRegisterGen, Evolution.onRight]
  erw [map_smul, Evolution.tmul_op_tmul, Evolution.id_op, one_apply_eq_self,
    gateTeleportCorrection_op_output_apply]
  rfl

/-- **The deterministic `CNOT` of gate teleportation** for a product input (Nielsen & Chuang Problem
4.6): the `ψ = q_A ⊗ q_B` special case of
`bellPairsMeasurement_corrected_op_gateTeleportRegisterGen`, whose output factor is
`CNOT (q_A ⊗ q_B)`, independent of the outcome.  So the resource set
`{single-qubit unitaries, Bell-basis measurement, four-qubit state preparation}` implements the
`CNOT` gate deterministically.  Definitional special case (`gateTeleportResourceRegister qA qB =
gateTeleportRegisterGen (qA.tmul qB)` and `(qA.tmul qB).vec = qA.vec ⊗ₜ qB.vec`, both `rfl`). -/
theorem bellPairsMeasurement_corrected_op_gateTeleportResourceRegister
    (qA qB : PureState qubit) (p q : Fin 2 × Fin 2) :
    ((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).op
        ((bellPairsMeasurement.op (p, q)) (gateTeleportResourceRegister qA qB).vec)
      = (4 : ℂ)⁻¹ • ((bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
          cnotGate.op (qA.vec ⊗ₜ[ℂ] qB.vec)) :=
  bellPairsMeasurement_corrected_op_gateTeleportRegisterGen (qA.tmul qB) p q

end AxQM
