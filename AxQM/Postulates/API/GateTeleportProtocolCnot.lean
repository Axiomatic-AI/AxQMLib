/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportResourceCnot

/-!
# AxQM.Postulates.API — the resource `CNOT` on the reshaped register, in operator form

The **operator restatement** of the gate-teleportation resource's pre-applied `CNOT`, for Nielsen &
Chuang **Problem 4.6** ("Universality with prior entanglement").  On the protocol-reshaped register
with *arbitrary* two-qubit inputs `q_A, q_B`, the resource register `(q_A ⊗ q_B) ⊗ |χ⟩` equals a
single `cnotGate` — applied to the two co-located teleported outputs — of the correction-free bare
register `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)`:

`reshape ((q_A ⊗ q_B) ⊗ |χ⟩) = (cnotGate.onRight _) (reshape ((q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)))`.

## Role in Problem 4.6

Gate teleportation implements a `CNOT` (the missing two-qubit gate; single-qubit gates are shared)
from `{single-qubit unitaries, Bell-basis measurement, four-qubit state preparation}`.  The two
input qubits `q_A, q_B` are teleported through the four-qubit resource `cnotGateTeleportResource`
(`|χ⟩`, a `CNOT` pre-applied to the two *output* halves of two Bell pairs); the protocol reshape
`gateTeleportProtocolReshape` blocks the two Bell-measured pairs `(q_A, a_in)`, `(q_B, b_in)` on the
left and co-locates the two output halves `a_out, b_out` on the right.

`AxQM/Postulates/API/GateTeleportProtocolReshape.lean` proves, *on the computational basis*
(`gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis`), that the resource `CNOT` transports
through the reshape to `cnotGate` on the co-located output factor.
`AxQM/Postulates/API/GateTeleportResourceCnot.lean` lifts the two register layouts to explicit
basis-sum form for arbitrary inputs (`cnotGateTeleportResource_protocolReshape_vec` and its bare
counterpart), reading the pre-applied `CNOT` off as `|j⟩ ↦ |i ⊕ j⟩` on the output factor.  This file
combines the two: it restates that difference as one honest `cnotGate.onRight` `Evolution` acting on
the bare register — the **operator** form, for arbitrary `q_A, q_B`.  It is the form in which the
byproduct-propagation assembly commutes the resource `CNOT` out through the teleportation
corrections (`cnotGate_comp_pauliByproduct_tmul`).

## What is formalised

* `cnotGateTeleportResource_protocolReshape_eq_cnotOnRight` — the **operator restatement**:
  `reshape ((q_A ⊗ q_B) ⊗ |χ⟩) = (cnotGate.onRight ((q⊗q)⊗(q⊗q))) (reshape ((q_A ⊗ q_B) ⊗
  (|Φ⁺⟩ ⊗ |Φ⁺⟩)))`, for arbitrary input qubits `q_A, q_B`.  The state-level lift of
  `gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis` (which is the same identity restricted to
  computational-basis inputs).

## Design notes

* **Route via the two explicit forms, not the operator conjugation.**  Both reshaped registers are
  already known as explicit basis sums (`GateTeleportResourceCnot.lean`), differing only in the
  co-located output factor (`|i⟩ ⊗ |j⟩` bare vs. `|i⟩ ⊗ |i ⊕ j⟩` resource).  Applying
  `cnotGate.onRight` to the bare sum term by term — `Evolution.onRight_op_tmul` puts the `cnotGate`
  on the output factor, then the truth table `cnotGate.op (|i⟩ ⊗ |j⟩) = |i⟩ ⊗ |j ⊕ i⟩`
  (`cnotGate_op_qubitBasisVec_tmul`) matches the resource form (`add_comm` reconciles `j ⊕ i` with
  `i ⊕ j`).  This avoids restating the transport as an `Evolution` equality over the nested
  six-qubit composite `((q⊗q)⊗(q⊗q))⊗(q⊗q)`, for which no extensionality lemma exists (noted in
  `GateTeleportProtocolReshape.lean`).
* **Distributing the output `CNOT` over the scalar/sum, generically.**  Pushing
  `(cnotGate.onRight _).op` through the bare register's `½ Σ …` needs `map_smul`/`map_sum` of the
  `Evolution.op` continuous linear map.  This is a general fact about *any* `Evolution.op` — nothing
  about `cnotGate` or the six-qubit composite — so it is the general `Evolution.op_smul_sum`
  (`AxQM/Postulates/API/Evolution.lean`), which is proved by `rw [map_smul, map_sum]` on the
  abstract space `S.space` (its module is an opaque instance there, so no composite `•`/`Σ`
  module-instance diamond arises and no `toLinearMap` bundling / heartbeat bump is needed).  It is a
  reusable lemma of the Evolution API.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The resource `CNOT`, in operator form on the reshaped register** (Nielsen & Chuang Problem
4.6).  For arbitrary input qubits `q_A, q_B`, the protocol reshape of the resource register equals a
single `cnotGate`, applied to the co-located output factor, of the protocol reshape of the bare
two-Bell-pair register:
`reshape ((q_A ⊗ q_B) ⊗ |χ⟩) = (cnotGate.onRight ((q⊗q)⊗(q⊗q))) (reshape ((q_A ⊗ q_B) ⊗
(|Φ⁺⟩ ⊗ |Φ⁺⟩)))`.  Since `|χ⟩` is `|Φ⁺⟩ ⊗ |Φ⁺⟩` with a `CNOT` pre-applied to the two output halves,
and the reshape co-locates those halves as the right factor, the whole difference between the two
reshaped registers is exactly one `cnotGate` there — the geometric heart of gate teleportation, now
as an honest `Evolution` acting on the correction-free register, for arbitrary inputs (the
state-level lift of `gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis`).  Proof: rewrite both
registers by their explicit basis sums (`cnotGateTeleportResource_protocolReshape_vec`,
`gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_vec`), distribute the output `CNOT` over the
scalar/sum (the general `Evolution.op_smul_sum`), and match term by term via
`Evolution.onRight_op_tmul` and the `CNOT` truth table `cnotGate.op (|i⟩ ⊗ |j⟩) = |i⟩ ⊗ |j ⊕ i⟩`
(`add_comm` reconciling `j ⊕ i` with the resource form's `i ⊕ j`). -/
theorem cnotGateTeleportResource_protocolReshape_eq_cnotOnRight (qA qB : qubit.space) :
    gateTeleportProtocolReshape.toIsometry ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] cnotGateTeleportResource.vec)
      = (cnotGate.onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).op
          (gateTeleportProtocolReshape.toIsometry
            ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] (bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec))) := by
  rw [cnotGateTeleportResource_protocolReshape_vec,
    gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_vec]
  -- `rw` cannot match the higher-order pattern `Σᵢ ?g i` / infer the index type in `op_smul_sum`,
  -- so apply it by unification (`.trans`); `g` is fixed by the output factor per summand.
  refine Eq.symm ((Evolution.op_smul_sum _ (2 : ℂ)⁻¹ _).trans ?_)
  refine congrArg (fun z => (2 : ℂ)⁻¹ • z) (Finset.sum_congr rfl (fun p _ => ?_))
  refine (Evolution.onRight_op_tmul cnotGate ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))
    ((qA ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ] (qB ⊗ₜ[ℂ] (qubitBasis p.2).vec))
    ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec)).trans ?_
  rw [cnotGate_op_qubitBasisVec_tmul, add_comm p.2 p.1]
  -- both sides are now the same value; `rfl` (default transparency) bridges the composite-space
  -- `⊗ₜ` instance diamond that the rewrite's reducible `rfl` leaves open.
  rfl

end AxQM
