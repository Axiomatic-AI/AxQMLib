/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportProtocolCnot
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# AxQM.Postulates.API — the CNOT gate-teleportation identity (assembly)

The **Gottesman–Chuang gate-teleportation identity for `CNOT`** of Nielsen & Chuang **Problem 4.6**
("Universality with prior entanglement") — the assembly of the ingredients built in the
preceding files into the single identity that establishes the universality of the resource set.

## Role in Problem 4.6

Problem 4.6 asks to show that `{single-qubit unitaries, Bell-basis measurement, four-qubit state
preparation}` is a universal set of resources, given that `{CNOT, single-qubit gates}` is.  Since
single-qubit gates are shared, it suffices to implement `CNOT` from the new resources — which is
done by **gate teleportation**: the two input qubits `q_A, q_B` are teleported through the
four-qubit resource state `cnotGateTeleportResource` (`|χ⟩`, a `CNOT` pre-applied to the two
*output* halves of two Bell pairs), the two Bell-measured pairs are `(q_A, a_in)` and `(q_B, b_in)`,
and the pre-applied `CNOT` — because it sits on the two output halves — lands on the teleported
result.  This file combines the pieces already established into the full identity.

## What is formalised

* `gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport` — the **correction-free
  teleportation form of the bare protocol-reshaped register**:
  `reshape ((q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩))
  = ¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ (X^{p} q_A ⊗ X^{q} q_B)`,
  with `X^{p} = X^{y₁}Z^{x₁} = pauliByproduct p.1 p.2`.  Bell-measuring the two co-located measured
  pairs `(q_A, a_in)`, `(q_B, b_in)` (outcomes `p, q`) leaves the two output halves `a_out, b_out`
  in `X^{p} q_A`, `X^{q} q_B` — the two independent single-qubit teleportations, laid out with the
  two outputs co-located on the right (where the resource `CNOT` acts).

* `cnotGateTeleportation_identity` — the **CNOT gate-teleportation identity** (the universality
  core): with the input qubits teleported through the resource `|χ⟩`,
  `reshape ((q_A ⊗ q_B) ⊗ |χ⟩)
  = ¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ ((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT (q_A ⊗ q_B)))`,
  `p = (x₁,y₁)`, `q = (x₂,y₂)`.  So Bell-measuring the two pairs (outcomes `p, q`) yields — on the
  two output qubits — a single `CNOT` applied to the inputs `q_A, q_B`, up to a **pair of
  single-qubit Pauli corrections** `pauliByproduct (p.1+q.1) p.2` and `pauliByproduct q.1 (p.2+q.2)`
  that depend only on the measurement outcomes.  Because those corrections are single-qubit
  unitaries (`pauliByproduct`), the protocol implements `CNOT` using only the resource set's
  operations — which is exactly why `{single-qubit unitaries, Bell-basis measurement, four-qubit
  state preparation}` is universal.

## Design notes

* **The assembly route (uses the operator-form resource `CNOT`).**  The identity composes three
  established facts, all in the `gateTeleportProtocolReshape` family:
  1. `cnotGateTeleportResource_protocolReshape_eq_cnotOnRight` (the operator form of the resource
     `CNOT`, `Postulates/API/GateTeleportProtocolCnot.lean`): after the reshape, the resource
     register is a single `cnotGate.onRight` of the *bare* two-Bell-pair register;
  2. `gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport` (below): that bare register, in
     Bell-teleportation form;
  3. `cnotGate_comp_pauliByproduct_tmul` (the Clifford propagation,
     `Postulates/API/CnotPauliPropagation.lean`): `CNOT` on the two corrected outputs commutes back
     through the two teleportation corrections, keeping them single-qubit.
  This is a revision of the originally-planned fold-in (which pulled the resource `CNOT` out as
  `cnotOnOutputs` and transported it through the reshape by a composite-iso conjugation): the
  operator form (1) already *is* the transported `CNOT`, so the conjugation step is unneeded.

* **The bare Bell form bridges the two reshape layouts.**  `gateTeleportProtocolReshape` co-locates
  the two teleported *outputs* on the right, whereas `double_teleportation_identity` /
  `parallelTeleportation_natural` produce the two teleportations with their outputs *split* across
  the two setups `(|β_p⟩ ⊗ X^{p} q_A) ⊗ (|β_q⟩ ⊗ X^{q} q_B)`.  The two layouts are related by one
  output-regrouping interchange braid `J = QSystem.Iso.interchange (q⊗q) q (q⊗q) q`, which sends
  `(|β_p⟩ ⊗ X^{p} q_A) ⊗ (|β_q⟩ ⊗ X^{q} q_B) ↦ (|β_p⟩ ⊗ |β_q⟩) ⊗ (X^{p} q_A ⊗ X^{q} q_B)`.  On the
  *specific* vector `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` the two composites `gateTeleportProtocolReshape`
  and `J ∘ (assoc ⊗ assoc) ∘ interchange` agree (they differ only by the ordering of the second Bell
  pair's two halves, which washes out because `|Φ⁺⟩` is expanded diagonally over the computational
  basis); this is `hkey`, proved by expanding `|Φ⁺⟩ ⊗ |Φ⁺⟩` over the basis and firing each reshape's
  pure-tensor action per summand — both reduce to `½ Σ_{i,j} ((q_A ⊗ |i⟩) ⊗ (q_B ⊗ |j⟩)) ⊗ (|i⟩ ⊗
  |j⟩)`.  As in `GateTeleportResourceCnot.lean`, the composite `J ∘ (assoc ⊗ assoc) ∘ interchange`
  is bundled as a single `ℂ`-linear map `φ` so `map_smul`/`map_sum` distribute past the
  composite-system module-instance diamond that blocks the generic `TensorProduct` lemmas.

The statement of N&C Problem 4.6 (the protocol, plus the universality annotation) is in
`AxQM/NC/Ch4/Problem4_6.lean`. -/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

set_option maxHeartbeats 1000000 in
-- The `change`/`rfl` through the deeply nested transport-iso composite `φ` (two `interchange`
-- braids over composite systems plus `assoc ⊗ assoc`) exceeds the default heartbeat budget; the
-- elaboration is pure `QSystem.Iso` data, not proof search.
/-- **The correction-free teleportation form of the bare protocol-reshaped register** (Nielsen &
Chuang Problem 4.6).  For arbitrary input qubits `q_A, q_B`, the protocol reshape of the bare
two-Bell-pair register is
`reshape ((q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)) = ¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ (X^{p} q_A ⊗ X^{q} q_B)`,
with `X^{p} = pauliByproduct p.1 p.2` the Pauli byproduct.  Bell-measuring the two co-located
measured pairs `(q_A, a_in)` and `(q_B, b_in)` (outcomes `p, q`) leaves the two output halves in
`X^{p} q_A`, `X^{q} q_B` — the two independent single-qubit teleportations, laid out with the
outputs co-located on the right (where the resource `CNOT` acts).

Proof: the composite `gateTeleportProtocolReshape` and `J ∘ (assoc ⊗ assoc) ∘ interchange`
(`J = QSystem.Iso.interchange (q⊗q) q (q⊗q) q` the output-regrouping braid) agree on
`(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` — both reduce, on the diagonal basis expansion of `|Φ⁺⟩ ⊗ |Φ⁺⟩`, to
`½ Σ_{i,j} ((q_A ⊗ |i⟩) ⊗ (q_B ⊗ |j⟩)) ⊗ (|i⟩ ⊗ |j⟩)` (`hkey`); then
`parallelTeleportation_natural` teleports both inputs into the split-output form, and `J` regroups
the two outputs together. -/
theorem gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport (qA qB : qubit.space) :
    gateTeleportProtocolReshape.toIsometry
        ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] (bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec))
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
            ((pauliByproduct p.1 p.2).op qA ⊗ₜ[ℂ] (pauliByproduct q.1 q.2).op qB) := by
  -- `hkey`: on this vector, `gateTeleportProtocolReshape` equals the output-regrouping braid `J`
  -- applied to the two-setups (parallel-teleportation) reshape.  Both reduce to
  -- `½ Σ_p ((q_A ⊗ |p.1⟩) ⊗ (q_B ⊗ |p.2⟩)) ⊗ (|p.1⟩ ⊗ |p.2⟩)`.
  have hkey : gateTeleportProtocolReshape.toIsometry
        ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] (bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec))
      = (QSystem.Iso.interchange (qubit ⊗ qubit) qubit (qubit ⊗ qubit) qubit).toIsometry
          ((QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
              (QSystem.assoc qubit qubit qubit)).toIsometry
            ((QSystem.Iso.interchange qubit qubit (qubit ⊗ qubit) (qubit ⊗ qubit)).toIsometry
              ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] (bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec)))) := by
    -- expand both registers over the computational basis (LHS and RHS's `|Φ⁺⟩⊗|Φ⁺⟩`), then
    -- bundle `J ∘ (assoc ⊗ assoc) ∘ interchange ∘ ((q_A ⊗ q_B) ⊗ ·)` as one `ℂ`-linear map `φ`, so
    -- `map_smul`/`map_sum` distribute past the composite-system module-instance diamond.
    rw [gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_vec, bellPhiPlus_tmul_bellPhiPlus_vec]
    set φ : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →ₗ[ℂ]
        (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)).space :=
      (QSystem.Iso.interchange (qubit ⊗ qubit) qubit (qubit ⊗ qubit)
            qubit).toIsometry.toLinearMap.comp
        (((QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
              (QSystem.assoc qubit qubit qubit)).toIsometry.toLinearMap.comp
            ((QSystem.Iso.interchange qubit qubit (qubit ⊗ qubit)
                (qubit ⊗ qubit)).toIsometry.toLinearMap.comp
              (TensorProduct.mk ℂ (qubit ⊗ qubit).space
                ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space (qA ⊗ₜ[ℂ] qB))))) with hφ
    change _ = φ ((2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
      ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ]
        ((qubitBasis p.2).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec))
    -- distribute `φ` over the scalar/sum by unification (`rw` cannot resolve the hom class on `φ`)
    refine Eq.symm ((map_smul φ (2 : ℂ)⁻¹ _).trans ?_)
    refine congrArg (fun z => (2 : ℂ)⁻¹ • z)
      ((map_sum φ _ _).trans (Finset.sum_congr rfl (fun p _ => ?_)))
    -- `φ (g_p)` is defeq to the three-reshape composite on `(q_A ⊗ q_B) ⊗ g_p` (unfolds `φ`, the
    -- coercions and `TensorProduct.mk`); expose that form with `change`, then fire the pure-tensor
    -- action lemmas of the three reshapes in turn.
    change (QSystem.Iso.interchange (qubit ⊗ qubit) qubit (qubit ⊗ qubit) qubit).toIsometry
        ((QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
            (QSystem.assoc qubit qubit qubit)).toIsometry
          ((QSystem.Iso.interchange qubit qubit (qubit ⊗ qubit) (qubit ⊗ qubit)).toIsometry
            ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ]
              (((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ]
                ((qubitBasis p.2).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec))))) = _
    -- fire the outer interchange braid's action; the remaining backbone isos (`assoc ⊗ assoc`, the
    -- co-locating interchange) compute definitionally on the pure tensor (`rfl`), as in
    -- `gateTeleportProtocolReshape_toIsometry_tmul`.
    have h := QSystem.Iso.interchange_toIsometry_tmul_tmul qubit qubit (qubit ⊗ qubit)
      (qubit ⊗ qubit) qA qB
      ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.1).vec)
      ((qubitBasis p.2).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec)
    rw [h]
    rfl
  rw [hkey, parallelTeleportation_natural]
  -- push the braid `J` through the `¼ Σ_p Σ_q` by unification (`rw` cannot match the composite-
  -- system `•`/`Σ` under the isometry coercion), regrouping the outputs per summand.
  refine (map_smul _ (4 : ℂ)⁻¹ _).trans ?_
  refine congrArg (fun z => (4 : ℂ)⁻¹ • z) ?_
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun p _ => ?_))
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun q _ => ?_))
  exact QSystem.Iso.interchange_toIsometry_tmul_tmul (qubit ⊗ qubit) qubit (qubit ⊗ qubit) qubit
    (bellBasisVec p.1 p.2) ((pauliByproduct p.1 p.2).op qA) (bellBasisVec q.1 q.2)
    ((pauliByproduct q.1 q.2).op qB)

set_option maxHeartbeats 800000 in
-- Distributing `cnotGate.onRight` over the reshaped register's `¼ Σ Σ` and commuting it through the
-- byproduct corrections over the nested six-qubit composite exceeds the default heartbeat budget.
/-- **The CNOT gate-teleportation identity** (Nielsen & Chuang Problem 4.6, the universality core).
Teleporting the two input qubits `q_A, q_B` through the four-qubit gate-teleportation resource state
`cnotGateTeleportResource` (`|χ⟩`) implements a `CNOT`:
`reshape ((q_A ⊗ q_B) ⊗ |χ⟩)
= ¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ ((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT (q_A ⊗ q_B)))`,
`p = (x₁,y₁)`, `q = (x₂,y₂)`.  Bell-measuring the two co-located pairs (outcomes `p, q`) yields, on
the two output qubits, a single `CNOT` applied to the inputs — up to a pair of **single-qubit**
Pauli corrections `pauliByproduct (p.1+q.1) p.2` (control) and `pauliByproduct q.1 (p.2+q.2)`
(target) determined by the outcomes.  Since the corrections are single-qubit unitaries, the protocol
implements `CNOT` from `{single-qubit unitaries, Bell-basis measurement, four-qubit state
preparation}`, which — with single-qubit gates shared — is exactly the universality claim of
Problem 4.6.

Proof: rewrite the resource register by its operator form
(`cnotGateTeleportResource_protocolReshape_eq_cnotOnRight`) — a single `cnotGate.onRight` of
the bare register — then by the bare Bell-teleportation form
(`gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport`); distribute the output `CNOT` over
the `¼ Σ` (`Evolution.op` is a continuous linear map) and hit the co-located outputs
(`Evolution.onRight_op_tmul`); finally commute the `CNOT` back through the two teleportation
corrections via the Clifford propagation `cnotGate_comp_pauliByproduct_tmul`, which keeps them
single-qubit. -/
theorem cnotGateTeleportation_identity (qA qB : qubit.space) :
    gateTeleportProtocolReshape.toIsometry
        ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] cnotGateTeleportResource.vec)
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
            ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
              (cnotGate.op (qA ⊗ₜ[ℂ] qB))) := by
  rw [cnotGateTeleportResource_protocolReshape_eq_cnotOnRight,
    gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport]
  -- distribute the output `CNOT` over the outer `¼ Σ_p` (`Evolution.op` is a continuous linear
  -- map); `rw` cannot infer the higher-order summand `g`, so apply the distributor by unification.
  refine (Evolution.op_smul_sum _ (4 : ℂ)⁻¹ _).trans ?_
  refine congrArg (fun z => (4 : ℂ)⁻¹ • z) (Finset.sum_congr rfl (fun p _ => ?_))
  -- distribute over the inner `Σ_q`, then act on the co-located outputs (both by unification, as
  -- `rw` cannot match the composite-system `Σ`/`⊗ₜ` under the operator coercion)
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun q _ => ?_))
  refine (Evolution.onRight_op_tmul cnotGate ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))
    (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2)
    ((pauliByproduct p.1 p.2).op qA ⊗ₜ[ℂ] (pauliByproduct q.1 q.2).op qB)).trans ?_
  refine congrArg (fun w => (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ] w) ?_
  -- commute the output `CNOT` back through the two teleportation corrections (Clifford propagation)
  rw [← Evolution.tmul_op_tmul]
  erw [← ContinuousLinearMap.comp_apply]
  rw [← Evolution.comp_op, cnotGate_comp_pauliByproduct_tmul]
  erw [Evolution.comp_op, ContinuousLinearMap.comp_apply]

end AxQM
