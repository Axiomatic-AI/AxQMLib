/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DoubleTeleportation
import AxQM.Postulates.API.GateTeleportResource
import AxQM.Postulates.API.Interchange

/-!
# AxQM.Postulates.API — the gate-teleportation ingredients (Problem 4.6)

The two structural facts that feed the Gottesman–Chuang **gate-teleportation identity** for `CNOT`
of Nielsen & Chuang **Problem 4.6** ("Universality with prior entanglement"), each a clean,
reusable unit; the identity itself is their assembly (see *Design notes / what remains*).

## Role in Problem 4.6

Problem 4.6 asks to show `{single-qubit unitaries, Bell-basis measurement, four-qubit state
preparation}` is universal, given `{CNOT, single-qubit gates}` is.  Since single-qubit gates are
shared, it suffices to implement `CNOT` by **gate teleportation**: the two input qubits `q_A, q_B`
are teleported through the four-qubit resource state `cnotGateTeleportResource` (a `CNOT`
pre-applied to two Bell pairs), so the pre-applied `CNOT` lands on the teleported inputs.  Two
facts assemble that protocol, and are what this file provides:

1. **the resource is `CNOT` applied to two Bell pairs**, as a genuine `Evolution` acting on the
   *literal* pair of Bell states — `cnotGateTeleportResource_eq_cnotOnOutputs`; and
2. **the two physical input qubits teleport in parallel through two Bell pairs** on the *physical*
   register `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` — `parallelTeleportation_natural`.

## What is formalised

* `cnotOnOutputs` — the `Evolution` `(q⊗q)⊗(q⊗q) → (q⊗q)⊗(q⊗q)` that applies `CNOT` to the two
  *output* halves `(a_out, b_out)` of the two Bell pairs, obtained by transporting the middle-pair
  `cnotMiddleGate` back along `gateTeleportReshape` (`Evolution.congr`).
* `cnotGateTeleportResource_eq_cnotOnOutputs` — the resource state as
  `cnotOnOutputs.evolvePure (|Φ⁺⟩ ⊗ |Φ⁺⟩)`: the four-qubit resource `|χ⟩` is exactly `CNOT` (on the
  output halves) applied to the literal two Bell pairs `bellPhiPlus ⊗ bellPhiPlus`.  This turns
  "`CNOT` applied to two Bell pairs" into a first-class `Evolution`-on-`PureState` fact — the form
  in which the assembly commutes the resource `CNOT` out onto the teleported outputs.
* `parallelTeleportation_natural` — the **two-qubit teleportation identity on the physical
  register**: re-shaping `(u ⊗ v) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` by the interchange braid into the two-setups
  register and then re-associating each setup,
  `(assoc ⊗ assoc)(interchange((u ⊗ v) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)))
  = ¼ Σ_{p,q} (|β_p⟩ ⊗ X^p u) ⊗ (|β_q⟩ ⊗ X^q v)`, with `X^p = X^{y₁}Z^{x₁}` the `pauliByproduct`.
  It is `double_teleportation_identity` (the two-setups form) precomposed with the interchange braid
  that moves the inputs-together physical register into the two-setups register.

## Design notes / what remains

* **The correction-free core, on the physical register.**  `double_teleportation_identity` lives on
  the *two-setups* register `(u ⊗ |Φ⁺⟩) ⊗ (v ⊗ |Φ⁺⟩)` (each input already beside its own Bell
  pair); `parallelTeleportation_natural` is its restatement on the *physical* register
  `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` — inputs together, Bell pairs together — via
  `QSystem.Iso.interchange` (Problem 4.6), whose pure-tensor action delivers the
  two-setups tensor exactly.
* **The assembly.**  The full gate-teleportation identity composes these two ingredients:
  substitute `cnotGateTeleportResource` for `|Φ⁺⟩ ⊗ |Φ⁺⟩` (fact 1 pulls the `CNOT` out as
  `cnotOnOutputs`), teleport (fact 2), and commute the pre-applied `CNOT` through the two
  `pauliByproduct` corrections via `cnotGate_comp_pauliByproduct_tmul` (the Clifford property,
  Problem 4.6) so the final corrections stay single-qubit.  Its one genuinely new obstacle is a
  reshape that regroups the two teleported **outputs** `a_out, b_out` — which land in *different*
  setups — into a single `qubit ⊗ qubit` factor for the resource `CNOT` to act on; that
  output-regrouping braid + the propagation is in `GateTeleportationIdentity.lean`.

The statement of N&C Problem 4.6 is in `AxQM/NC/Ch4/Problem4_6.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The two-qubit teleportation identity on the physical register** (Nielsen & Chuang Problem
4.6).  With the two input qubits `u, v` together and the two Bell pairs together —
`(u ⊗ v) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)`, the physical layout of the gate-teleportation protocol — the
interchange braid `QSystem.Iso.interchange` moves the register into the two independent
single-qubit teleportation setups `(u ⊗ |Φ⁺⟩) ⊗ (v ⊗ |Φ⁺⟩)`, and re-associating each setup gives
`(assoc ⊗ assoc)(interchange((u ⊗ v) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)))
= ¼ Σ_{p,q} (|β_p⟩ ⊗ X^{y₁}Z^{x₁} u) ⊗ (|β_q⟩ ⊗ X^{y₂}Z^{x₂} v)`,
`p = (x₁,y₁)`, `q = (x₂,y₂)`, `X^{y}Z^{x} = pauliByproduct x y`.  So Bell-measuring the two
`(input, ancilla)` pairs leaves the two outputs in `X^{y₁}Z^{x₁} u` and `X^{y₂}Z^{x₂} v`, each
undone by its own single-qubit `pauliByproduct`.  Proof: the interchange braid's pure-tensor action
delivers the two-setups tensor, then this is exactly `double_teleportation_identity`. -/
theorem parallelTeleportation_natural (u v : qubit.space) :
    (QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
        (QSystem.assoc qubit qubit qubit)).toIsometry
        ((QSystem.Iso.interchange qubit qubit (qubit ⊗ qubit) (qubit ⊗ qubit)).toIsometry
          ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec)))
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] (pauliByproduct p.1 p.2).op u) ⊗ₜ[ℂ]
            (bellBasisVec q.1 q.2 ⊗ₜ[ℂ] (pauliByproduct q.1 q.2).op v) := by
  rw [QSystem.Iso.interchange_toIsometry_tmul_tmul]
  exact double_teleportation_identity u v

/-- **`CNOT` on the two output halves of the resource system**, as an `Evolution`
`(q⊗q)⊗(q⊗q) → (q⊗q)⊗(q⊗q)`.  In the register `(a_in a_out) ⊗ (b_out b_in)` it applies `CNOT` with
control `a_out` and target `b_out` (the two *output* halves), obtained by transporting the
middle-pair gate `cnotMiddleGate` back along `gateTeleportReshape` (`Evolution.congr`), i.e. the
`Evolution` whose `evolvePure` of two Bell pairs is the gate-teleportation resource state. -/
def cnotOnOutputs : Evolution ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) :=
  Evolution.congr gateTeleportReshape.symm cnotMiddleGate

/-- **The gate-teleportation resource is `CNOT` applied to two Bell pairs.**  The four-qubit
resource state `cnotGateTeleportResource` (`|χ⟩`) equals `cnotOnOutputs.evolvePure (|Φ⁺⟩ ⊗ |Φ⁺⟩)`:
the genuine output-halves `CNOT` `Evolution` (`cnotOnOutputs`, Postulate 5) applied to the *literal*
pair of Bell states `bellPhiPlus ⊗ bellPhiPlus`.  This restates the resource's definition (a
transport–evolve–transport around `gateTeleportReshape`) as a single unitary acting on two Bell
pairs, the form in which the gate-teleportation identity commutes the resource `CNOT` out onto the
teleported outputs.  Proof: both sides' vectors reduce, via `Evolution.congr_op` /
`conjStarAlgEquiv_apply_apply` on the right and the `PureState.congr` / `evolvePure` unfoldings on
the left, to `R⁻¹(CNOT_mid(R(|Φ⁺⟩ ⊗ |Φ⁺⟩)))` with `R = gateTeleportReshape`. -/
theorem cnotGateTeleportResource_eq_cnotOnOutputs :
    cnotGateTeleportResource = cnotOnOutputs.evolvePure (bellPhiPlus.tmul bellPhiPlus) := by
  apply PureState.ext
  rw [cnotOnOutputs, Evolution.evolvePure_vec, Evolution.congr_op, PureState.tmul_vec]
  have hconj := LinearIsometryEquiv.conjStarAlgEquiv_apply_apply gateTeleportReshape.symm.toIsometry
    cnotMiddleGate.op (bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec)
  rw [hconj, QSystem.Iso.symm_toIsometry,
    LinearIsometryEquiv.symm_symm, cnotGateTeleportResource, PureState.congr_vec,
    Evolution.evolvePure_vec, PureState.congr_vec, PureState.tmul_vec, QSystem.Iso.symm_toIsometry]

end AxQM
