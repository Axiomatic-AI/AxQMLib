/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportProtocolReshape

/-!
# AxQM.Postulates.API — the reshaped register with arbitrary inputs

The **protocol-reshaped gate-teleportation register with arbitrary two-qubit input**, of Nielsen &
Chuang **Problem 4.6** ("Universality with prior entanglement"): laying out the six-qubit registers
`(q_A ⊗ q_B) ⊗ |χ⟩` (resource) and `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` (bare) through the protocol
reshape, in explicit computational-basis form, for *arbitrary* input qubits `q_A, q_B` — not just
basis states.  Comparing the two exhibits the resource's pre-applied `CNOT` directly.

## Role in Problem 4.6

Gate teleportation implements a `CNOT` (the missing two-qubit gate; single-qubit gates are shared)
from `{single-qubit unitaries, Bell-basis measurement, four-qubit state preparation}`.  The two
input qubits `q_A, q_B` are teleported through the four-qubit resource `cnotGateTeleportResource`
(`|χ⟩`, a `CNOT` pre-applied to the two *output* halves of two Bell pairs); the physical register
`(q_A ⊗ q_B) ⊗ ((a_in ⊗ a_out) ⊗ (b_out ⊗ b_in))` is regrouped by `gateTeleportProtocolReshape` so
the two Bell-measured pairs `(q_A, a_in)`, `(q_B, b_in)` block on the left and the two output halves
`a_out, b_out` co-locate on the right, where the resource `CNOT` acts.

`AxQM/Postulates/API/GateTeleportProtocolReshape.lean` proves the reshape's geometry — that the
resource `CNOT` transports through the reshape to `cnotGate` on the co-located output factor — *on
the computational basis* (`gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis`, all six labels
basis states).  This
file lifts the layout to the **actual resource state** `|χ⟩` and **arbitrary input qubits**
`q_A, q_B`, giving the reshaped register as an explicit basis sum in which the pre-applied `CNOT` is
visible as the truth table on the co-located output halves.  These are the concrete state the
byproduct-propagation assembly consumes.

## What is formalised

* `gateTeleportProtocolReshape_toIsometry_tmul_smul_sum` — the **scalar/sum linearity bridge** for
  the protocol reshape: `reshape (x ⊗ (c • Σᵢ g i)) = c • Σᵢ reshape (x ⊗ g i)`.  The shared
  distributor (crossing the composite module-instance diamond once) that both explicit-form
  lemmas below — and the byproduct-propagation assembly — reuse.
* `gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_vec` — the reshape of the **correction-free**
  register `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` (the two bare Bell pairs, no resource `CNOT`):
  `reshape ((q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)) = ½ Σ_{i,j} ((q_A ⊗ |i⟩) ⊗ (q_B ⊗ |j⟩)) ⊗ (|i⟩ ⊗ |j⟩)`.
  Each summand blocks the two measured pairs `(q_A, |i⟩) = (q_A, a_in)`, `(q_B, |j⟩) = (q_B, b_in)`
  on the left and the two Bell-output halves `a_out = |i⟩`, `b_out = |j⟩` on the right.
* `cnotGateTeleportResource_protocolReshape_vec` — the reshape of the **resource** register
  `(q_A ⊗ q_B) ⊗ |χ⟩`:
  `reshape ((q_A ⊗ q_B) ⊗ |χ⟩) = ½ Σ_{i,j} ((q_A ⊗ |i⟩) ⊗ (q_B ⊗ |j⟩)) ⊗ (|i⟩ ⊗ |i ⊕ j⟩)`.
  Identical to the bare register except the right output factor is `(|i⟩ ⊗ |i ⊕ j⟩)` instead of
  `(|i⟩ ⊗ |j⟩)`: the `CNOT` truth table `(a_out, b_out) = (|i⟩, |j⟩) ↦ (|i⟩, |i ⊕ j⟩)`, exactly the
  resource's pre-applied `CNOT` on the co-located output halves.  So `|χ⟩` versus `|Φ⁺⟩ ⊗ |Φ⁺⟩`
  differ, after the reshape, by exactly a `cnotGate` on the co-located output factor — the geometric
  heart of gate teleportation, read off the two explicit forms.

## Design notes

* **Basis-to-state lift.**  The reshape's pure-tensor action
  `gateTeleportProtocolReshape_toIsometry_tmul` already holds for *arbitrary* vectors in all six
  slots, so the input qubits `q_A, q_B` need no basis restriction.  Only the four resource qubits
  are expanded over the computational basis — via the explicit forms `cnotGateTeleportResource_vec`
  (`|χ⟩ = ½ Σ (|i⟩|i⟩)⊗(|i⊕j⟩|j⟩)`) and `bellPhiPlus_tmul_bellPhiPlus_vec`
  (`|Φ⁺⟩⊗|Φ⁺⟩ = ½ Σ (|i⟩|i⟩)⊗(|j⟩|j⟩)`) — after which the reshape action fires per summand.  This
  route reads the `CNOT` off the explicit forms directly (the `|i ⊕ j⟩` in the resource form vs.
  `|j⟩` in the bare form), bypassing the basis lemma
  `gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis` and the `cnotOnOutputs` `Evolution`.
  Lifting these to the operator restatement
  `reshape (…|χ⟩) = cnotGate.onRight (reshape (…|Φ⁺⟩⊗|Φ⁺⟩))` is in
  `AxQM/Postulates/API/GateTeleportProtocolCnot.lean`, where `cnotGate.onRight` distributes over the
  explicit sum term by term.
* **The composite `•`/`Σ` diamond, factored out once.**  On a composite system the
  `⊗ₜ`/`•`/`+` go through the inner-product-space module instance, *defeq but not syntactically
  equal* to `TensorProduct`'s canonical module (documented throughout
  `GateTeleportResourceExplicit.lean` / `DoubleTeleportation.lean`), so the generic `TensorProduct`
  `rw`/`simp` lemmas do not distribute `reshape ((q_A ⊗ q_B) ⊗ (½ Σ …))` directly.  Bundling
  `y ↦ reshape ((q_A ⊗ q_B) ⊗ y)` as a single `ℂ`-linear map lets `map_smul`/`map_sum` pull the
  scalar and sum out cleanly over the bundled map's own (composite) module.  This bundling is
  extracted once as `gateTeleportProtocolReshape_toIsometry_tmul_smul_sum` (rather than re-inlined
  per proof, the `cnotGateTeleportResource_vec` idiom); each explicit-form lemma then just expands
  and applies it via `.trans` (unification solves the `Σᵢ ?g i` binder that a bare `rw` cannot).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

set_option maxHeartbeats 1000000 in
-- The `change` unifies the bundled map through the deeply nested `gateTeleportProtocolReshape`
-- (whose own `def` needs the same budget); the elaboration is pure iso data, not proof search.
/-- **Scalar/sum linearity bridge for the protocol reshape.**  For an arbitrary left factor `x`, a
scalar `c`, and a family `g` of four-qubit resource vectors,
`reshape (x ⊗ (c • Σᵢ g i)) = c • Σᵢ reshape (x ⊗ g i)`.  Bundling `y ↦ reshape (x ⊗ y)` as a single
`ℂ`-linear map crosses the composite `⊗ₜ`/`•`/`Σ` module-instance diamond (*defeq but not
syntactically equal* to `TensorProduct`'s canonical module, documented across
`GateTeleportResourceExplicit.lean` / `DoubleTeleportation.lean`), which otherwise blocks the
generic `TensorProduct` `rw`/`simp` lemmas — so `map_smul`/`map_sum` distribute over the bundled
map's own module.  The shared distributor the two explicit-form lemmas below (and the
byproduct-propagation assembly) reuse, rather than re-inlining the bundling per proof. -/
theorem gateTeleportProtocolReshape_toIsometry_tmul_smul_sum {ι : Type*} [Fintype ι]
    (x : (qubit ⊗ qubit).space) (c : ℂ)
    (g : ι → ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space) :
    gateTeleportProtocolReshape.toIsometry (x ⊗ₜ[ℂ] (c • ∑ i, g i))
      = c • ∑ i, gateTeleportProtocolReshape.toIsometry (x ⊗ₜ[ℂ] g i) := by
  set φ : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →ₗ[ℂ]
      (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)).space :=
    gateTeleportProtocolReshape.toIsometry.toLinearMap.comp
      (TensorProduct.mk ℂ (qubit ⊗ qubit).space ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space x) with hφ
  change φ (c • ∑ i, g i) = c • ∑ i, φ (g i)
  rw [map_smul, map_sum]

/-- **The protocol reshape of the bare two-Bell-pair register** with arbitrary inputs (Nielsen &
Chuang Problem 4.6): `reshape ((q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)) = ½ Σ_{i,j} ((q_A ⊗ |i⟩) ⊗ (q_B ⊗ |j⟩))
⊗ (|i⟩ ⊗ |j⟩)`.  Expanding the two Bell pairs `|Φ⁺⟩ ⊗ |Φ⁺⟩ = ½ Σ (|i⟩|i⟩)⊗(|j⟩|j⟩)` over the
computational basis (`bellPhiPlus_tmul_bellPhiPlus_vec`) and firing the reshape's pure-tensor action
per summand blocks the two measured pairs `(q_A, a_in = |i⟩)`, `(q_B, b_in = |j⟩)` on the left and
co-locates the two Bell-output halves `a_out = |i⟩`, `b_out = |j⟩` on the right — the layout that
carries no resource `CNOT`.  Proof: expand, distribute the scalar/sum through the reshape with the
`gateTeleportProtocolReshape_toIsometry_tmul_smul_sum` bridge, then the reshape action per term. -/
theorem gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_vec (qA qB : qubit.space) :
    gateTeleportProtocolReshape.toIsometry
        ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] (bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec))
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          ((qA ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ] (qB ⊗ₜ[ℂ] (qubitBasis p.2).vec)) ⊗ₜ[ℂ]
            ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec) := by
  rw [bellPhiPlus_tmul_bellPhiPlus_vec]
  refine (gateTeleportProtocolReshape_toIsometry_tmul_smul_sum (qA ⊗ₜ[ℂ] qB) (2 : ℂ)⁻¹ _).trans ?_
  refine congrArg (fun z => (2 : ℂ)⁻¹ • z) (Finset.sum_congr rfl (fun p _ => ?_))
  exact gateTeleportProtocolReshape_toIsometry_tmul qA qB (qubitBasis p.1).vec (qubitBasis p.1).vec
    (qubitBasis p.2).vec (qubitBasis p.2).vec

/-- **The protocol reshape of the resource register** with arbitrary inputs (Nielsen & Chuang
Problem 4.6): `reshape ((q_A ⊗ q_B) ⊗ |χ⟩) = ½ Σ_{i,j} ((q_A ⊗ |i⟩) ⊗ (q_B ⊗ |j⟩)) ⊗ (|i⟩ ⊗ |i⊕j⟩)`.
Expanding the resource `|χ⟩ = ½ Σ (|i⟩|i⟩)⊗(|i⊕j⟩|j⟩)` (`cnotGateTeleportResource_vec`) over the
computational basis and firing the reshape's pure-tensor action per summand co-locates the two
output halves `a_out = |i⟩`, `b_out = |i ⊕ j⟩` on the right — identical to the bare register
`gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_vec` except the right output factor carries the
resource's pre-applied `CNOT` (`b_out = |j⟩ ↦ |i ⊕ j⟩`).  Same proof route via the
`gateTeleportProtocolReshape_toIsometry_tmul_smul_sum` bridge and the reshape action per term. -/
theorem cnotGateTeleportResource_protocolReshape_vec (qA qB : qubit.space) :
    gateTeleportProtocolReshape.toIsometry ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] cnotGateTeleportResource.vec)
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          ((qA ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ] (qB ⊗ₜ[ℂ] (qubitBasis p.2).vec)) ⊗ₜ[ℂ]
            ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis (p.1 + p.2)).vec) := by
  rw [cnotGateTeleportResource_vec]
  refine (gateTeleportProtocolReshape_toIsometry_tmul_smul_sum (qA ⊗ₜ[ℂ] qB) (2 : ℂ)⁻¹ _).trans ?_
  refine congrArg (fun z => (2 : ℂ)⁻¹ • z) (Finset.sum_congr rfl (fun p _ => ?_))
  exact gateTeleportProtocolReshape_toIsometry_tmul qA qB (qubitBasis p.1).vec (qubitBasis p.1).vec
    (qubitBasis (p.1 + p.2)).vec (qubitBasis p.2).vec

end AxQM
