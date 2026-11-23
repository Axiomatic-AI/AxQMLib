/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Teleportation
import ToMathlib.LinearAlgebra.TensorProduct.Defs

/-!
# AxQM.Postulates.API — parallel teleportation of two qubits

The **two-qubit (parallel) teleportation identity** used in Nielsen & Chuang
**Problem 4.6** ("Universality with prior entanglement"), following the single-qubit
`teleportation_identity` of `AxQM/Postulates/API/Teleportation.lean`.

## The role in Problem 4.6

Gate teleportation of a `CNOT` teleports the two input qubits `q_A, q_B` through the four-qubit
resource state, each along its own Bell pair.  Once the register has been arranged into the two
independent single-qubit teleportation setups `(q_A ⊗ |Φ⁺⟩) ⊗ (q_B ⊗ |Φ⁺⟩)`, the single-qubit
`teleportation_identity` applies to each factor, and the tensor of the two identities is the
**double teleportation identity**: two qubits teleported at once, yielding — per *pair* of
Bell-measurement outcomes `(p, q)` — the corresponding pair of single-qubit Pauli byproduct
corrections on the two output qubits.  This is the correction-free core of the Gottesman–Chuang
gate-teleportation protocol, before the `CNOT` pre-applied to the resource couples the two lines.

## What is formalised

* `double_teleportation_identity` — the **two-qubit teleportation identity**: re-associating each of
  the two independent setups in `(u ⊗ |Φ⁺⟩) ⊗ (v ⊗ |Φ⁺⟩)`,
  `(assoc ⊗ assoc)((u ⊗ |Φ⁺⟩) ⊗ (v ⊗ |Φ⁺⟩)) = ¼ Σ_{p,q} (|β_p⟩ ⊗ X^{p} u) ⊗ (|β_q⟩ ⊗ X^{q} v)`,
  where `X^{p} = X^{y₁}Z^{x₁}` (`p = (x₁,y₁)`) is the `pauliByproduct` correction pairing with the
  Bell outcome `β_p`.  So the two Bell measurements (on the two left `(input, ancilla)` pairs) leave
  the outputs in `X^{y₁}Z^{x₁} u` and `X^{y₂}Z^{x₂} v`, each undone by its own single-qubit
  `pauliByproduct` correction.

## Design notes

* **The two-setups register.**  The identity is stated on `(u ⊗ |Φ⁺⟩) ⊗ (v ⊗ |Φ⁺⟩)` — each input
  qubit already beside its own Bell pair — so it is exactly the tensor of two single-qubit
  teleportations and its content is the parallel-teleportation fact, kept independent of the
  register bookkeeping (the interchange braid that reshapes the natural inputs-together register
  `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)` into this form, and the fold-in of the `CNOT`-coupled resource,
  are separate matters).  The two Bell pairs are the correction-free
  `bellPhiPlus ⊗ bellPhiPlus`, kept as opaque `PureState` vectors so no tensor-head friction arises.
* **Proof.**  Apply `QSystem.Iso.tmul`'s pure-tensor action once (the reshape acts factor-wise), the
  single-qubit `teleportation_identity` to each factor, and the general
  `TensorProduct.smul_sum_tmul_smul_sum` (`ToMathlib/`) to distribute the product `(½ Σ) ⊗ (½ Σ)`
  of the two half-normalised sums into `¼ Σ Σ`.
* **The tensor helper launders the module instance.**  On a composite system's state space
  `((qubit ⊗ qubit) ⊗ qubit).space` the `•`/`⊗ₜ` go through the inner-product-space module instance,
  which is *defeq but not syntactically equal* to `TensorProduct`'s canonical module, so the generic
  `TensorProduct` `rw`/`simp` lemmas do not fire directly.  The distribution lemma
  `TensorProduct.smul_sum_tmul_smul_sum` (a general fact, found in `ToMathlib/`
  alongside `TensorProduct.sum_tmul`/`tmul_sum`) is stated with the module a *bound* instance, so
  closing the goal with `exact` — which matches up to defeq — routes around the diamond cleanly.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The two-qubit (parallel) teleportation identity** (Nielsen & Chuang Problem 4.6): teleporting
two input qubits `u, v` through two Bell pairs at once.  With the register already arranged as the
two independent single-qubit teleportation setups `(u ⊗ |Φ⁺⟩) ⊗ (v ⊗ |Φ⁺⟩)`, re-associating each
setup (grouping each `(input, ancilla)` pair) gives
`(assoc ⊗ assoc)((u ⊗ |Φ⁺⟩) ⊗ (v ⊗ |Φ⁺⟩))
= ¼ Σ_{p,q} (|β_p⟩ ⊗ (X^{y₁}Z^{x₁} u)) ⊗ (|β_q⟩ ⊗ (X^{y₂}Z^{x₂} v))`, with `p = (x₁,y₁)`,
`q = (x₂,y₂)`.  A Bell measurement of each `(input, ancilla)` pair therefore
leaves the two output qubits in `X^{y₁}Z^{x₁} u` and `X^{y₂}Z^{x₂} v`, each undone by its own
single-qubit `pauliByproduct` correction — the correction-free core of gate teleportation, before
the `CNOT` on the resource couples the two lines.  Proved by applying the single-qubit
`teleportation_identity` to each factor and distributing the tensor product of the two
half-normalised sums (`TensorProduct.smul_sum_tmul_smul_sum`). -/
theorem double_teleportation_identity (u v : qubit.space) :
    (QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
        (QSystem.assoc qubit qubit qubit)).toIsometry
        ((u ⊗ₜ[ℂ] bellPhiPlus.vec) ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] bellPhiPlus.vec))
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] (pauliByproduct p.1 p.2).op u) ⊗ₜ[ℂ]
            (bellBasisVec q.1 q.2 ⊗ₜ[ℂ] (pauliByproduct q.1 q.2).op v) := by
  let x : (qubit ⊗ (qubit ⊗ qubit)).space := u ⊗ₜ[ℂ] bellPhiPlus.vec
  let y : (qubit ⊗ (qubit ⊗ qubit)).space := v ⊗ₜ[ℂ] bellPhiPlus.vec
  have hgen :
      (QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
          (QSystem.assoc qubit qubit qubit)).toIsometry (x ⊗ₜ[ℂ] y)
        = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
            (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] (pauliByproduct p.1 p.2).op u) ⊗ₜ[ℂ]
              (bellBasisVec q.1 q.2 ⊗ₜ[ℂ] (pauliByproduct q.1 q.2).op v) := by
    rw [QSystem.Iso.tmul_toIsometry_tmul]
    change (QSystem.assoc qubit qubit qubit).toIsometry (u ⊗ₜ[ℂ] bellPhiPlus.vec) ⊗ₜ[ℂ]
        (QSystem.assoc qubit qubit qubit).toIsometry (v ⊗ₜ[ℂ] bellPhiPlus.vec)
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] (pauliByproduct p.1 p.2).op u) ⊗ₜ[ℂ]
            (bellBasisVec q.1 q.2 ⊗ₜ[ℂ] (pauliByproduct q.1 q.2).op v)
    rw [teleportation_identity u, teleportation_identity v,
      show (4 : ℂ)⁻¹ = 2⁻¹ * 2⁻¹ by norm_num]
    exact TensorProduct.smul_sum_tmul_smul_sum (α := Fin 2 × Fin 2) (β := Fin 2 × Fin 2)
      2⁻¹ 2⁻¹ Finset.univ Finset.univ _ _
  exact hgen

end AxQM
