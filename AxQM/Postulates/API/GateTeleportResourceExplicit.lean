/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportResource
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# AxQM.Postulates.API — the explicit computational-basis form of the resource state

The **explicit computational-basis expansion** of the four-qubit gate-teleportation resource state
`cnotGateTeleportResource` (`|χ⟩`) of Nielsen & Chuang **Problem 4.6** ("Universality with prior
entanglement"), the form flagged in `GateTeleportResource.lean` as landing "with the
gate-teleportation protocol identity that consumes it".

## What is formalised

* `gateTeleportReshape_toIsometry_tmul_tmul` / `gateTeleportReshape_symm_toIsometry_tmul_tmul` — the
  pure-tensor action of the middle-qubit regrouping `gateTeleportReshape` and its inverse:
  `R ((a⊗b)⊗(c⊗d)) = a⊗((b⊗c)⊗d)` and `R⁻¹ (a⊗((b⊗c)⊗d)) = (a⊗b)⊗(c⊗d)`, bringing the two middle
  qubits together / apart.
* `cnotMiddleGate_op_tmul` — the operator action of the placed middle `CNOT`,
  `cnotMiddleGate (a⊗(m⊗d)) = a⊗((CNOT m)⊗d)`.
* `cnotGateTeleportResource_reshape_qubitBasis` — the per-computational-basis action of the resource
  construction `R⁻¹ ∘ cnotMiddle ∘ R` on the input product `(|i⟩⊗|i⟩)⊗(|j⟩⊗|j⟩)`:
  `(|i⟩⊗|i⟩)⊗(|i⊕j⟩⊗|j⟩)`, i.e. the two `CNOT` inputs `(a_out, b_out) = (|i⟩, |j⟩)` become
  `(|i⟩, |i⊕j⟩)`.
* `cnotGateTeleportResource_vec` — the **explicit form** `|χ⟩ = ½ Σ_{i,j} (|i⟩⊗|i⟩)⊗(|i⊕j⟩⊗|j⟩)`:
  the two Bell pairs `Σ_i |i⟩|i⟩` and `Σ_j |j⟩|j⟩` with the `CNOT` truth table `(i,j) ↦ (i, i⊕j)`
  applied to the two output halves, the input labels `i, j` copied to the input halves `a_in, b_in`.

## Design notes

* **The composite/raw tensor-head diamond.**  On a composite system's state space the
  `⊗ₜ`/`•`/`+` go through the inner-product-space module instance, *defeq but not syntactically
  equal* to `TensorProduct`'s canonical module (the diamond documented in `BellState.lean` /
  `DoubleTeleportation.lean`).  A term *produced* by applying a reshape isometry therefore carries
  different instance arguments from the same term written *freshly*, so the generic `TensorProduct`
  `rw`/`simp` lemmas do not chain between the two forms.  The reshape-action lemmas close it with a
  defeq `exact` of the freshly-written value; the per-basis action chains the produced/fresh
  junctions with `Eq.trans` (unifies up to defeq) and closes the `X = X` residues with `rfl` at
  default transparency; the explicit form distributes the maps over the four Bell summands in term
  mode (`map_add`/`map_smul`) and matches each leaf to the per-basis action.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### Pure-tensor action of the middle-qubit regrouping -/

/-- **Pure-tensor action of the middle-qubit regrouping** `gateTeleportReshape`:
`R ((a⊗b)⊗(c⊗d)) = a⊗((b⊗c)⊗d)`, bringing the two middle qubits `b, c` (`a_out, b_out`) together.
The reshape is `(assoc a b (c⊗d))⁻¹` then `assoc b c d` lifted into the right factor; each step's
action is a raw `assoc`/`assoc.symm` on a pure tensor, and the composite-iso boundary is closed by
a defeq `exact`. -/
theorem gateTeleportReshape_toIsometry_tmul_tmul (a b c d : qubit.space) :
    gateTeleportReshape.toIsometry ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
      = a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] d) := by
  have key : (QSystem.Iso.tmul (.refl qubit) (QSystem.assoc qubit qubit qubit)).toIsometry
        (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))) = a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] d) := by
    have h1 := QSystem.Iso.tmul_toIsometry_tmul (.refl qubit) (QSystem.assoc qubit qubit qubit)
      a (b ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
    rw [QSystem.Iso.refl_toIsometry, assoc_toIsometry_tmul_tmul] at h1
    exact h1
  change (QSystem.Iso.tmul (.refl qubit) (QSystem.assoc qubit qubit qubit)).toIsometry
      ((QSystem.assoc qubit qubit (qubit ⊗ qubit)).symm.toIsometry
        ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))) = a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] d)
  have h2 := @assoc_symm_toIsometry_tmul_tmul qubit qubit (qubit ⊗ qubit) a b (c ⊗ₜ[ℂ] d)
  rw [h2]
  exact key

/-- **Pure-tensor action of the inverse regrouping** `gateTeleportReshape⁻¹`:
`R⁻¹ (a⊗((b⊗c)⊗d)) = (a⊗b)⊗(c⊗d)`, separating the two middle qubits back into their Bell pairs.
Proved from `gateTeleportReshape_toIsometry_tmul_tmul` and injectivity of the forward reshape. -/
theorem gateTeleportReshape_symm_toIsometry_tmul_tmul (a b c d : qubit.space) :
    gateTeleportReshape.symm.toIsometry (a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] d))
      = (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d) := by
  rw [QSystem.Iso.symm_toIsometry]
  apply gateTeleportReshape.toIsometry.injective
  have h := LinearIsometryEquiv.apply_symm_apply gateTeleportReshape.toIsometry
    (a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] d))
  rw [h]
  exact (gateTeleportReshape_toIsometry_tmul_tmul a b c d).symm

/-- **Operator action of the placed middle `CNOT`** `cnotMiddleGate = 1 ⊗ (CNOT ⊗ 1)` on the
regrouped register `a_in ⊗ ((a_out b_out) ⊗ b_in)`: `cnotMiddleGate (a⊗(m⊗d)) = a⊗((CNOT m)⊗d)`,
identity on `a_in = a` and `b_in = d`, `cnotGate` on the middle pair `m = (a_out, b_out)`. -/
theorem cnotMiddleGate_op_tmul (a d : qubit.space) (m : (qubit ⊗ qubit).space) :
    cnotMiddleGate.op (a ⊗ₜ[ℂ] (m ⊗ₜ[ℂ] d)) = a ⊗ₜ[ℂ] (cnotGate.op m ⊗ₜ[ℂ] d) := by
  rw [cnotMiddleGate]
  have h := Evolution.onRight_op_tmul (cnotGate.onLeft qubit) qubit a (m ⊗ₜ[ℂ] d)
  rw [h, Evolution.onLeft_op_tmul]
  rfl

/-! ### The explicit computational-basis form of the resource state -/

/-- **Per-computational-basis action of the resource construction** `R⁻¹ ∘ cnotMiddle ∘ R`.
On the product `(|i⟩⊗|i⟩)⊗(|j⟩⊗|j⟩)` of two computational-basis Bell summands it produces
`(|i⟩⊗|i⟩)⊗(|i⊕j⟩⊗|j⟩)`: regroup so `(a_out, b_out) = (|i⟩, |j⟩)` are adjacent, apply the `CNOT`
truth table `(|i⟩, |j⟩) ↦ (|i⟩, |j⊕i⟩)`, regroup back.  The produced/fresh instance boundary after
the reshape is chained through `Eq.trans` (defeq unification) and the `X = X` residues closed by
`rfl`. -/
theorem cnotGateTeleportResource_reshape_qubitBasis (i j : Fin 2) :
    gateTeleportReshape.symm.toIsometry (cnotMiddleGate.op (gateTeleportReshape.toIsometry
        (((qubitBasis i).vec ⊗ₜ[ℂ] (qubitBasis i).vec) ⊗ₜ[ℂ]
          ((qubitBasis j).vec ⊗ₜ[ℂ] (qubitBasis j).vec))))
      = ((qubitBasis i).vec ⊗ₜ[ℂ] (qubitBasis i).vec) ⊗ₜ[ℂ]
          ((qubitBasis (i + j)).vec ⊗ₜ[ℂ] (qubitBasis j).vec) := by
  have hmid : cnotMiddleGate.op (gateTeleportReshape.toIsometry
        (((qubitBasis i).vec ⊗ₜ[ℂ] (qubitBasis i).vec) ⊗ₜ[ℂ]
          ((qubitBasis j).vec ⊗ₜ[ℂ] (qubitBasis j).vec)))
      = (qubitBasis i).vec ⊗ₜ[ℂ]
          (((qubitBasis i).vec ⊗ₜ[ℂ] (qubitBasis (j + i)).vec) ⊗ₜ[ℂ] (qubitBasis j).vec) := by
    rw [gateTeleportReshape_toIsometry_tmul_tmul]
    refine (cnotMiddleGate_op_tmul (qubitBasis i).vec (qubitBasis j).vec
      ((qubitBasis i).vec ⊗ₜ[ℂ] (qubitBasis j).vec)).trans ?_
    rw [cnotGate_op_qubitBasisVec_tmul]
    rfl
  rw [hmid, add_comm i j]
  exact gateTeleportReshape_symm_toIsometry_tmul_tmul (qubitBasis i).vec (qubitBasis i).vec
    (qubitBasis (j + i)).vec (qubitBasis j).vec

/-- **The two-Bell-pair state, expanded over the computational basis:**
`|Φ⁺⟩ ⊗ |Φ⁺⟩ = ½ Σ_{i,j} (|i⟩⊗|i⟩)⊗(|j⟩⊗|j⟩)`.  The scalar `½ = (√2)⁻¹·(√2)⁻¹` from the two Bell
normalisations; the `change` restates each `bellVec` at the raw `qubit.space ⊗ qubit.space` head so
`TensorProduct.add_tmul`/`tmul_add` fire on the outer composite tensor. -/
theorem bellPhiPlus_tmul_bellPhiPlus_vec :
    bellPhiPlus.vec ⊗ₜ[ℂ] bellPhiPlus.vec
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ]
            ((qubitBasis p.2).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec) := by
  rw [bellPhiPlus_vec, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    Concrete.inv_sqrt_two_mul_self]
  congr 1
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  change ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec : qubit.space ⊗[ℂ] qubit.space) ⊗ₜ[ℂ]
      ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec : qubit.space ⊗[ℂ] qubit.space) = _
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add]

/-- **The explicit computational-basis form of the gate-teleportation resource state** `|χ⟩`
(Nielsen & Chuang Problem 4.6): `|χ⟩ = ½ Σ_{i,j} (|i⟩⊗|i⟩)⊗(|i⊕j⟩⊗|j⟩)`.  The two Bell pairs
`Σ_i |i⟩|i⟩` and `Σ_j |j⟩|j⟩` copy the input labels `i, j` to the input halves `a_in, b_in`, and the
`CNOT` on the output halves maps `(a_out, b_out) = (|i⟩, |j⟩)` to `(|i⟩, |i⊕j⟩)`.  Proved by
expanding `|Φ⁺⟩⊗|Φ⁺⟩` over the basis (`bellPhiPlus_tmul_bellPhiPlus_vec`), distributing the
reshape–`CNOT`–reshape maps over the four summands in term mode, and applying the per-basis action
`cnotGateTeleportResource_reshape_qubitBasis` to each. -/
theorem cnotGateTeleportResource_vec :
    cnotGateTeleportResource.vec
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ]
            ((qubitBasis (p.1 + p.2)).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec) := by
  rw [cnotGateTeleportResource, PureState.congr_vec, Evolution.evolvePure_vec, PureState.congr_vec,
    PureState.tmul_vec, bellPhiPlus_tmul_bellPhiPlus_vec]
  -- Bundle the reshape–`CNOT`–reshape composition as a single `ℂ`-linear map `φ`; over `φ` the
  -- scalar and sum distribute cleanly (`map_smul`/`map_sum`), sidestepping the composite-system
  -- `•` diamond that blocks the generic lemmas on the raw isometry/operator coercions.
  set φ : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →ₗ[ℂ]
      ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space :=
    (gateTeleportReshape.symm.toIsometry.toLinearMap.comp
      cnotMiddleGate.op.toLinearMap).comp gateTeleportReshape.toIsometry.toLinearMap with hφ
  change φ ((2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, _) = _
  rw [map_smul]
  have hsum := map_sum φ (fun p : Fin 2 × Fin 2 =>
    ((qubitBasis p.1).vec ⊗ₜ[ℂ] (qubitBasis p.1).vec) ⊗ₜ[ℂ]
      ((qubitBasis p.2).vec ⊗ₜ[ℂ] (qubitBasis p.2).vec)) Finset.univ
  refine congrArg (fun z => (2 : ℂ)⁻¹ • z)
    (hsum.trans (Finset.sum_congr rfl (fun p _ => ?_)))
  rw [hφ]
  exact cnotGateTeleportResource_reshape_qubitBasis p.1 p.2

end AxQM
