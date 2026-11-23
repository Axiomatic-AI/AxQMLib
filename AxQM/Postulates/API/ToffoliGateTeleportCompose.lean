/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliGateTeleportCorrection
import AxQM.Postulates.API.ToffoliGateTeleportReshape
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.MeasurementSimulation
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.API.QubitThree
import AxQM.Postulates.API.PhaseFlipStabilizerMaximality
import AxQM.Postulates.PartialTraceTensor

/-!
# AxQM.Postulates.API — assembling the Toffoli gate-teleportation identity

The vector-level identities for the assembled corrected gate-teleportation identity of Nielsen &
Chuang **Exercise 10.68** (the Figure on p. 488, part (2)), composing the classically controlled
byproduct corrections (`AxQM/Postulates/API/ToffoliGateTeleportCorrection.lean`) with the *actual*
measured state on the coupled-pairs register. It is the Toffoli analogue of
`gateTeleportCorrection_evolvePure_normalizeGen` (Problem 4.6), which lifts the vector correction
identity to the normalised pure state.

## The step, and why the phase washes out

The measurement step (`toffoliDataMeasurement_op_toffoliTeleportPreMeasure`) collapses the honest
pre-measurement state to the single branch

  `2⁻³ᐟ² (-1)^{m₃·z} |x⊕m₁, m₁⟩ |y⊕m₂, m₂⟩ |(x⊕m₁)·(y⊕m₂) ⊕ z, H|m₃⟩⟩`

on the interleaved coupled-pairs register `(a₁ ⊗ d_x) ⊗ ((a₂ ⊗ d_y) ⊗ (a₃ ⊗ d_z))`. The three data
qubits (the right qubit of each pair) hold the measurement residuals `|m₁⟩, |m₂⟩, H|m₃⟩`, and the
ancilla qubits (the left qubit of each pair) hold `|x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z⟩`.
**De-interleaving** this branch by `toffoliTeleportReshape.symm` gathers the ancilla wires into the
left block and the data residuals into the right block, exhibiting the branch as an honest *product*
`(ancilla block) ⊗ (data block)`. The classically-controlled correction, acting on the ancilla
block, then recovers `Toffoli|xyz⟩` there — and, applied to the *signed* collapsed ancilla, does so
**phase-free** for every outcome (`toffoliTeleportCorrection_op_ancillaBranch_toffoli`: the branch
sign `(-1)^{m₃·z}` and the target `Z`-byproduct's correction sign cancel).

## What is formalised

* `toffoliTeleportReshape_symm_toIsometry_tmul` — the **de-interleaving** pure-tensor action, the
  inverse of `toffoliTeleportReshape_toIsometry_tmul`:
  `(a₁ ⊗ x) ⊗ ((a₂ ⊗ y) ⊗ (a₃ ⊗ z)) ↦ (a₁ ⊗ (a₂ ⊗ a₃)) ⊗ (x ⊗ (y ⊗ z))` — gathering the three
  coupled ancilla–data pairs back into the ancilla block beside the data block.

* `toffoliTeleportDataBlock m₁ m₂ m₃` — the **data residual** `|m₁⟩ ⊗ (|m₂⟩ ⊗ H|m₃⟩)`: the state
  the three measured data qubits are left in (the two `Z`-basis controls in `|m₁⟩, |m₂⟩`, the
  `X`-basis target in `H|m₃⟩`), gathered into the right block after de-interleaving.

* `toffoliTeleportReshape_symm_measured_branch` — the de-interleaved measured branch, as the product
  `(qubitThreeBasis (x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z)) ⊗ (toffoliTeleportDataBlock m₁ m₂ m₃)`.

* `toffoliTeleportPreMeasureGen ψ` — the pre-measurement state for a **general input** `ψ` (the
  analogue of `gateTeleportRegisterGen`); the computational-basis state is the special case
  `ψ = |xyz⟩` (`toffoliTeleportPreMeasure_eq_gen`).

* `qubitThreeVecBasis` — the computational basis as a `Module.Basis` of the three-qubit register, so
  that a *linear* identity in the input can be checked on the eight basis kets.

* `toffoliTeleportCorrection_onLeft_op_reshape_symm_measured` (computational-basis input) and its
  general-input extension `..._gen` — **the corrected, de-interleaved measured branch is the product
  `2⁻³ᐟ² • (Toffoli(ψ) ⊗ (data residual))`.** Applying the classically-controlled correction on the
  ancilla block (via `Evolution.onLeft`) to the de-interleaved measured branch yields a product
  whose ancilla (left) factor is the clean Toffoli of the *whole* input, for **every** outcome (the
  branch sign cancels against the correction sign). Both sides are ℂ-linear in `ψ.vec`, so the
  general form follows from the computational-basis one by `Module.Basis.ext qubitThreeVecBasis` —
  the analogue of `cnotGateTeleportation_identity_general`.

* `norm_toffoliDataMeasurement_op_toffoliTeleportPreMeasureGen` — the branch norm is `2⁻³ᐟ²` for
  every input (the correction and reshape being norm-preserving), so it normalises and the amplitude
  divides out.

* `toffoliTeleportCorrection_onLeft_evolvePure_congr_normalizeGen` — **the corrected,
  de-interleaved, normalised branch is the product `Toffoli(ψ) ⊗ (data block)`, for an arbitrary
  input** `ψ`: a *product* pure state whose ancilla (left) factor is the clean
  `toffoliGate.evolvePure ψ`, for **every** outcome. This is the pure-state factorisation whose left
  marginal is the induced Toffoli output.

The assembled `State`-level identity (the ancilla marginal of the corrected post-measurement state
`= (Toffoli|xyz⟩).toState`) is in `AxQM/NC/Ch10/Exercise10_68_FTToffoli.lean`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

set_option maxHeartbeats 800000 in
-- The symm-isometry action over the 64-dimensional coupled-pairs register exceeds the default
-- budget.
/-- **De-interleaving pure-tensor action of the Toffoli-teleportation reshape** (the inverse of
`toffoliTeleportReshape_toIsometry_tmul`):
`toffoliTeleportReshape.symm ((a₁ ⊗ x) ⊗ ((a₂ ⊗ y) ⊗ (a₃ ⊗ z))) = (a₁ ⊗ (a₂ ⊗ a₃)) ⊗ (x ⊗ (y ⊗ z))`.
The three coupled ancilla–data pairs `(aᵢ, dᵢ)` are regrouped back into the ancilla block
`a₁ ⊗ (a₂ ⊗ a₃)` beside the data block `x ⊗ (y ⊗ z)`. Proved from the forward action lemma by
`LinearIsometryEquiv.symm_apply_eq` (`QSystem.Iso.symm_toIsometry` identifies the transported
isometry of the inverse iso with the inverse isometry). -/
theorem toffoliTeleportReshape_symm_toIsometry_tmul (a₁ a₂ a₃ x y z : qubit.space) :
    toffoliTeleportReshape.symm.toIsometry
        ((a₁ ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] ((a₂ ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a₃ ⊗ₜ[ℂ] z)))
      = (a₁ ⊗ₜ[ℂ] (a₂ ⊗ₜ[ℂ] a₃)) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) := by
  rw [QSystem.Iso.symm_toIsometry]
  apply toffoliTeleportReshape.toIsometry.injective
  erw [LinearIsometryEquiv.apply_symm_apply]

/-- **The data residual** the three data-qubit measurements leave, gathered into the right block
after de-interleaving: `|m₁⟩ ⊗ (|m₂⟩ ⊗ H|m₃⟩)` — the two control data qubits in their `Z`-basis
outcomes `|m₁⟩, |m₂⟩` and the target data qubit in its `X`-basis outcome `H|m₃⟩` (`pmQubit m₃`). It
is the right (traced-out) factor of the de-interleaved measured branch. -/
def toffoliTeleportDataBlock (m₁ m₂ m₃ : Fin 2) : PureState (qubit ⊗ (qubit ⊗ qubit)) :=
  (qubitBasis m₁).tmul ((qubitBasis m₂).tmul (hadamardGate.evolvePure (qubitBasis m₃)))

set_option maxHeartbeats 800000 in
-- Expanding both sides over the 64-dimensional coupled-pairs register exceeds the default budget.
/-- **The de-interleaved measured branch is the product `(ancilla block) ⊗ (data block)`.**
De-interleaving the unit branch tensor by `toffoliTeleportReshape.symm` gathers the ancilla wires
into the left block `|x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z⟩` and the data residuals into the right block
`toffoliTeleportDataBlock = |m₁, m₂, H|m₃⟩⟩`:

  `reshape.symm (|x⊕m₁, m₁⟩ |y⊕m₂, m₂⟩ |(x⊕m₁)·(y⊕m₂) ⊕ z, H|m₃⟩⟩)
     = |x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z⟩ ⊗ |m₁, m₂, H|m₃⟩⟩`.

Both sides expand to the same leaf tensor (`PureState.tmul_vec`, `qubitThreeBasis`,
`toffoliTeleportDataBlock`), whereupon the de-interleaving action
`toffoliTeleportReshape_symm_toIsometry_tmul` matches them. -/
theorem toffoliTeleportReshape_symm_measured_branch (x y z m₁ m₂ m₃ : Fin 2) :
    toffoliTeleportReshape.symm.toIsometry
        (((qubitBasis (x + m₁)).tmul (qubitBasis m₁)).tmul
          (((qubitBasis (y + m₂)).tmul (qubitBasis m₂)).tmul
            ((qubitBasis ((x + m₁) * (y + m₂) + z)).tmul
              (hadamardGate.evolvePure (qubitBasis m₃))))).vec
      = (qubitThreeBasis (x + m₁, y + m₂, (x + m₁) * (y + m₂) + z)).vec ⊗ₜ[ℂ]
          (toffoliTeleportDataBlock m₁ m₂ m₃).vec := by
  simp only [PureState.tmul_vec, qubitThreeBasis, toffoliTeleportDataBlock]
  exact toffoliTeleportReshape_symm_toIsometry_tmul _ _ _ _ _ _

/-! ## The general-input development

"This circuit implements the Toffoli gate" (part (2)) is a *gate* claim: it must act correctly on
**every** input state, including superposed and entangled inputs — not merely the eight
computational-basis inputs `|xyz⟩`. Following the CNOT gate-teleportation development (Problem 4.6),
the whole chain is therefore stated for a **general input pure state** `ψ` and the computational-
basis statements are its `ψ = |xyz⟩` corollaries. The induced operation *normalises* the collapsed
branch, so is **not** linear in the input; but the underlying corrected, de-interleaved *vector*
identity IS ℂ-linear in the input, and the branch norm is input-independent, so the general-input
identity follows from the computational-basis one by `Module.Basis.ext` (the computational basis
spans). -/

/-- **The computational basis as a `Module.Basis` of the three-qubit register.** The eight
orthonormal kets `(qubitThreeBasis s).vec` (`qubitThreeBasis_orthonormal`) number
`8 = dim (qubit ⊗ (qubit ⊗ qubit))` (`finrank_bitFlipReg`), so they form a `Module.Basis`; this lets
a *linear* identity in the input be checked on the computational basis (the analogue of
`pmThreeBasis` for the `±` basis). -/
def qubitThreeVecBasis : Module.Basis (Fin 2 × Fin 2 × Fin 2) ℂ (qubit ⊗ (qubit ⊗ qubit)).space :=
  basisOfLinearIndependentOfCardEqFinrank qubitThreeBasis_orthonormal.linearIndependent
    (by rw [finrank_bitFlipReg]; rfl)

@[simp] theorem qubitThreeVecBasis_apply (s : Fin 2 × Fin 2 × Fin 2) :
    qubitThreeVecBasis s = (qubitThreeBasis s).vec :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) s

set_option maxHeartbeats 800000 in
-- `evolvePure` of the coupling on the 64-dimensional coupled-pairs register exceeds the default.
/-- **The pre-measurement gate-teleportation state for a general input** `ψ`: the offline resource
`toffoliAncilla = |Θ_T⟩` beside the data `ψ`, reshaped into coupled pairs
(`toffoliTeleportReshape`), then coupled (`toffoliTeleportCoupling`). The analogue of the CNOT
`gateTeleportRegisterGen`; the computational-basis state is the special case
`ψ = qubitThreeBasis (x, y, z)` (`toffoliTeleportPreMeasure_eq_gen`, definitionally). Taking `ψ` an
*arbitrary* three-qubit pure state — possibly entangled with the two control wires — is what makes
the identity below "the circuit implements the Toffoli **gate**", not just its truth table. -/
def toffoliTeleportPreMeasureGen (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) :
    PureState ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  toffoliTeleportCoupling.evolvePure
    (PureState.congr toffoliTeleportReshape (toffoliAncilla.tmul ψ))

/-- The computational-basis pre-measurement state is the general one at `ψ = |xyz⟩`
(definitional). -/
theorem toffoliTeleportPreMeasure_eq_gen (x y z : Fin 2) :
    toffoliTeleportPreMeasure x y z = toffoliTeleportPreMeasureGen (qubitThreeBasis (x, y, z)) :=
  rfl

set_option maxHeartbeats 1600000 in
-- The full corrected-branch reduction over the 64-dimensional register exceeds the default budget.
/-- **The corrected, de-interleaved measured branch is the product `Toffoli|xyz⟩ ⊗ (data block)`**
(computational-basis input; Nielsen & Chuang, Exercise 10.68, part (2)). Applying the
classically-controlled correction on the ancilla block (`Evolution.onLeft`) to the de-interleaved
measured branch of the computational-basis pre-measurement state (outcome `(m₁, m₂, m₃)`) yields the
product `2⁻³ᐟ² • (Toffoli|xyz⟩ ⊗ (data residual))` — the ancilla (left) factor is the clean
`Toffoli|xyz⟩` for **every** outcome. The collapse
(`toffoliDataMeasurement_op_toffoliTeleportPreMeasure`) gives the branch, de-interleaving
(`toffoliTeleportReshape_symm_measured_branch`) exposes the product structure, and the correction on
the *signed* ancilla recovers `Toffoli|xyz⟩` phase-free
(`toffoliTeleportCorrection_op_ancillaBranch`, the branch sign `(-1)^{m₃·z}` and the correction sign
cancelling). This is the input-value on which
the general-input identity is checked by `Module.Basis.ext`. -/
theorem toffoliTeleportCorrection_onLeft_op_reshape_symm_measured (x y z m₁ m₂ m₃ : Fin 2) :
    ((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))).op
        (toffoliTeleportReshape.symm.toIsometry
          (toffoliDataMeasurement.op (m₁, m₂, m₃) (toffoliTeleportPreMeasure x y z).vec))
      = Concrete.invSqrt2 ^ 3 •
          ((toffoliGate.evolvePure (qubitThreeBasis (x, y, z))).vec ⊗ₜ[ℂ]
            (toffoliTeleportDataBlock m₁ m₂ m₃).vec) := by
  -- Applying the correction to the *signed* collapsed ancilla returns `Toffoli|xyz⟩` phase-free
  -- (`toffoliTeleportCorrection_op_ancillaBranch_toffoli`, folded to `qubitThreeBasis`).
  have hcorr : (toffoliTeleportCorrection m₁ m₂ m₃).op
      (((-1 : ℂ) ^ (m₃.val * z.val)) •
        (qubitThreeBasis (x + m₁, y + m₂, (x + m₁) * (y + m₂) + z)).vec)
      = (toffoliGate.evolvePure (qubitThreeBasis (x, y, z))).vec := by
    have h := toffoliTeleportCorrection_op_ancillaBranch_toffoli x y z m₁ m₂ m₃
    simpa only [toffoliTeleportAncillaBranch] using h
  -- Push the (composite-system) branch sign onto the ancilla factor. `TensorProduct.smul_tmul'`
  -- discharges the module-instance diamond of `QSystem.space` by `exact`/defeq (the ascription pins
  -- the scalar action the goal carries), then it is applied with `erw`.
  have hpush : ((-1 : ℂ) ^ (m₃.val * z.val)) •
        (((qubitThreeBasis (x + m₁, y + m₂, (x + m₁) * (y + m₂) + z)).vec ⊗ₜ[ℂ]
            (toffoliTeleportDataBlock m₁ m₂ m₃).vec :
          ((qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))).space))
      = (((-1 : ℂ) ^ (m₃.val * z.val)) •
          (qubitThreeBasis (x + m₁, y + m₂, (x + m₁) * (y + m₂) + z)).vec) ⊗ₜ[ℂ]
          (toffoliTeleportDataBlock m₁ m₂ m₃).vec :=
    TensorProduct.smul_tmul' _ _ _
  -- The amplitude `invSqrt2^3` is pulled to the front through both maps; the residual sign
  -- `(-1)^{m₃·z}` stays on the ancilla, where the correction cancels it phase-free (`hcorr`).
  rw [toffoliDataMeasurement_op_toffoliTeleportPreMeasure, map_smul, map_smul, map_smul,
    toffoliTeleportReshape_symm_measured_branch]
  erw [hpush]
  rw [Evolution.onLeft_op_tmul, hcorr]
  -- The two `invSqrt2^3 • (… ⊗ₜ …)` sides differ only in the composite-system vs `TensorProduct`
  -- module instance (defeq); a default-transparency `rfl` bridges the diamond.
  rfl

set_option maxHeartbeats 3200000 in
-- Bundling the six-map pipeline over the 64-dimensional register and checking it on the eight
-- computational-basis vectors exceeds the default heartbeat budget (and, on the pinned Mathlib, the
-- default recursion depth of the definitional unfolding).
set_option maxRecDepth 4000 in
/-- **The corrected, de-interleaved measured branch is the product `Toffoli(ψ) ⊗ (data block)`, for
an arbitrary input** `ψ` (Nielsen & Chuang, Exercise 10.68, part (2)). For *every* three-qubit input
pure state `ψ` — including one entangled between its three wires — applying the classically
controlled correction on the ancilla block to the de-interleaved measured branch of the general
pre-measurement state yields `2⁻³ᐟ² • (toffoliGate(ψ) ⊗ (data residual))` — the ancilla factor is
the Toffoli of the *whole* input `ψ`. Both sides are ℂ-linear in `ψ.vec` (the coupling, reshapes,
measurement operator, correction, and tensor placements are all linear), so — bundling each as a
`LinearMap` — the identity extends off the computational basis, on which it is
`toffoliTeleportCorrection_onLeft_op_reshape_symm_measured`, to *all* of the three-qubit space by
`Module.Basis.ext qubitThreeVecBasis`. This is the step upgrading the identity from the eight
`|xyz⟩` truth-table inputs to every, possibly entangled, input — the analogue of
`cnotGateTeleportation_identity_general`. -/
theorem toffoliTeleportCorrection_onLeft_op_reshape_symm_measured_gen
    (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) (m₁ m₂ m₃ : Fin 2) :
    ((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))).op
        (toffoliTeleportReshape.symm.toIsometry
          (toffoliDataMeasurement.op (m₁, m₂, m₃) (toffoliTeleportPreMeasureGen ψ).vec))
      = Concrete.invSqrt2 ^ 3 •
          ((toffoliGate.op ψ.vec) ⊗ₜ[ℂ] (toffoliTeleportDataBlock m₁ m₂ m₃).vec) := by
  suffices key :
      (((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))).op.toLinearMap ∘ₗ
          toffoliTeleportReshape.symm.toIsometry.toLinearEquiv.toLinearMap ∘ₗ
          (toffoliDataMeasurement.op (m₁, m₂, m₃)).toLinearMap ∘ₗ
          toffoliTeleportCoupling.op.toLinearMap ∘ₗ
          toffoliTeleportReshape.toIsometry.toLinearEquiv.toLinearMap ∘ₗ
          TensorProduct.mk ℂ (qubit ⊗ (qubit ⊗ qubit)).space (qubit ⊗ (qubit ⊗ qubit)).space
            toffoliAncilla.vec)
        = Concrete.invSqrt2 ^ 3 •
            (((TensorProduct.mk ℂ (qubit ⊗ (qubit ⊗ qubit)).space
                    (qubit ⊗ (qubit ⊗ qubit)).space).flip
                (toffoliTeleportDataBlock m₁ m₂ m₃).vec).comp toffoliGate.op.toLinearMap) by
    have hcong := LinearMap.congr_fun key ψ.vec
    simp only [toffoliTeleportPreMeasureGen, Evolution.evolvePure_vec, PureState.congr_vec,
      PureState.tmul_vec]
    -- The remaining steps (`comp_apply`, `mk_apply`, `smul_apply`, `flip_apply`) are definitional.
    exact hcong
  refine Module.Basis.ext qubitThreeVecBasis fun s => ?_
  obtain ⟨x, y, z⟩ := s
  simp only [qubitThreeVecBasis_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  -- Both bundled maps reduce (definitionally) on the basis input to the computational-basis
  -- identity `toffoliTeleportCorrection_onLeft_op_reshape_symm_measured`.
  exact toffoliTeleportCorrection_onLeft_op_reshape_symm_measured x y z m₁ m₂ m₃

set_option maxHeartbeats 800000 in
-- The norm computation over the 64-dimensional coupled-pairs register exceeds the default budget.
/-- **The measured branch has norm `2⁻³ᐟ²`, for an arbitrary input** `ψ`. Since the correction and
the de-interleaving reshape are norm-preserving (`Evolution.norm_op_apply`,
`LinearIsometryEquiv.norm_map`), the branch norm equals that of the corrected product
`2⁻³ᐟ² • (Toffoli(ψ) ⊗ (data residual))`
(`toffoliTeleportCorrection_onLeft_op_reshape_symm_measured_gen`), i.e. `2⁻³ᐟ² = ‖invSqrt2^3‖` (the
Toffoli output and the data residual are unit, `Evolution.norm_op_apply`/`PureState.normalized`,
`TensorProduct.norm_tmul`). Input-independent — the outcome probability is `1/8` for every input —
so the branch normalises and the `2⁻³ᐟ²` amplitude divides out. -/
theorem norm_toffoliDataMeasurement_op_toffoliTeleportPreMeasureGen
    (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) (m₁ m₂ m₃ : Fin 2) :
    ‖toffoliDataMeasurement.op (m₁, m₂, m₃) (toffoliTeleportPreMeasureGen ψ).vec‖
      = ‖Concrete.invSqrt2 ^ 3‖ := by
  rw [← LinearIsometryEquiv.norm_map toffoliTeleportReshape.symm.toIsometry
      (toffoliDataMeasurement.op (m₁, m₂, m₃) (toffoliTeleportPreMeasureGen ψ).vec),
    ← Evolution.norm_op_apply
      ((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))),
    toffoliTeleportCorrection_onLeft_op_reshape_symm_measured_gen]
  -- The `invSqrt2^3 • …` scalar action carries `TensorProduct`'s `SMul` (no `NormSMulClass`);
  -- `set`+`change` re-elaborates it to the canonical scalar action so `norm_smul` fires.
  set W : ((qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))).space :=
    toffoliGate.op ψ.vec ⊗ₜ[ℂ] (toffoliTeleportDataBlock m₁ m₂ m₃).vec with hW
  change ‖Concrete.invSqrt2 ^ 3 • W‖ = ‖Concrete.invSqrt2 ^ 3‖
  rw [norm_smul, hW]
  erw [TensorProduct.norm_tmul]
  rw [Evolution.norm_op_apply, PureState.normalized, PureState.normalized, mul_one, mul_one]

set_option maxHeartbeats 1600000 in
-- The `.op`/normalise/reshape bridge over the 64-dimensional register exceeds the default budget.
/-- **The corrected, de-interleaved, normalised measured branch is the product `Toffoli(ψ) ⊗ (data
block)`, for an arbitrary input** `ψ` (Nielsen & Chuang, Exercise 10.68, part (2)). Applying the
correction on the ancilla block to the *normalised* de-interleaved measured branch of the general
pre-measurement state yields exactly the product pure state
`(toffoliGate.evolvePure ψ) ⊗ (toffoliTeleportDataBlock m₁ m₂ m₃)` — the ancilla factor being the
clean Toffoli of the *whole* input `ψ`, for **every** outcome. The `2⁻³ᐟ²` branch amplitude
(`norm_...Gen`) cancels against the `‖·‖⁻¹` normalisation; the corrected vector identity
(`toffoliTeleportCorrection_onLeft_op_reshape_symm_measured_gen`) supplies the output factor. This
is the Toffoli analogue of the CNOT normalisation bridge
`gateTeleportCorrection_evolvePure_normalizeGen` (Problem 4.6). -/
theorem toffoliTeleportCorrection_onLeft_evolvePure_congr_normalizeGen
    (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) (m₁ m₂ m₃ : Fin 2)
    (hv : toffoliDataMeasurement.op (m₁, m₂, m₃) (toffoliTeleportPreMeasureGen ψ).vec ≠ 0) :
    ((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))).evolvePure
        (PureState.congr toffoliTeleportReshape.symm
          (PureState.normalize (toffoliDataMeasurement.op (m₁, m₂, m₃)
            (toffoliTeleportPreMeasureGen ψ).vec) hv))
      = (toffoliGate.evolvePure ψ).tmul (toffoliTeleportDataBlock m₁ m₂ m₃) := by
  have h1 : ((‖Concrete.invSqrt2 ^ 3‖ : ℝ) : ℂ)⁻¹ * Concrete.invSqrt2 ^ 3 = 1 := by
    have h2 : ((‖Concrete.invSqrt2 ^ 3‖ : ℝ) : ℂ) = Concrete.invSqrt2 ^ 3 := by
      rw [Concrete.invSqrt2, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h2, inv_mul_cancel₀ (pow_ne_zero 3 Concrete.invSqrt2_ne_zero)]
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.congr_vec, PureState.normalize_vec,
    norm_toffoliDataMeasurement_op_toffoliTeleportPreMeasureGen, map_smul, map_smul,
    toffoliTeleportCorrection_onLeft_op_reshape_symm_measured_gen, PureState.tmul_vec,
    Evolution.evolvePure_vec]
  -- Both scalar actions carry `TensorProduct`'s `SMul`; `set`+`change` canonicalises them so
  -- `smul_smul` fires and the `‖·‖⁻¹` normalisation cancels the `invSqrt2^3` amplitude.
  set W : ((qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))).space :=
    toffoliGate.op ψ.vec ⊗ₜ[ℂ] (toffoliTeleportDataBlock m₁ m₂ m₃).vec with hW
  change ((‖Concrete.invSqrt2 ^ 3‖ : ℝ) : ℂ)⁻¹ • Concrete.invSqrt2 ^ 3 • W = W
  rw [smul_smul, h1, one_smul]

end AxQM
