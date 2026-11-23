/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyMonotone

/-!
# Strong subadditivity of the von Neumann entropy

For a strictly positive (faithful) density operator `ρ` on a tripartite space
`E ⊗ (F ⊗ G)`, the von Neumann entropy satisfies the **strong subadditivity** inequality

`S(ρ) + S(ρ_F) ≤ S(ρ_{EF}) + S(ρ_{FG})`,

where `ρ_F`, `ρ_{EF}`, `ρ_{FG}` are the marginals obtained by tracing out the complementary
subsystems (Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 11.14).

## Proof route

The engine is the **quantum mutual information** written as a relative entropy against the product
of the marginals: for a strictly positive density operator `ρ` on `E ⊗ F`,

`D(ρ ‖ (Tr_F ρ) ⊗ (Tr_E ρ)) = S(Tr_F ρ) + S(Tr_E ρ) - S(ρ)`

(`ContinuousLinearMap.quantumRelativeEntropy_mapL_partialTrace_eq`), obtained from the trace form
`D(ρ ‖ σ) = -S(ρ) - re tr((log σ) ρ)`
(`IsDensityOp.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub`), the additivity of the operator
logarithm on a tensor product (`IsSelfAdjoint.cfc_log_tensorMap`), and the two trace–marginal
dualities `trace ((V ⊗ 1) T) = tr(V · Tr_F T)` /  `trace ((1 ⊗ V) T) = tr(V · Tr_E T)`
(`LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTrace{Right,Left}`).

Strong subadditivity is then the **monotonicity of the mutual information under discarding `G`**:
`I(E:F) ≤ I(E:FG)`. Tracing out `G` from the re-associated state
`(assocIsometry).symm.conjStarAlgEquiv ρ` on `(E ⊗ F) ⊗ G` sends `ρ` to its `E ⊗ F`-marginal and
sends the product `ρ_E ⊗ ρ_{FG}` to `ρ_E ⊗ ρ_F` (`LinearMap.partialTraceRight_assoc_conj_map`),
so the monotonicity of the relative entropy under the right partial trace
(`ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le`, N&C Thm 11.17) gives
`D(ρ_{EF} ‖ ρ_E ⊗ ρ_F) ≤ D(ρ ‖ ρ_E ⊗ ρ_{FG})`; expanding both sides by the mutual-information
identity and cancelling `S(ρ_E)` yields the inequality. The associator tower lemmas
(`LinearMap.partialTraceRight_eq_of_partialTraceRight_assocIsometry`,
`LinearMap.partialTraceLeft_partialTraceRight_assoc`) identify the two ways of reading off the `E`-
and `F`-marginals of the tripartite state.

## Faithfulness

The mutual-information identity and the monotonicity of the relative entropy are stated for the
finite, real-valued relative-entropy engine, which requires the states to be **strictly positive**
(faithful). Consequently this file proves strong subadditivity for strictly positive tripartite
states. The fully general statement (which is entropy-only and has no finiteness obstruction)
follows by a continuity/limiting argument over faithful approximants and is left for future work.

## Main results

* `ContinuousLinearMap.quantumRelativeEntropy_mapL_partialTrace_eq` — the quantum
  mutual-information identity `D(ρ ‖ ρ_E ⊗ ρ_F) = S(ρ_E) + S(ρ_F) - S(ρ)`.
* `ContinuousLinearMap.vonNeumannEntropy_add_partialTrace_le` — strong subadditivity
  `S(ρ) + S(ρ_F) ≤ S(ρ_{EF}) + S(ρ_{FG})`.
-/

@[expose] public section

open Module InnerProductSpace
open scoped TensorProduct

namespace ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **Quantum mutual information as a relative entropy against the product of the marginals.**
For a strictly positive density operator `ρ` on `E ⊗ F` with marginals `ρ_E = Tr_F ρ` and
`ρ_F = Tr_E ρ`,

`D(ρ ‖ ρ_E ⊗ ρ_F) = S(ρ_E) + S(ρ_F) - S(ρ)`.

The right-hand side is the quantum mutual information `I(E:F)`. The marginals are supplied as
hypotheses (`hρE`, `hρF`) so the identity threads a bundled reduced state directly. -/
theorem quantumRelativeEntropy_mapL_partialTrace_eq
    {ιE ιF : Type*} [Fintype ιE] [Fintype ιF] [Nonempty ιE] [Nonempty ιF]
    (bE : OrthonormalBasis ιE ℂ E) (bF : OrthonormalBasis ιF ℂ F)
    {ρ : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρE : E →L[ℂ] E} {ρF : F →L[ℂ] F}
    (hρ : ρ.IsDensityOp) (hρs : IsStrictlyPositive ρ)
    (hρE : LinearMap.partialTraceRight bF ρ.toLinearMap = ρE.toLinearMap)
    (hρF : LinearMap.partialTraceLeft bE ρ.toLinearMap = ρF.toLinearMap) :
    ρ.quantumRelativeEntropy (TensorProduct.mapL ρE ρF) =
      ρE.vonNeumannEntropy + ρF.vonNeumannEntropy - ρ.vonNeumannEntropy := by
  have hρEd : ρE.IsDensityOp := hρ.of_partialTraceRight_eq bF hρE
  have hρFd : ρF.IsDensityOp := hρ.of_partialTraceLeft_eq bE hρF
  have hρEs : IsStrictlyPositive ρE := hρs.of_partialTraceRight_eq bF hρE
  have hρFs : IsStrictlyPositive ρF := hρs.of_partialTraceLeft_eq bE hρF
  have hEpos := fun i => hρEs.eigenvalues_pos hρEd.isPositive.isSelfAdjoint.isSymmetric rfl i
  have hFpos := fun j => hρFs.eigenvalues_pos hρFd.isPositive.isSelfAdjoint.isSymmetric rfl j
  have hlog : cfc Real.log (TensorProduct.mapL ρE ρF) =
      TensorProduct.mapL (cfc Real.log ρE) (1 : F →L[ℂ] F) +
        TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log ρF) :=
    IsSelfAdjoint.cfc_log_tensorMap hρEd.isPositive.isSelfAdjoint hρFd.isPositive.isSelfAdjoint
      rfl rfl hEpos hFpos
  -- The two marginal trace terms.
  have ht1 : LinearMap.trace ℂ (E ⊗[ℂ] F)
        ((TensorProduct.mapL (cfc Real.log ρE) (1 : F →L[ℂ] F)).toLinearMap ∘ₗ ρ.toLinearMap) =
      LinearMap.trace ℂ E ((cfc Real.log ρE).toLinearMap ∘ₗ ρE.toLinearMap) := by
    rw [TensorProduct.toLinearMap_mapL, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
      LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight bF, hρE]
  have ht2 : LinearMap.trace ℂ (E ⊗[ℂ] F)
        ((TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log ρF)).toLinearMap ∘ₗ ρ.toLinearMap) =
      LinearMap.trace ℂ F ((cfc Real.log ρF).toLinearMap ∘ₗ ρF.toLinearMap) := by
    rw [TensorProduct.toLinearMap_mapL, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
      LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft bE, hρF]
  rw [hρ.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub, hlog]
  rw [ContinuousLinearMap.toLinearMap_add, LinearMap.add_comp, map_add, ht1, ht2]
  rw [map_add, hρEd.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy,
    hρFd.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy]
  ring

set_option synthInstance.maxHeartbeats 400000 in
-- The nested-tensor operator algebras `(E ⊗ (F ⊗ G)) →L …` force a deep `Algebra ℝ` /
-- `IsScalarTower ℝ ℂ` instance search (these are not global instances for abstract spaces), which
-- exceeds the default `synthInstance` budget even though the instances are supplied locally below.
/-- **Strong subadditivity of the von Neumann entropy** (Nielsen & Chuang, Theorem 11.14). For a
strictly positive (faithful) density operator `ρ` on the tripartite space `E ⊗ (F ⊗ G)`,

`S(ρ) + S(ρ_F) ≤ S(ρ_{EF}) + S(ρ_{FG})`,

where `ρ_{EF}` is the `E ⊗ F`-marginal (trace out `G`, read off after re-associating to
`(E ⊗ F) ⊗ G`), `ρ_{FG} = Tr_E ρ` is the `F ⊗ G`-marginal, and `ρ_F = Tr_G ρ_{FG}` is the
`F`-marginal. Equivalently the quantum mutual information is monotone under discarding `G`,
`I(E:F) ≤ I(E:FG)`.

The three marginals are supplied as hypotheses so a physics-layer consumer can thread its reduced
states directly; the `E`-marginal `ρ_E` is internal (it cancels). Faithfulness
(`IsStrictlyPositive`) is the finite-branch hypothesis of the relative-entropy engine (see the
module docstring). -/
theorem vonNeumannEntropy_add_partialTrace_le
    {ιE ιF ιG : Type*} [Fintype ιE] [Fintype ιF] [Fintype ιG]
    [Nonempty ιE] [Nonempty ιF] [Nonempty ιG]
    (bE : OrthonormalBasis ιE ℂ E) (bF : OrthonormalBasis ιF ℂ F) (bG : OrthonormalBasis ιG ℂ G)
    {ρ : (E ⊗[ℂ] (F ⊗[ℂ] G)) →L[ℂ] (E ⊗[ℂ] (F ⊗[ℂ] G))}
    {ρAB : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρBC : (F ⊗[ℂ] G) →L[ℂ] (F ⊗[ℂ] G)} {ρB : F →L[ℂ] F}
    (hρ : ρ.IsDensityOp) (hρs : IsStrictlyPositive ρ)
    (hρAB : LinearMap.partialTraceRight bG
      ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv ρ).toLinearMap = ρAB.toLinearMap)
    (hρBC : LinearMap.partialTraceLeft bE ρ.toLinearMap = ρBC.toLinearMap)
    (hρB : LinearMap.partialTraceRight bG ρBC.toLinearMap = ρB.toLinearMap) :
    ρ.vonNeumannEntropy + ρB.vonNeumannEntropy ≤
      ρAB.vonNeumannEntropy + ρBC.vonNeumannEntropy := by
  classical
  -- The real–complex scalar tower on the operator algebras, needed by the relative-entropy engine
  -- (not global instances for abstract spaces; synthesis is slow for the nested tensors).
  let : NormedSpace ℝ ((E ⊗[ℂ] (F ⊗[ℂ] G)) →L[ℂ] (E ⊗[ℂ] (F ⊗[ℂ] G))) := NormedSpace.complexToReal
  let : NormedSpace ℝ (((E ⊗[ℂ] F) ⊗[ℂ] G) →L[ℂ] ((E ⊗[ℂ] F) ⊗[ℂ] G)) := NormedSpace.complexToReal
  have : IsScalarTower ℝ ℂ ((E ⊗[ℂ] (F ⊗[ℂ] G)) →L[ℂ] (E ⊗[ℂ] (F ⊗[ℂ] G))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower ℝ ℂ (((E ⊗[ℂ] F) ⊗[ℂ] G) →L[ℂ] ((E ⊗[ℂ] F) ⊗[ℂ] G)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- The `E`-marginal `ρ_E = Tr_{F⊗G} ρ`, kept as an opaque operator with its defining equation.
  set ρA : E →L[ℂ] E := LinearMap.toContinuousLinearMap
    (LinearMap.partialTraceRight (bF.tensorProduct bG) ρ.toLinearMap) with hρA_def
  have hρA : LinearMap.partialTraceRight (bF.tensorProduct bG) ρ.toLinearMap = ρA.toLinearMap :=
    (LinearMap.coe_toContinuousLinearMap _).symm
  clear_value ρA
  -- Density / strict positivity of every operator that appears (`σ = ρ_E ⊗ ρ_{FG}` and its
  -- re-associated conjugate, and the re-associated tripartite state).
  have hρAd : ρA.IsDensityOp := hρ.of_partialTraceRight_eq (bF.tensorProduct bG) hρA
  have hρAs : IsStrictlyPositive ρA := hρs.of_partialTraceRight_eq (bF.tensorProduct bG) hρA
  have hρBCd : ρBC.IsDensityOp := hρ.of_partialTraceLeft_eq bE hρBC
  have hρBCs : IsStrictlyPositive ρBC := hρs.of_partialTraceLeft_eq bE hρBC
  have hσd : (TensorProduct.mapL ρA ρBC).IsDensityOp := hρAd.mapL hρBCd
  have hσs : IsStrictlyPositive (TensorProduct.mapL ρA ρBC) :=
    TensorProduct.mapL_isStrictlyPositive hρAs hρBCs
  have hρ''d : ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv ρ).IsDensityOp :=
    (LinearIsometryEquiv.conjStarAlgEquiv_isDensityOp_iff _).mpr hρ
  have hρ''s : IsStrictlyPositive ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv ρ) :=
    (LinearIsometryEquiv.conjStarAlgEquiv_isStrictlyPositive_iff _).mpr hρs
  have hσ''d : ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv
      (TensorProduct.mapL ρA ρBC)).IsDensityOp :=
    (LinearIsometryEquiv.conjStarAlgEquiv_isDensityOp_iff _).mpr hσd
  have hσ''s : IsStrictlyPositive ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv
      (TensorProduct.mapL ρA ρBC)) :=
    (LinearIsometryEquiv.conjStarAlgEquiv_isStrictlyPositive_iff _).mpr hσs
  have hρABd : ρAB.IsDensityOp := hρ''d.of_partialTraceRight_eq bG hρAB
  have hρABs : IsStrictlyPositive ρAB := hρ''s.of_partialTraceRight_eq bG hρAB
  -- `Tr_F ρ_{EF} = ρ_E` and `Tr_E ρ_{EF} = ρ_F` via the associator tower lemmas.
  have hAB_A : LinearMap.partialTraceRight bF ρAB.toLinearMap = ρA.toLinearMap :=
    LinearMap.partialTraceRight_eq_of_partialTraceRight_assocIsometry bF bG hρAB hρA
  have hAB_B : LinearMap.partialTraceLeft bE ρAB.toLinearMap = ρB.toLinearMap := by
    rw [← hρAB, LinearMap.assocIsometry_symm_conjStarAlgEquiv_toLinearMap,
      LinearMap.partialTraceLeft_partialTraceRight_assoc, hρBC, hρB]
  -- The two mutual informations, via the mutual-information identity.
  have hBi : ρ.quantumRelativeEntropy (TensorProduct.mapL ρA ρBC) =
      ρA.vonNeumannEntropy + ρBC.vonNeumannEntropy - ρ.vonNeumannEntropy :=
    quantumRelativeEntropy_mapL_partialTrace_eq bE (bF.tensorProduct bG) hρ hρs hρA hρBC
  have hBii : ρAB.quantumRelativeEntropy (TensorProduct.mapL ρA ρB) =
      ρA.vonNeumannEntropy + ρB.vonNeumannEntropy - ρAB.vonNeumannEntropy :=
    quantumRelativeEntropy_mapL_partialTrace_eq bE bF hρABd hρABs hAB_A hAB_B
  -- The two `G`-marginals of the re-associated states: `Tr_G ρ'' = ρ_{EF}`, `Tr_G σ'' = ρ_E ⊗ ρ_F`.
  have e1 : LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight bG
        ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv ρ).toLinearMap) = ρAB := by
    rw [hρAB]; exact ContinuousLinearMap.toLinearMap_toContinuousLinearMap ρAB
  have e2 : LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight bG
        ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv
          (TensorProduct.mapL ρA ρBC)).toLinearMap) = TensorProduct.mapL ρA ρB := by
    rw [LinearMap.assocIsometry_symm_conjStarAlgEquiv_toLinearMap, TensorProduct.toLinearMap_mapL,
      LinearMap.partialTraceRight_assoc_conj_map, hρB, ← TensorProduct.toLinearMap_mapL,
      ContinuousLinearMap.toLinearMap_toContinuousLinearMap]
  -- Invariance of the relative entropy under the associator.
  have hinv : ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv ρ).quantumRelativeEntropy
        ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv (TensorProduct.mapL ρA ρBC)) =
      ρ.quantumRelativeEntropy (TensorProduct.mapL ρA ρBC) :=
    quantumRelativeEntropy_conjStarAlgEquiv_of_isStrictlyPositive _ hρs hσs
  -- Monotonicity of the relative entropy under tracing out `G`, rewritten to the SSA form.
  have hmono := quantumRelativeEntropy_partialTraceRight_le bG hρ''d hσ''d hρ''s hσ''s
  simp only [e1, e2, hinv] at hmono
  rw [hBi, hBii] at hmono
  linarith

end ContinuousLinearMap
