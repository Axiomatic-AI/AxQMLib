/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumStrongSubadditivity

/-!
# The conditional entropy as a relative entropy against a maximally mixed factor

For a strictly positive density operator `ρ` on `E ⊗ F` with `F`-marginal `ρ_F = Tr_E ρ`, the
quantum relative entropy against the product of the **maximally mixed** state on `E` with `ρ_F` is

`D(ρ ‖ (I/d_E) ⊗ ρ_F) = log d_E + S(ρ_F) - S(ρ)`,   `d_E = dim E`.

Since the conditional entropy of `ρ` (in the Nielsen & Chuang convention `S(A|B) = S(A,B) - S(B)`,
with `A = E`, `B = F`) is `S(ρ) - S(ρ_F)`, this rearranges to `D(ρ ‖ (I/d_E) ⊗ ρ_F) = log d_E -
S(A|B)`, i.e. `S(A|B) = log d_E - D(ρ ‖ (I/d_E) ⊗ ρ_F)`. Because `(I/d_E) ⊗ ρ_F` is an **affine**
function of `ρ` (the maximally mixed factor is constant, and `ρ_F = Tr_E ρ` is linear), the joint
convexity of the relative entropy (Lindblad's theorem) transfers to the **concavity** of the
conditional entropy — this is the operator-level argument behind Nielsen & Chuang Corollary 11.13.

## Proof

The identity is the maximally-mixed companion of the mutual-information identity
`ContinuousLinearMap.quantumRelativeEntropy_mapL_partialTrace_eq` and is proved by the same
mechanism: the additive factorization of the operator logarithm on a tensor product
(`IsSelfAdjoint.cfc_log_tensorMap`), the partial-trace/trace duality
(`LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft`), and the self-trace formula
`re tr(ρ log ρ) = -S(ρ)`. The only new ingredient is that the logarithm of the maximally mixed
operator `(1/d_E) • 1` is the scalar `-log d_E • 1` (via `cfc_algebraMap`), so the `E`-factor trace
term collapses to `-log d_E` without reference to the `E`-marginal.

The two `Finset.sum` distributivity helpers `LinearMap.partialTraceLeft_sum_smul` and
`TensorProduct.mapL_sum_smul_right` (the partial trace and the tensor map commute with a finite
`𝕜`-linear combination) support the physics-layer transfer of joint convexity to concavity, where
the mixture `∑ᵢ wᵢ ρᵢ` and its marginal must be threaded through both operations. They are one-line
consequences of the bundled `LinearMap.partialTraceLeftLM` and of `TensorProduct.mapL_sum_right`.

## Main results

* `ContinuousLinearMap.quantumRelativeEntropy_mapL_maximallyMixed_left_eq` — the identity above.
* `LinearMap.partialTraceLeft_sum_smul` / `TensorProduct.mapL_sum_smul_right` — the sum helpers.
-/

@[expose] public section

open Module InnerProductSpace
open scoped TensorProduct

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **The partial trace over the left factor commutes with a finite linear combination**:
`Tr_E (∑ᵢ cᵢ • Tᵢ) = ∑ᵢ cᵢ • Tr_E Tᵢ`. A one-line consequence of the `𝕜`-linearity of the bundled
`LinearMap.partialTraceLeftLM`, used to push a mixture `∑ᵢ wᵢ ρᵢ` through the reduced-state
construction. -/
theorem partialTraceLeft_sum_smul {ι₁ : Type*} [Fintype ι₁] (bE : OrthonormalBasis ι₁ 𝕜 E)
    {ι : Type*} [Fintype ι] (c : ι → 𝕜) (T : ι → (E ⊗[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] F)) :
    LinearMap.partialTraceLeft bE (∑ i, c i • T i)
      = ∑ i, c i • LinearMap.partialTraceLeft bE (T i) := by
  simp only [← LinearMap.partialTraceLeftLM_apply, map_sum, map_smul]

/-- **The partial trace over the right factor commutes with a finite linear combination**:
`Tr_F (∑ᵢ cᵢ • Tᵢ) = ∑ᵢ cᵢ • Tr_F Tᵢ`. The `partialTraceRight` companion of
`partialTraceLeft_sum_smul`, a one-line consequence of the `𝕜`-linearity of the bundled
`LinearMap.partialTraceRightLM`. -/
theorem partialTraceRight_sum_smul {ι₂ : Type*} [Fintype ι₂] (bF : OrthonormalBasis ι₂ 𝕜 F)
    {ι : Type*} [Fintype ι] (c : ι → 𝕜) (T : ι → (E ⊗[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] F)) :
    LinearMap.partialTraceRight bF (∑ i, c i • T i)
      = ∑ i, c i • LinearMap.partialTraceRight bF (T i) := by
  simp only [← LinearMap.partialTraceRightLM_apply, map_sum, map_smul]

end LinearMap

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **The tensor map commutes with a finite linear combination in its second argument**:
`M ⊗ (∑ᵢ cᵢ • gᵢ) = ∑ᵢ cᵢ • (M ⊗ gᵢ)`. A one-line consequence of distributivity over sums
(`TensorProduct.mapL_sum_right`) and homogeneity (`TensorProduct.mapL_smul_right`) in the second
argument, used to push a mixed marginal through the `(I/d) ⊗ ·` construction. -/
theorem mapL_sum_smul_right (M : E →L[𝕜] E) {ι : Type*} [Fintype ι] (c : ι → 𝕜)
    (g : ι → F →L[𝕜] F) :
    TensorProduct.mapL M (∑ i, c i • g i) = ∑ i, c i • TensorProduct.mapL M (g i) := by
  simp only [TensorProduct.mapL_sum_right, TensorProduct.mapL_smul_right]

end TensorProduct

namespace ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℂ E] in
/-- **The operator logarithm of the maximally mixed operator is a scalar**: for the maximally
mixed operator `I/d = (finrank ℂ E : ℂ)⁻¹ • 1` on `E`,  `log(I/d) = -log d • 1`. A companion of
the `*_finrank_inv_smul_one` family (`isDensityOp_`/`isStrictlyPositive_`/`vonNeumannEntropy_`),
computed from `cfc_algebraMap` — the operator is the real scalar `algebraMap ℝ _ ((finrank ℂ E)⁻¹)`
times the identity. -/
theorem cfc_log_finrank_inv_smul_one :
    cfc Real.log ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E))
      = ((- Real.log (Module.finrank ℂ E) : ℝ) : ℂ) • (1 : E →L[ℂ] E) := by
  have : NormedSpace ℝ (E →L[ℂ] E) := NormedSpace.complexToReal
  have : IsScalarTower ℝ ℂ (E →L[ℂ] E) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hM : ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E))
      = algebraMap ℝ (E →L[ℂ] E) ((Module.finrank ℂ E : ℝ)⁻¹) := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (E →L[ℂ] E), Algebra.algebraMap_eq_smul_one]
    norm_num
  rw [hM, cfc_algebraMap, Real.log_inv, IsScalarTower.algebraMap_apply ℝ ℂ (E →L[ℂ] E),
    Algebra.algebraMap_eq_smul_one]
  norm_num

/-- **Relative entropy against a maximally mixed factor computes the conditional entropy.**
For a strictly positive density operator `ρ` on `E ⊗ F` with `F`-marginal `ρ_F = Tr_E ρ`,

`D(ρ ‖ (I/d_E) ⊗ ρ_F) = log d_E + S(ρ_F) - S(ρ)`,   `d_E = dim E`,

where `I/d_E = (finrank ℂ E : ℂ)⁻¹ • 1` is the maximally mixed operator on `E`. Rearranged, this is
`S(ρ) - S(ρ_F) = log d_E - D(ρ ‖ (I/d_E) ⊗ ρ_F)`: the conditional entropy `S(A|B) = S(A,B) - S(B)`
(N&C convention, `A = E`, `B = F`) is an affine image of the relative entropy, whence the joint
convexity of the latter yields the concavity of the former (N&C Corollary 11.13).

The `F`-marginal is supplied as a hypothesis (`hρF`) so a bundled reduced state threads directly.
Faithfulness (`IsStrictlyPositive ρ`) is the finite-branch hypothesis of the relative-entropy
engine; it makes `ρ_F` strictly positive, so `log((I/d_E) ⊗ ρ_F)` factors additively. -/
theorem quantumRelativeEntropy_mapL_maximallyMixed_left_eq [Nontrivial E]
    {ιE : Type*} [Fintype ιE] [Nonempty ιE] (bE : OrthonormalBasis ιE ℂ E)
    {ρ : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρF : F →L[ℂ] F}
    (hρ : ρ.IsDensityOp) (hρs : IsStrictlyPositive ρ)
    (hρF : LinearMap.partialTraceLeft bE ρ.toLinearMap = ρF.toLinearMap) :
    ρ.quantumRelativeEntropy
        (TensorProduct.mapL ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E)) ρF) =
      Real.log (Module.finrank ℂ E) + ρF.vonNeumannEntropy - ρ.vonNeumannEntropy := by
  have hMd0 : ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E)).IsDensityOp :=
    isDensityOp_finrank_inv_smul_one
  have hMs0 : IsStrictlyPositive ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E)) :=
    isStrictlyPositive_finrank_inv_smul_one
  set M : E →L[ℂ] E := (Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E) with hMdef
  have hMsa : IsSelfAdjoint M := hMd0.isPositive.isSelfAdjoint
  have hρFd : ρF.IsDensityOp := hρ.of_partialTraceLeft_eq bE hρF
  have hρFs : IsStrictlyPositive ρF := hρs.of_partialTraceLeft_eq bE hρF
  have hEpos := fun i => hMs0.eigenvalues_pos hMsa.isSymmetric rfl i
  have hFpos := fun j => hρFs.eigenvalues_pos hρFd.isPositive.isSelfAdjoint.isSymmetric rfl j
  -- The operator logarithm factors additively over the tensor product.
  have hlog : cfc Real.log (TensorProduct.mapL M ρF) =
      TensorProduct.mapL (cfc Real.log M) (1 : F →L[ℂ] F) +
        TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log ρF) :=
    IsSelfAdjoint.cfc_log_tensorMap hMsa hρFd.isPositive.isSelfAdjoint rfl rfl hEpos hFpos
  -- The `E`-factor trace term collapses to `-log d_E` (as `tr ρ = 1`), using
  -- `log(I/d) = -log d • 1` (`cfc_log_finrank_inv_smul_one`).
  have ht1 : LinearMap.trace ℂ (E ⊗[ℂ] F)
        ((TensorProduct.mapL (cfc Real.log M) (1 : F →L[ℂ] F)).toLinearMap ∘ₗ ρ.toLinearMap)
      = ((- Real.log (Module.finrank ℂ E) : ℝ) : ℂ) := by
    rw [hMdef, cfc_log_finrank_inv_smul_one, TensorProduct.mapL_smul_left, TensorProduct.mapL_one,
      ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_comp, map_smul,
      ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.id_comp, hρ.2]
    simp
  -- The `F`-factor trace term is `-S(ρ_F)` via partial-trace duality.
  have ht2 : LinearMap.trace ℂ (E ⊗[ℂ] F)
        ((TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log ρF)).toLinearMap ∘ₗ ρ.toLinearMap) =
      LinearMap.trace ℂ F ((cfc Real.log ρF).toLinearMap ∘ₗ ρF.toLinearMap) := by
    rw [TensorProduct.toLinearMap_mapL, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
      LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft bE, hρF]
  have hre : RCLike.re ((↑(- Real.log (Module.finrank ℂ E)) : ℂ))
      = - Real.log (Module.finrank ℂ E) := RCLike.ofReal_re _
  rw [hρ.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub, hlog,
    ContinuousLinearMap.toLinearMap_add, LinearMap.add_comp, map_add, ht1, ht2, map_add,
    hρFd.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy, hre]
  ring

end ContinuousLinearMap
