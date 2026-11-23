/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFCTensor
public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import ToMathlib.Analysis.InnerProductSpace.LiebConcavityTrace
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import ToMathlib.Analysis.Convex.FunctionTopology

/-!
# Quantum relative entropy

For density operators `ρ, σ : E →L[𝕜] E` on a finite-dimensional inner product space (with
`𝕜 = ℂ` in practice; see `quantumRelativeEntropy`'s docstring for the RCLike parametrization
details), the **(Umegaki) quantum relative entropy** of `ρ` with respect to `σ` is

`D(ρ ‖ σ) := re tr(ρ log ρ) - re tr(ρ log σ)`

where `log` denotes the operator logarithm via the continuous functional calculus. It is
finite whenever `σ` has all-positive eigenvalues (so that `log σ` is defined on the spectrum)
and is the quantum analogue of the classical Kullback–Leibler divergence.

We define it as a real-valued function on arbitrary continuous linear operators, with a
junk-value pattern: when `ρ`, `σ` are not density operators (or `σ` has a zero eigenvalue,
making `log σ` ill-defined), the expression still parses but carries no quantum-information
meaning.

## Main definitions

- `ContinuousLinearMap.quantumRelativeEntropy : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ`

## Main results

- `IsDensityOp.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub`: the equivalent form
  `D(ρ ‖ σ) = -S(ρ) - re tr((cfc log σ) ∘ ρ)` for `ρ` density with positive spectrum.
- `IsDensityOp.quantumRelativeEntropy_self`: `D(ρ ‖ ρ) = 0`.
- `IsDensityOp.quantumRelativeEntropy_nonneg`: **Klein–Gibbs inequality** — `D(ρ ‖ σ) ≥ 0`
  for density `ρ, σ` with `σ` positive-spectrum. Immediate corollary of operator Klein's
  inequality (`vonNeumannEntropy_le_neg_re_trace_cfc_log_comp`).

## Joint convexity (Lindblad's theorem)

- `ContinuousLinearMap.convexOn_quantumRelativeEntropy`: **Lindblad's theorem** — `D(ρ ‖ σ)`
  is jointly convex on pairs of strictly positive operators on `EuclideanSpace ℂ ι`. Proved as
  the `p → 0⁺` limit of the jointly convex approximants `F_p` (the Lieb trace form
  `concaveAt_trace` gives the convexity of `F_p`; the trace-rate limit
  `tendsto_quantumRelativeEntropyApprox` identifies the limit).

## Tensor additivity (§2.37 P3.c)

- `IsDensityOp.quantumRelativeEntropy_tensorMap`:
  `D(ρ₁⊗ρ₂ ‖ σ₁⊗σ₂) = D(ρ₁‖σ₁) + D(ρ₂‖σ₂)` for density operators on abstract finite-dim
  complex Hilbert spaces. Uses `IsSelfAdjoint.cfc_log_tensorMap` (the tensor-product log
  identity) + `LinearMap.trace_tensorProduct'` + density-op trace-1.
-/

@[expose] public section

open scoped Topology
open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [CompleteSpace E]
    [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- The **(Umegaki) quantum relative entropy** of `ρ` with respect to `σ`:
`D(ρ ‖ σ) := re tr(ρ log ρ) - re tr(ρ log σ)`, where the operator logarithm is taken via the
continuous functional calculus. Junk-valued (still parses but carries no quantum-information
meaning) when the arguments are not density operators or `σ` has a zero eigenvalue.

Stated RCLike-parametrically with explicit `Algebra ℝ` + `IsScalarTower` + `CFC ℝ` instance
hypotheses (the canonical `StarOrder.lean` template).
The hypotheses synthesize automatically for `𝕜 = ℂ`. For `𝕜 = ℝ` they would require a
real-CFC framework which is currently absent from Mathlib. -/
noncomputable def quantumRelativeEntropy (ρ σ : E →L[𝕜] E) : ℝ :=
  RCLike.re (LinearMap.trace 𝕜 E ((cfc Real.log ρ).toLinearMap ∘ₗ ρ.toLinearMap)) -
    RCLike.re (LinearMap.trace 𝕜 E ((cfc Real.log σ).toLinearMap ∘ₗ ρ.toLinearMap))

omit [FiniteDimensional 𝕜 E] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- Unfold of `quantumRelativeEntropy` to the two-term trace expression. -/
theorem quantumRelativeEntropy_def (ρ σ : E →L[𝕜] E) :
    quantumRelativeEntropy ρ σ =
      RCLike.re (LinearMap.trace 𝕜 E ((cfc Real.log ρ).toLinearMap ∘ₗ ρ.toLinearMap)) -
        RCLike.re (LinearMap.trace 𝕜 E ((cfc Real.log σ).toLinearMap ∘ₗ ρ.toLinearMap)) :=
  rfl

omit [FiniteDimensional 𝕜 E] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- `D(ρ ‖ ρ) = 0`: the relative entropy of any operator against itself vanishes (true
unconditionally from the definition's `tr(X) - tr(X)` shape). -/
@[simp] theorem quantumRelativeEntropy_self (ρ : E →L[𝕜] E) :
    quantumRelativeEntropy ρ ρ = 0 :=
  sub_self _

end RCLike

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]

/-- `D(ρ ‖ σ) = -S(ρ) - re tr((cfc log σ) ∘ ρ)` for *any* density `ρ` (no positivity needed).
Combines `re_trace_cfc_log_self_eq_neg_vonNeumannEntropy` with the definition. -/
theorem IsDensityOp.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub
    {ρ σ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) :
    quantumRelativeEntropy ρ σ = -ρ.vonNeumannEntropy -
      RCLike.re (LinearMap.trace ℂ E ((cfc Real.log σ).toLinearMap ∘ₗ ρ.toLinearMap)) := by
  rw [quantumRelativeEntropy_def, hρ.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy]

/-- **Klein–Gibbs inequality**: the quantum relative entropy of density operators is
non-negative. For density `ρ, σ : E →L[ℂ] E` with `σ`'s eigenvalues all positive,
`D(ρ ‖ σ) ≥ 0`. Immediate corollary of operator Klein's inequality
(`vonNeumannEntropy_le_neg_re_trace_cfc_log_comp`) plus the self-trace expansion
(`re_trace_cfc_log_self_eq_neg_vonNeumannEntropy`). -/
theorem IsDensityOp.quantumRelativeEntropy_nonneg {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) :
    0 ≤ quantumRelativeEntropy ρ σ := by
  rw [hρ.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub, sub_nonneg]
  linarith [hρ.vonNeumannEntropy_le_neg_re_trace_cfc_log_comp hσ hσ_pos]

section ConjInvariance

-- `IsScalarTower ℝ ℂ (E →L[ℂ] E)` is mathematically valid but not a global instance for abstract
-- `E` (it is the RCLike section's standing assumption); `StarAlgHom.map_cfc` requires it
-- explicitly. It synthesizes for the concrete `EuclideanSpace ℂ ι` consumers (DPI).
variable [IsScalarTower ℝ ℂ (E →L[ℂ] E)]

/-- **Unitary invariance of the quantum relative entropy.** For a linear isometry equivalence
`e : E ≃ₗᵢ[ℂ] F` (a unitary, possibly between different spaces) and self-adjoint `ρ, σ` whose
spectra avoid `0` (so `log` is defined), `D(e ρ e⁻¹ ‖ e σ e⁻¹) = D(ρ ‖ σ)`. Sibling of
`vonNeumannEntropy_conjStarAlgEquiv` / `traceDistance_conjStarAlgEquiv`; the load-bearer for the
partial-trace DPI (twirl) argument, and — in its cross-space form — for transporting the Lindblad
joint convexity to abstract finite-dimensional spaces. Each trace term is preserved by
`conjStarAlgEquiv_cfc_real_log` + `conjStarAlgEquiv` multiplicativity + `trace_conjStarAlgEquiv`. -/
theorem quantumRelativeEntropy_conjStarAlgEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [CompleteSpace F] [IsScalarTower ℝ ℂ (F →L[ℂ] F)] (e : E ≃ₗᵢ[ℂ] F) {ρ σ : E →L[ℂ] E}
    (hρ : IsSelfAdjoint ρ) (hρc : ContinuousOn Real.log (spectrum ℝ ρ))
    (hσ : IsSelfAdjoint σ) (hσc : ContinuousOn Real.log (spectrum ℝ σ)) :
    quantumRelativeEntropy (e.conjStarAlgEquiv ρ) (e.conjStarAlgEquiv σ) =
      quantumRelativeEntropy ρ σ := by
  rw [quantumRelativeEntropy_def, quantumRelativeEntropy_def,
    e.conjStarAlgEquiv_cfc_real_log hρ hρc, e.conjStarAlgEquiv_cfc_real_log hσ hσc]
  congr 1 <;>
    rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.mul_def, ← map_mul,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.trace_conjStarAlgEquiv,
      ContinuousLinearMap.toLinearMap_comp]

end ConjInvariance

/-! ### Tensor additivity -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Trace of tensor-product composition factors** (CLM, ℂ-finite-dim): for any
`A, C : E →L[ℂ] E` and `B, D : F →L[ℂ] F`,
`tr((mapL A B) ∘ (mapL C D)) = tr(A ∘ C) * tr(B ∘ D)`. Direct consequence of
`TensorProduct.map_comp` (composition factors through `TensorProduct.map`) and
`LinearMap.trace_tensorProduct'` (trace of tensor map is product of traces). -/
theorem trace_mapL_comp_mapL
    (A C : E →L[ℂ] E) (B D : F →L[ℂ] F) :
    LinearMap.trace ℂ (E ⊗[ℂ] F)
        ((TensorProduct.mapL A B).toLinearMap ∘ₗ (TensorProduct.mapL C D).toLinearMap) =
      LinearMap.trace ℂ E (A.toLinearMap ∘ₗ C.toLinearMap) *
        LinearMap.trace ℂ F (B.toLinearMap ∘ₗ D.toLinearMap) := by
  rw [TensorProduct.toLinearMap_mapL, TensorProduct.toLinearMap_mapL,
    ← TensorProduct.map_comp, LinearMap.trace_tensorProduct']

/-- **A tensor product of density operators is a density operator.** Positivity from
`TensorProduct.mapL_nonneg`; trace `1` from `trace (ρ₁ ⊗ ρ₂) = tr ρ₁ · tr ρ₂ = 1`. The
density-operator companion of `mapL_nonneg` / `mapL_isStrictlyPositive`. -/
theorem IsDensityOp.mapL {ρ₁ : E →L[ℂ] E} {ρ₂ : F →L[ℂ] F}
    (hρ₁ : ρ₁.IsDensityOp) (hρ₂ : ρ₂.IsDensityOp) : (TensorProduct.mapL ρ₁ ρ₂).IsDensityOp := by
  refine ⟨nonneg_iff_isPositive.mp (TensorProduct.mapL_nonneg hρ₁.nonneg hρ₂.nonneg), ?_⟩
  rw [TensorProduct.toLinearMap_mapL, LinearMap.trace_tensorProduct', hρ₁.trace_eq_one,
    hρ₂.trace_eq_one, mul_one]

/-- **Binary tensor-product additivity of the quantum relative entropy.** For density
operators `ρ₁, σ₁ : E →L[ℂ] E` and `ρ₂, σ₂ : F →L[ℂ] F` with strictly positive eigenvalues:

  `D(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = D(ρ₁ ‖ σ₁) + D(ρ₂ ‖ σ₂)`.

Uses `IsSelfAdjoint.cfc_log_tensorMap` to expand `log(ρ₁ ⊗ ρ₂) = log ρ₁ ⊗ I + I ⊗ log ρ₂`
(and likewise for σ), then distributes the trace via `trace_mapL_comp_mapL` and absorbs
`tr(ρᵢ) = 1` from `IsDensityOp.trace_eq_one`.
-/
theorem IsDensityOp.quantumRelativeEntropy_tensorMap
    {ρ₁ σ₁ : E →L[ℂ] E} (hρ₁ : ρ₁.IsDensityOp)
    (hρ₁_pos : ∀ i, 0 < hρ₁.isSymmetric.eigenvalues rfl i)
    {ρ₂ σ₂ : F →L[ℂ] F} (hρ₂ : ρ₂.IsDensityOp)
    (hρ₂_pos : ∀ j, 0 < hρ₂.isSymmetric.eigenvalues rfl j)
    (hσ₁ : σ₁.IsDensityOp) (hσ₁_pos : ∀ i, 0 < hσ₁.isSymmetric.eigenvalues rfl i)
    (hσ₂ : σ₂.IsDensityOp) (hσ₂_pos : ∀ j, 0 < hσ₂.isSymmetric.eigenvalues rfl j) :
    quantumRelativeEntropy (TensorProduct.mapL ρ₁ ρ₂) (TensorProduct.mapL σ₁ σ₂) =
      quantumRelativeEntropy ρ₁ σ₁ + quantumRelativeEntropy ρ₂ σ₂ := by
  have h_log_ρ : cfc Real.log (TensorProduct.mapL ρ₁ ρ₂) =
      TensorProduct.mapL (cfc Real.log ρ₁) (1 : F →L[ℂ] F) +
        TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log ρ₂) :=
    IsSelfAdjoint.cfc_log_tensorMap hρ₁.isPositive.isSelfAdjoint hρ₂.isPositive.isSelfAdjoint
      rfl rfl hρ₁_pos hρ₂_pos
  have h_log_σ : cfc Real.log (TensorProduct.mapL σ₁ σ₂) =
      TensorProduct.mapL (cfc Real.log σ₁) (1 : F →L[ℂ] F) +
        TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log σ₂) :=
    IsSelfAdjoint.cfc_log_tensorMap hσ₁.isPositive.isSelfAdjoint hσ₂.isPositive.isSelfAdjoint
      rfl rfl hσ₁_pos hσ₂_pos
  simp only [quantumRelativeEntropy_def, h_log_ρ, h_log_σ, ContinuousLinearMap.toLinearMap_add,
    LinearMap.add_comp, map_add, trace_mapL_comp_mapL,
    ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.id_comp,
    hρ₁.trace_eq_one, hρ₂.trace_eq_one, mul_one, one_mul]
  ring

end Complex

section Lindblad

open scoped ComplexOrder
open Filter

variable {ι : Type*} [Fintype ι]

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` `Pow`/`NonnegSpectrumClass` instances on the
-- `EuclideanSpace ℂ ι →L …` operator algebra (see `LiebConcavityTrace`); near-minimal.
/-- The Lindblad approximant `F_p(A, B) = p⁻¹ (re tr A - re tr (A^{1-p} B^p))` to the quantum
relative entropy. -/
noncomputable def quantumRelativeEntropyApprox (p : ℝ)
    (X : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) ×
      (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) : ℝ :=
  p⁻¹ * (RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) X.1.toLinearMap) -
    RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
      ((X.1 ^ ((1 : ℝ) - p)) ∘L (X.2 ^ p)).toLinearMap))

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` instances on the operator algebra.
/-- Unfold lemma for the Lindblad approximant. -/
theorem quantumRelativeEntropyApprox_def (p : ℝ)
    (X : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) ×
      (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) :
    quantumRelativeEntropyApprox p X =
      p⁻¹ * (RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) X.1.toLinearMap) -
        RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          ((X.1 ^ ((1 : ℝ) - p)) ∘L (X.2 ^ p)).toLinearMap)) :=
  rfl

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` + `whnf` budget for the CFC `rpow` instances/reductions on the
-- `EuclideanSpace ℂ ι →L …` operator algebra.
/-- `a^{1-p} a^p = a` for a strictly positive operator (the numerator-factoring identity behind
the Lindblad limit). -/
theorem rpow_one_sub_mul_rpow_self {A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hA : IsStrictlyPositive A) (p : ℝ) : A ^ (1 - p) * A ^ p = A := by
  rw [← CFC.rpow_add hA.isUnit, sub_add_cancel, CFC.rpow_one A hA.nonneg]

set_option linter.unusedFintypeInType false in
-- `[Fintype ι]` occurs in the statement only inside instance proofs on `EuclideanSpace ℂ ι`, so
-- it can be neither omitted nor weakened to `Finite ι` here.
/-- `re tr` is `ℝ`-homogeneous in the operator: `re tr (r • X) = r * re tr X`. -/
theorem re_trace_smul (r : ℝ) (X : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (r • X : _).toLinearMap) =
      r * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) X.toLinearMap) := by
  rw [show (r • X : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) = (r : ℂ) • X from
      (Complex.coe_smul r X).symm, ContinuousLinearMap.toLinearMap_smul, map_smul]
  simp

set_option linter.unusedFintypeInType false in
-- `[Fintype ι]` occurs in the statement only inside instance proofs on `EuclideanSpace ℂ ι`, so
-- it can be neither omitted nor weakened to `Finite ι` here.
/-- `re tr` is additive on differences: `re tr (X - Y) = re tr X - re tr Y`. -/
theorem re_trace_sub (X Y : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (X - Y : _).toLinearMap) =
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) X.toLinearMap) -
        RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) Y.toLinearMap) := by
  rw [ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub]

set_option linter.unusedFintypeInType false in
-- `[Fintype ι]` occurs in the statement only inside instance proofs on `EuclideanSpace ℂ ι`, so
-- it can be neither omitted nor weakened to `Finite ι` here.
/-- `re tr` is `ℝ`-linear in the operator: `re tr (a • C + b • D) = a re tr C + b re tr D`. -/
theorem re_trace_add_smul (a b : ℝ) (C D : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (a • C + b • D : _).toLinearMap) =
      a * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) C.toLinearMap) +
        b * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) D.toLinearMap) := by
  rw [ContinuousLinearMap.toLinearMap_add, map_add, map_add, re_trace_smul, re_trace_smul]

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` `Pow`/`NonnegSpectrumClass` instances on the
-- `EuclideanSpace ℂ ι →L …` operator algebra (see `LiebConcavityTrace`); near-minimal.
theorem convexOn_quantumRelativeEntropyApprox {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ ({a | IsStrictlyPositive a} ×ˢ {a | IsStrictlyPositive a})
      (quantumRelativeEntropyApprox (ι := ι) p) := by
  refine ⟨convex_isStrictlyPositive.prod convex_isStrictlyPositive, ?_⟩
  rintro ⟨A₁, B₁⟩ ⟨hA₁, hB₁⟩ ⟨A₂, B₂⟩ ⟨hA₂, hB₂⟩ a b ha hb hab
  have key := TensorProduct.concaveAt_trace
    (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (q := 1 - p) (r := p)
    (by linarith) hp.le (by linarith) hA₁ hA₂ hB₁ hB₂ ha hb hab
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_comp, smul_eq_mul] at key
  simp only [quantumRelativeEntropyApprox_def, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, re_trace_add_smul, smul_eq_mul]
  nlinarith [key, mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ p⁻¹)]

set_option maxHeartbeats 400000 in
-- The general `maxHeartbeats` bump covers the CFC `whnf` reductions accumulated across the
-- `rpow`/`log` limit witnesses (`h1`, `h2`, `hG`).
set_option synthInstance.maxHeartbeats 80000 in
-- The `synthInstance` bump covers the CFC `rpow` `Pow`/`NonnegSpectrumClass` instances on the
-- `EuclideanSpace ℂ ι →L …` operator algebra (see `LiebConcavityTrace`).
/-- **Lindblad limit form of the quantum relative entropy** (the trace-rate limit). For strictly
positive `A, B`, the approximants `F_p(A, B)` converge to `D(A ‖ B)` as `p → 0⁺`:

  `lim_{p → 0⁺} p⁻¹ (tr A - tr (A^{1-p} B^p)) = re tr (A log A) - re tr (A log B)`.

The numerator factors as `tr (A^{1-p} (A^p - B^p))`, so the rate is the product of the
continuous-in-exponent factor `A^{1-p} → A` (`CFC.continuous_const_rpow`) and the difference of
two single-operator logarithm limits `p⁻¹ (A^p - B^p) → log A - log B`
(`CFC.tendsto_cfc_rpow_sub_one_log`); trace-continuity (`ContinuousLinearMap.continuous_trace`)
then transports the operator limit to the scalar. -/
theorem tendsto_quantumRelativeEntropyApprox
    {A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    Tendsto (fun p : ℝ ↦ quantumRelativeEntropyApprox p (A, B)) (𝓝[>] 0)
      (𝓝 (quantumRelativeEntropy A B)) := by
  -- factor 1: `A^{1-p} → A`
  have h1 : Tendsto (fun p : ℝ ↦ A ^ (1 - p)) (𝓝[>] 0) (𝓝 A) := by
    have h : Tendsto (fun p : ℝ ↦ A ^ (1 - p)) (𝓝[>] 0) (𝓝 (A ^ (1 - (0 : ℝ)))) :=
      ((CFC.continuous_const_rpow hA).comp (continuous_const.sub continuous_id)).continuousWithinAt
    simpa [CFC.rpow_one A hA.nonneg] using h
  -- factor 2: `p⁻¹ (A^p - B^p) → log A - log B`
  have h2 : Tendsto (fun p : ℝ ↦ p⁻¹ • (A ^ p - B ^ p)) (𝓝[>] 0)
      (𝓝 (CFC.log A - CFC.log B)) := by
    have hAlim := (CFC.tendsto_cfc_rpow_sub_one_log (a := A) hA).congr fun p ↦
      CFC.cfc_p_inv_rpow_sub_one_eq p hA
    have hBlim := (CFC.tendsto_cfc_rpow_sub_one_log (a := B) hB).congr fun p ↦
      CFC.cfc_p_inv_rpow_sub_one_eq p hB
    exact (hAlim.sub hBlim).congr fun p ↦ by rw [← smul_sub]; congr 1; abel
  -- the operator-valued limit and its continuous image under `re tr`
  have hG := h1.mul h2
  have hcont : Continuous (fun X : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι ↦
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) X.toLinearMap)) :=
    RCLike.continuous_re.comp ContinuousLinearMap.continuous_trace
  -- the approximant equals `re tr` of the operator-valued function
  have hEq : ∀ p : ℝ, quantumRelativeEntropyApprox p (A, B) =
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (A ^ (1 - p) * (p⁻¹ • (A ^ p - B ^ p))).toLinearMap) := by
    intro p
    rw [mul_smul_comm, mul_sub, rpow_one_sub_mul_rpow_self hA, re_trace_smul, re_trace_sub,
      quantumRelativeEntropyApprox_def]
    rfl
  -- the limit point is the quantum relative entropy
  have hqre : RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
      (A * (CFC.log A - CFC.log B)).toLinearMap) = quantumRelativeEntropy A B := by
    rw [mul_sub, re_trace_sub, quantumRelativeEntropy_def]
    congr 1 <;>
      (rw [ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm]; rfl)
  rw [← hqre]
  exact ((hcont.tendsto _).comp hG).congr fun p ↦ (hEq p).symm

/-- **Lindblad's theorem**: the quantum relative entropy `D(ρ ‖ σ) = re tr(ρ log ρ) -
re tr(ρ log σ)` is **jointly convex** on pairs of strictly positive operators. Obtained as the
pointwise `p → 0⁺` limit of the jointly convex approximants `F_p`
(`convexOn_quantumRelativeEntropyApprox` + `tendsto_quantumRelativeEntropyApprox`), via
`ConvexOn.of_tendsto_pointwise_on`. -/
theorem convexOn_quantumRelativeEntropy :
    ConvexOn ℝ ({a | IsStrictlyPositive a} ×ˢ {a | IsStrictlyPositive a})
      (fun X : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) ×
        (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) ↦ quantumRelativeEntropy X.1 X.2) := by
  have hev : ∀ᶠ p : ℝ in 𝓝[>] 0, 0 < p ∧ p ≤ 1 :=
    eventually_mem_nhdsWithin.mono (fun p hp ↦ hp) |>.and
      ((eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  refine ConvexOn.of_tendsto_pointwise_on (l := 𝓝[>] (0 : ℝ))
    (F := quantumRelativeEntropyApprox)
    (convex_isStrictlyPositive.prod convex_isStrictlyPositive) ?_ ?_
  · filter_upwards [hev] with p hp using convexOn_quantumRelativeEntropyApprox hp.1 hp.2
  · rintro ⟨A, B⟩ ⟨hA, hB⟩
    exact tendsto_quantumRelativeEntropyApprox hA hB

/-- **Joint convexity of the quantum relative entropy, binary form** (the workhorse for SSA / data
processing): for strictly positive `ρ₁, ρ₂, σ₁, σ₂` and convex weights `t + s = 1`,

  `D(t ρ₁ + s ρ₂ ‖ t σ₁ + s σ₂) ≤ t D(ρ₁ ‖ σ₁) + s D(ρ₂ ‖ σ₂)`.

The pointwise unfolding of `convexOn_quantumRelativeEntropy`. Density-operator consumers obtain the
strict-positivity hypotheses from `IsDensityOp.isStrictlyPositive` (full-rank states). -/
theorem quantumRelativeEntropy_jointly_convex
    {ρ₁ ρ₂ σ₁ σ₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hρ₁ : IsStrictlyPositive ρ₁) (hρ₂ : IsStrictlyPositive ρ₂)
    (hσ₁ : IsStrictlyPositive σ₁) (hσ₂ : IsStrictlyPositive σ₂)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    quantumRelativeEntropy (t • ρ₁ + s • ρ₂) (t • σ₁ + s • σ₂) ≤
      t * quantumRelativeEntropy ρ₁ σ₁ + s * quantumRelativeEntropy ρ₂ σ₂ := by
  simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using
    convexOn_quantumRelativeEntropy.2 (Set.mk_mem_prod hρ₁ hσ₁) (Set.mk_mem_prod hρ₂ hσ₂) ht hs hts

end Lindblad

/-! ### Joint convexity on abstract finite-dimensional spaces

The Lindblad convexity (`convexOn_quantumRelativeEntropy`) is proved on `EuclideanSpace ℂ ι`
(the pinning is essential — Lieb's Theorem 1 routes through `EuclideanSpace.transposeOp`). For the
partial-trace data-processing inequality we need it on an abstract finite-dimensional space
`E ⊗ F`. We transport it along the orthonormal-basis isometry `E ≃ₗᵢ EuclideanSpace ℂ ι` using
unitary invariance of `D`. -/
section AbstractConvexity

-- `continuousOn_log_spectrum` is general (no relative-entropy content); upstream-relocation
-- candidate → `CFC.lean`. (`conjStarAlgEquiv_isStrictlyPositive_iff` now lives in `Positive.lean`,
-- beside `conjStarAlgEquiv_isPositive_iff`.)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] [IsScalarTower ℝ ℂ (E →L[ℂ] E)]

omit [FiniteDimensional ℂ E] [IsScalarTower ℝ ℂ (E →L[ℂ] E)] in
/-- `log` is continuous on the spectrum of a strictly positive operator (which is `⊆ (0, ∞)`). -/
theorem IsStrictlyPositive.continuousOn_log_spectrum {T : E →L[ℂ] E} (hT : IsStrictlyPositive T) :
    ContinuousOn Real.log (spectrum ℝ T) :=
  Real.continuousOn_log.mono fun _ hx ↦ (hT.spectrum_pos hx).ne'

/-- **Unitary invariance of `D`, no positivity needed.** For self-adjoint `ρ, σ` on a
finite-dimensional space, conjugating both by a linear isometry equivalence leaves the quantum
relative entropy unchanged. The `log`-continuity premises of the base `conjStarAlgEquiv` lemma are
discharged by `IsSelfAdjoint.continuousOn_log_spectrum` (the spectrum is finite). The canonical
invariance engine; also the form used to transport `D` across a Stinespring
isometry-onto-its-range. -/
theorem quantumRelativeEntropy_conjStarAlgEquiv_of_isSelfAdjoint
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [CompleteSpace F] [IsScalarTower ℝ ℂ (F →L[ℂ] F)] (e : E ≃ₗᵢ[ℂ] F) {ρ σ : E →L[ℂ] E}
    (hρ : IsSelfAdjoint ρ) (hσ : IsSelfAdjoint σ) :
    quantumRelativeEntropy (e.conjStarAlgEquiv ρ) (e.conjStarAlgEquiv σ) =
      quantumRelativeEntropy ρ σ :=
  quantumRelativeEntropy_conjStarAlgEquiv e hρ (IsSelfAdjoint.continuousOn_log_spectrum hρ) hσ
    (IsSelfAdjoint.continuousOn_log_spectrum hσ)

/-- Unitary invariance of `D` for strictly positive operators — the strict-positivity convenience
form of `quantumRelativeEntropy_conjStarAlgEquiv_of_isSelfAdjoint` (`IsStrictlyPositive` ⟹
`IsSelfAdjoint`). -/
theorem quantumRelativeEntropy_conjStarAlgEquiv_of_isStrictlyPositive
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [CompleteSpace F] [IsScalarTower ℝ ℂ (F →L[ℂ] F)] (e : E ≃ₗᵢ[ℂ] F) {ρ σ : E →L[ℂ] E}
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    quantumRelativeEntropy (e.conjStarAlgEquiv ρ) (e.conjStarAlgEquiv σ) =
      quantumRelativeEntropy ρ σ :=
  quantumRelativeEntropy_conjStarAlgEquiv_of_isSelfAdjoint e hρ.isSelfAdjoint hσ.isSelfAdjoint

section IsometryConj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [CompleteSpace H]

variable [IsScalarTower ℝ ℂ (H →L[ℂ] H)]

/-- **Invariance of the quantum relative entropy under conjugation by an isometry.** For
`V : E →L[ℂ] H` an isometry (`V† V = 1`) and self-adjoint `ρ, σ`,
`D(V ρ V† ‖ V σ V†) = D(ρ ‖ σ)`. The non-surjective companion to the unitary-equivalence form
`quantumRelativeEntropy_conjStarAlgEquiv_of_isSelfAdjoint`: `V` need not be onto, because the zero
eigenspace `(ran V)ᗮ` of `V ρ V†` is harmless (`Real.log 0 = 0`, via `cfc_conj_isometry`) and trace
cyclicity (`trace_conj_isometry`) collapses the `V† V`. The dilation half of the Stinespring
channel-DPI: with the partial-trace DPI it yields `D(Φρ ‖ Φσ) ≤ D(ρ ‖ σ)`. -/
theorem quantumRelativeEntropy_conj_isometry {V : E →L[ℂ] H} (hV : V.adjoint ∘L V = 1)
    {ρ σ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) (hσ : IsSelfAdjoint σ) :
    quantumRelativeEntropy (V ∘L ρ ∘L V.adjoint) (V ∘L σ ∘L V.adjoint)
      = quantumRelativeEntropy ρ σ := by
  have hterm : ∀ {X : E →L[ℂ] E}, IsSelfAdjoint X →
      LinearMap.trace ℂ H ((cfc Real.log (V ∘L X ∘L V.adjoint)).toLinearMap
        ∘ₗ (V ∘L ρ ∘L V.adjoint).toLinearMap)
        = LinearMap.trace ℂ E ((cfc Real.log X).toLinearMap ∘ₗ ρ.toLinearMap) := by
    intro X hX
    rw [cfc_conj_isometry hV hX Real.log_zero, ← ContinuousLinearMap.toLinearMap_comp,
      ← conjIsometryₙ_apply hV, ← conjIsometryₙ_apply hV, ← ContinuousLinearMap.mul_def,
      ← map_mul, conjIsometryₙ_apply, trace_conj_isometry hV, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.toLinearMap_comp]
  rw [quantumRelativeEntropy_def, quantumRelativeEntropy_def, hterm hρ, hterm hσ]

end IsometryConj

/-- **n-ary joint convexity of the quantum relative entropy** on an abstract finite-dimensional
complex inner product space (`EuclideanSpace`-form transported along an orthonormal basis):
`D(∑ wₖ ρₖ ‖ ∑ wₖ σₖ) ≤ ∑ wₖ D(ρₖ ‖ σₖ)` for strictly positive `ρₖ, σₖ` and convex weights `wₖ`.
The partial-trace data-processing inequality applies this on `E ⊗ F`. -/
theorem quantumRelativeEntropy_jointly_convex_sum {κ : Type*} (t : Finset κ)
    {ρ σ : κ → E →L[ℂ] E} {w : κ → ℝ}
    (hρ : ∀ k ∈ t, IsStrictlyPositive (ρ k)) (hσ : ∀ k ∈ t, IsStrictlyPositive (σ k))
    (hw : ∀ k ∈ t, 0 ≤ w k) (hsum : ∑ k ∈ t, w k = 1) :
    quantumRelativeEntropy (∑ k ∈ t, w k • ρ k) (∑ k ∈ t, w k • σ k) ≤
      ∑ k ∈ t, w k * quantumRelativeEntropy (ρ k) (σ k) := by
  set Φ := (stdOrthonormalBasis ℂ E).repr with hΦ
  have : IsScalarTower ℝ ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsmul : ∀ (c : ℝ) (A : E →L[ℂ] E),
      Φ.conjStarAlgEquiv (c • A) = c • Φ.conjStarAlgEquiv A := fun c A ↦ by
    rw [← algebraMap_smul ℂ c A, map_smul, algebraMap_smul]
  have hρs : IsStrictlyPositive (∑ k ∈ t, w k • ρ k) :=
    (convex_isStrictlyPositive (A := E →L[ℂ] E)).sum_mem hw hsum hρ
  have hσs : IsStrictlyPositive (∑ k ∈ t, w k • σ k) :=
    (convex_isStrictlyPositive (A := E →L[ℂ] E)).sum_mem hw hsum hσ
  rw [← quantumRelativeEntropy_conjStarAlgEquiv_of_isStrictlyPositive Φ hρs hσs, map_sum, map_sum]
  simp_rw [hsmul]
  have hEuc := convexOn_quantumRelativeEntropy.map_sum_le
    (p := fun k ↦ (Φ.conjStarAlgEquiv (ρ k), Φ.conjStarAlgEquiv (σ k))) hw hsum
    fun k hk ↦ Set.mk_mem_prod (Φ.conjStarAlgEquiv_isStrictlyPositive_iff.mpr (hρ k hk))
      (Φ.conjStarAlgEquiv_isStrictlyPositive_iff.mpr (hσ k hk))
  simp only [Prod.smul_mk, Prod.fst_sum, Prod.snd_sum, smul_eq_mul] at hEuc
  refine hEuc.trans (le_of_eq (Finset.sum_congr rfl fun k hk ↦ ?_))
  rw [quantumRelativeEntropy_conjStarAlgEquiv_of_isStrictlyPositive Φ (hρ k hk) (hσ k hk)]

/-- **Monotonicity of the quantum relative entropy under a mixed-unitary (random-unitary)
channel.** For a family `e : κ → (E ≃ₗᵢ[ℂ] E)` of unitaries, strictly positive operators `ρ, σ`,
and convex weights `w` on a `Finset t` (`w k ≥ 0`, `∑ w k = 1`),
`D(∑ₖ wₖ • eₖ ρ eₖ⁻¹ ‖ ∑ₖ wₖ • eₖ σ eₖ⁻¹) ≤ D(ρ ‖ σ)`.

Joint convexity (`quantumRelativeEntropy_jointly_convex_sum`) bounds the left-hand side by
`∑ₖ wₖ · D(eₖ ρ eₖ⁻¹ ‖ eₖ σ eₖ⁻¹)`, and each summand equals `D(ρ ‖ σ)` by unitary invariance
(`quantumRelativeEntropy_conjStarAlgEquiv_of_isStrictlyPositive`); as the weights sum to `1`, the
weighted sum then collapses to `D(ρ ‖ σ)`. Strict positivity of each conjugate `eₖ ρ eₖ⁻¹` —
required by the convexity lemma — is `LinearIsometryEquiv.conjStarAlgEquiv_isStrictlyPositive_iff`.

This is the step that turns joint convexity into a data-processing inequality. The completely
depolarizing partial-trace twirl `partialTrace(·) ⊗ I/d` is a mixed-unitary average over a unitary
`1`-design (N&C Ex 11.19), so the monotonicity of the relative entropy under partial trace — the
bridge to the strong subadditivity of the von Neumann entropy (N&C Thm 11.14) — is an instance of
this lemma. -/
theorem quantumRelativeEntropy_sum_conjStarAlgEquiv_le {κ : Type*} (t : Finset κ)
    (e : κ → (E ≃ₗᵢ[ℂ] E)) {ρ σ : E →L[ℂ] E} {w : κ → ℝ}
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ)
    (hw : ∀ k ∈ t, 0 ≤ w k) (hsum : ∑ k ∈ t, w k = 1) :
    quantumRelativeEntropy (∑ k ∈ t, w k • (e k).conjStarAlgEquiv ρ)
        (∑ k ∈ t, w k • (e k).conjStarAlgEquiv σ) ≤ quantumRelativeEntropy ρ σ := by
  refine (quantumRelativeEntropy_jointly_convex_sum t
    (fun k _ ↦ (e k).conjStarAlgEquiv_isStrictlyPositive_iff.mpr hρ)
    (fun k _ ↦ (e k).conjStarAlgEquiv_isStrictlyPositive_iff.mpr hσ) hw hsum).trans (le_of_eq ?_)
  have hterm : ∀ k ∈ t, w k * quantumRelativeEntropy ((e k).conjStarAlgEquiv ρ)
      ((e k).conjStarAlgEquiv σ) = w k * quantumRelativeEntropy ρ σ := fun k _ ↦ by
    rw [quantumRelativeEntropy_conjStarAlgEquiv_of_isStrictlyPositive (e k) hρ hσ]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hsum, one_mul]

end AbstractConvexity

/-! ### Support condition

The precise precondition under which `D(ρ ‖ σ)` (the `cfc`-based definition) is meaningful is the
**support condition** `supp ρ ⊆ supp σ`. For positive operators `supp = (ker)ᗮ`, so this is the
operator-kernel inclusion `ker σ ≤ ker ρ`: `ρ` carries no weight where `σ` vanishes, exactly the
regime in which `Real.log 0 = 0` on `ker σ` is harmless.
It relaxes the faithful (`IsStrictlyPositive σ`) hypothesis of the DPI engine. -/

section SupportCondition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The support condition is preserved by unitary conjugation `e (·) e⁻¹`. The load-bearer for
transporting `D(ρ ‖ σ)`'s meaningfulness along the Stinespring isometry (B5c). -/
theorem HasSupportLE.conjStarAlgEquiv {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (e : E ≃ₗᵢ[ℂ] F) {ρ σ : E →L[ℂ] E} (h : HasSupportLE ρ σ) :
    HasSupportLE (e.conjStarAlgEquiv ρ) (e.conjStarAlgEquiv σ) := by
  intro x hx
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    LinearIsometryEquiv.conjStarAlgEquiv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    EmbeddingLike.map_eq_zero_iff] at hx ⊢
  exact h hx

/-- The support condition is preserved by conjugation by a (possibly non-surjective) isometry `V`
(`V† V = 1`): `supp ρ ⊆ supp σ ⟹ supp (V ρ V†) ⊆ supp (V σ V†)`. The non-equiv companion to
`HasSupportLE.conjStarAlgEquiv`; transports the meaningfulness of `D` across the Stinespring
isometry (B5c). -/
theorem HasSupportLE.conj_isometry {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {V : E →L[ℂ] F} (hV : V.adjoint ∘L V = 1) {ρ σ : E →L[ℂ] E}
    (h : HasSupportLE ρ σ) :
    HasSupportLE (V ∘L ρ ∘L V.adjoint) (V ∘L σ ∘L V.adjoint) := by
  have hVinj : Function.Injective V := Function.LeftInverse.injective (g := V.adjoint) fun y ↦ by
    rw [← ContinuousLinearMap.comp_apply, hV, one_apply_eq_self]
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply] at hx ⊢
  have hσ0 : V.adjoint x ∈ LinearMap.ker (σ : E →ₗ[ℂ] E) :=
    LinearMap.mem_ker.mpr (hVinj (by rw [map_zero]; exact hx))
  have hρ0 : ρ (V.adjoint x) = 0 := LinearMap.mem_ker.mp (h hσ0)
  rw [hρ0, map_zero]

/-- **The support condition kills the `ker σ`-block.** If `supp ρ ⊆ supp σ` (`HasSupportLE ρ σ`)
and `σ` is self-adjoint, then `ρ` annihilates the spectral projection `cfc 1_{{0}} σ` onto `ker σ`:
the projection's range lies in `ker σ ⊆ ker ρ`. This is the only place the support condition enters
the relative-entropy continuity limit (plan §3.1). -/
theorem HasSupportLE.comp_cfc_indicator_zero [FiniteDimensional ℂ E] {ρ σ : E →L[ℂ] E}
    (h : HasSupportLE ρ σ) (hσ : IsSelfAdjoint σ) :
    ρ * cfc (Set.indicator {0} (1 : ℝ → ℝ)) σ = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hker : cfc (Set.indicator {0} (1 : ℝ → ℝ)) σ x ∈ LinearMap.ker (σ : E →ₗ[ℂ] E) := by
    rw [LinearMap.mem_ker]
    simpa using DFunLike.congr_fun hσ.self_mul_cfc_indicator_zero x
  simpa using h hker

end SupportCondition

/-! ### General operator facts: tensor trace and involution positivity

Two ℂ-finite-dimensional operator lemmas: the trace factorises over `TensorProduct.mapL`, and
`I − cG` is positive for a self-adjoint involution `G` with `c² ≤ 1`. -/

section GeneralOperatorFacts

open scoped ComplexOrder

/-- **Trace of a tensor-product operator factorises:** `tr (A ⊗ B) = (tr A) · (tr B)`.
The `mapL 1 1` case of `trace_mapL_comp_mapL`. -/
theorem trace_mapL {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    LinearMap.trace ℂ (TensorProduct ℂ E F) ↑(TensorProduct.mapL A B) =
      LinearMap.trace ℂ E ↑A * LinearMap.trace ℂ F ↑B := by
  have h := trace_mapL_comp_mapL A 1 B 1
  simpa only [TensorProduct.mapL_one, ContinuousLinearMap.toLinearMap_one,
    Module.End.one_eq_id, LinearMap.comp_id] using h

/-- **`mapL A B` is an involution when `A`, `B` are:** `(A ⊗ B)² = 1` from `A² = 1` and `B² = 1`,
since `mapL` is multiplicative and `mapL 1 1 = 1`. -/
theorem mapL_mul_mapL_self {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : A * A = 1) (hB : B * B = 1) :
    TensorProduct.mapL A B * TensorProduct.mapL A B = 1 := by
  rw [← TensorProduct.mapL_mul, hA, hB, TensorProduct.mapL_one]

/-- **`I − cG` is positive for a self-adjoint involution `G` and `c² ≤ 1`.** Writing the projections
`P = ½(I + G)`, `Q = ½(I − G)` (idempotent because `G² = 1`, self-adjoint because `G` is, hence
positive), one has `I − cG = (1 − c)·P + (1 + c)·Q`, a nonnegative combination of positive operators
(`1 ± c ≥ 0` from `c² ≤ 1`). This is the operator-positivity engine behind the high-temperature NMR
thermal states (`I − cZ ⪰ 0`). -/
theorem isPositive_one_sub_smul_of_selfAdjoint_involution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {G : E →L[ℂ] E} (hsa : IsSelfAdjoint G)
    (hG : G * G = 1) {c : ℝ} (hc : c ^ 2 ≤ 1) : (1 - (c : ℂ) • G).IsPositive := by
  have h1sa : IsSelfAdjoint (1 : E →L[ℂ] E) := by rw [isSelfAdjoint_iff, star_one]
  have hhalf : IsSelfAdjoint ((2 : ℂ)⁻¹) := by rw [isSelfAdjoint_iff]; simp
  have hPsa : IsSelfAdjoint ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) + G)) := by
    rw [isSelfAdjoint_iff, star_smul, hhalf.star_eq, star_add, h1sa.star_eq, hsa.star_eq]
  have hQsa : IsSelfAdjoint ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) - G)) := by
    rw [isSelfAdjoint_iff, star_smul, hhalf.star_eq, star_sub, h1sa.star_eq, hsa.star_eq]
  have hPidem : IsIdempotentElem ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) + G)) := by
    have h2 : ((1 : E →L[ℂ] E) + G) * (1 + G) = (2 : ℂ) • (1 + G) := by
      rw [add_mul, mul_add, mul_add, mul_one, one_mul, mul_one, hG]; module
    unfold IsIdempotentElem
    rw [smul_mul_smul_comm, h2, smul_smul]; norm_num
  have hQidem : IsIdempotentElem ((2 : ℂ)⁻¹ • ((1 : E →L[ℂ] E) - G)) := by
    have h2 : ((1 : E →L[ℂ] E) - G) * (1 - G) = (2 : ℂ) • (1 - G) := by
      rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, mul_one, hG]; module
    unfold IsIdempotentElem
    rw [smul_mul_smul_comm, h2, smul_smul]; norm_num
  have hP := (IsIdempotentElem.isPositive_iff_isSelfAdjoint hPidem).mpr hPsa
  have hQ := (IsIdempotentElem.isPositive_iff_isSelfAdjoint hQidem).mpr hQsa
  have hdecomp : (1 : E →L[ℂ] E) - (c : ℂ) • G
      = ((1 - c : ℝ) : ℂ) • ((2 : ℂ)⁻¹ • (1 + G)) + ((1 + c : ℝ) : ℂ) • ((2 : ℂ)⁻¹ • (1 - G)) := by
    push_cast; module
  rw [hdecomp]
  have h1c : (0 : ℝ) ≤ 1 - c := by nlinarith [hc, sq_nonneg (1 - c), sq_nonneg (1 + c)]
  have h1c' : (0 : ℝ) ≤ 1 + c := by nlinarith [hc, sq_nonneg (1 - c), sq_nonneg (1 + c)]
  exact (hP.smul_of_nonneg (Complex.zero_le_real.mpr h1c)).add
    (hQ.smul_of_nonneg (Complex.zero_le_real.mpr h1c'))

end GeneralOperatorFacts

end ContinuousLinearMap
