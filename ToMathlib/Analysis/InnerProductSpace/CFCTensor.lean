/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC
public import ToMathlib.Analysis.InnerProductSpace.TensorPower
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.GeometricMean

/-!
# CFC functions distribute over the tensor product (log, sqrt, conjSqrt, geometric mean)

This file collects identities expressing how Continuous Functional Calculus operations on
operators distribute over `TensorProduct.mapL` on a finite-dim complex Hilbert space:

* `log(A ⊗ B) = log A ⊗ I + I ⊗ log B` for strictly positive `A, B` (`cfc_log_tensorMap`).
  The log identity requires spectral decomposition.
* `(A ⊗ B)^y = A^y ⊗ B^y` for strictly positive `A, B` (`cfc_rpow_const_tensorMap`).
  Also spectral; uses `Real.mul_rpow` as the eigenvalue-level identity.
* `sqrt(A ⊗ B) = sqrt A ⊗ sqrt B` for `0 ≤ A, B` (`sqrt_mapL`).
* `conjSqrt(A ⊗ B, C ⊗ D) = conjSqrt A C ⊗ conjSqrt B D` for `0 ≤ A, B` (`conjSqrt_mapL`).
* `M₀(A₁ ⊗ A₂, B₁ ⊗ B₂) = M₀(A₁, B₁) ⊗ M₀(A₂, B₂)` for strictly positive `A_i`, nonneg
  `B_i` (`geometricMean_mapL`).

Plus the supporting algebraic facts: `mapL` preserves nonnegativity (`mapL_nonneg`),
positivity (`mapL_isPositive`), strict positivity (`mapL_isStrictlyPositive`),
invertibility (`isUnit_mapL`), and ring-inverse (`ringInverse_mapL`).

## Main results

- `IsSelfAdjoint.tensorMapL`: CLM-level analog of `IsSelfAdjoint.tensorMap` (LM-level).
- `IsSelfAdjoint.cfc_log_tensorMap`: the log additivity identity.
- `IsSelfAdjoint.cfc_rpow_const_tensorMap`: the rpow multiplicativity identity.
- `TensorProduct.geometricMean_mapL`: tensor distributivity of the operator geometric mean.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

/-! ### CLM-level self-adjointness of `TensorProduct.mapL` -/

/-- **CLM-level analog of `IsSelfAdjoint.tensorMap`** (LM-level): the tensor product of
self-adjoint continuous linear maps is self-adjoint. Restricted to `ℂ`-scalar because the CLM
`Star` instance `Star (E →L[𝕜] E)` only synthesizes for `𝕜 = ℂ` in current Mathlib.

`(TensorProduct.mapL A B).toLinearMap` is no longer definitionally `TensorProduct.map ↑A ↑B`
(only propositionally, via the `@[simp]`-but-not-`rfl` `TensorProduct.toLinearMap_mapL`), so
naively applying `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr` to a proof about
`TensorProduct.map ↑A ↑B` makes the elaborator try (and time out) unifying the two forms;
`rw`-ing the goal through `toLinearMap_mapL` first avoids that unification entirely. -/
theorem IsSelfAdjoint.tensorMapL {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (TensorProduct.mapL A B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, TensorProduct.toLinearMap_mapL]
  exact LinearMap.IsSymmetric.tensorMap hA.isSymmetric hB.isSymmetric

/-! ### Transport of eigen-data along an operator equality -/

/-- **Eigenvalues are transported along an equality of operators**: if `T = S` then the
eigenvalue functions attached to symmetry proofs for `T` and `S` agree. Needed because
`(TensorProduct.mapL A B).toLinearMap` is only propositionally (not definitionally) equal to
`TensorProduct.map ↑A ↑B`, so eigen-data of the two forms is not interchangeable by `rfl`. -/
theorem LinearMap.IsSymmetric.eigenvalues_congr {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) (h : T = S)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    hT.eigenvalues hn = hS.eigenvalues hn := by
  subst h; rfl

/-! ### Abstract `cfc_log_tensorMap` -/

namespace IsSelfAdjoint

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- **Operator log on a tensor product factors additively** (abstract): for positive
self-adjoint operators `A, B` (with strictly positive eigenvalues) on finite-dim complex
Hilbert spaces, `log(A ⊗ B) = log A ⊗ I + I ⊗ log B`. The identity follows from spectral
decomposition: on the joint eigenbasis `eA i ⊗ₜ eB j`, the LHS has eigenvalues `log(λᵢμⱼ)`
and the RHS has `log λᵢ + log μⱼ`, which agree by `Real.log_mul`. -/
theorem cfc_log_tensorMap
    {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {dE dF : ℕ}
    (hdE : Module.finrank ℂ E = dE) (hdF : Module.finrank ℂ F = dF)
    (hA_pos : ∀ i, 0 < hA.isSymmetric.eigenvalues hdE i)
    (hB_pos : ∀ j, 0 < hB.isSymmetric.eigenvalues hdF j) :
    cfc Real.log (TensorProduct.mapL A B) =
      TensorProduct.mapL (cfc Real.log A) (1 : F →L[ℂ] F) +
        TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log B) := by
  have hev : (hA.tensorMapL hB).isSymmetric.eigenvalues
        (rfl : Module.finrank ℂ (E ⊗[ℂ] F) = Module.finrank ℂ (E ⊗[ℂ] F)) =
      (LinearMap.IsSymmetric.tensorMap hA.isSymmetric hB.isSymmetric).eigenvalues rfl :=
    LinearMap.IsSymmetric.eigenvalues_congr _ _ (TensorProduct.toLinearMap_mapL A B) _
  refine ContinuousLinearMap.coe_injective
    ((OrthonormalBasis.tensorProduct (hA.isSymmetric.eigenvectorBasis hdE)
      (hB.isSymmetric.eigenvectorBasis hdF)).toBasis.ext fun ⟨i, j⟩ ↦ ?_)
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    ContinuousLinearMap.coe_coe]
  have hmu : (TensorProduct.mapL A B)
        (hA.isSymmetric.eigenvectorBasis hdE i ⊗ₜ[ℂ] hB.isSymmetric.eigenvectorBasis hdF j) =
      ((hA.isSymmetric.eigenvalues hdE i * hB.isSymmetric.eigenvalues hdF j : ℝ) : ℂ) •
        (hA.isSymmetric.eigenvectorBasis hdE i ⊗ₜ[ℂ] hB.isSymmetric.eigenvectorBasis hdF j) := by
    rw [← ContinuousLinearMap.coe_coe, TensorProduct.toLinearMap_mapL]
    exact LinearMap.IsSymmetric.tensorMap_apply_eigenvectorBasis_smul
      hA.isSymmetric hB.isSymmetric hdE hdF i j
  rw [(hA.tensorMapL hB).cfc_log_apply_smul_of_apply_eq_smul (n := Module.finrank ℂ (E ⊗[ℂ] F)) rfl
      (fun k ↦ hev ▸ LinearMap.IsSymmetric.tensorMap_eigenvalues_pos
        hA.isSymmetric hB.isSymmetric hdE hdF rfl hA_pos hB_pos k) hmu,
    add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    one_apply_eq_self, one_apply_eq_self,
    hA.cfc_log_apply_eigenvectorBasis hdE hA_pos i,
    hB.cfc_log_apply_eigenvectorBasis hdF hB_pos j,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul]
  congr 1
  exact_mod_cast Real.log_mul (hA_pos i).ne' (hB_pos j).ne'

/-- **Operator real-power on a tensor product factors multiplicatively** (abstract): for
positive self-adjoint operators `A, B` (with strictly positive eigenvalues) on finite-dim
complex Hilbert spaces and any exponent `y : ℝ`, `(A ⊗ B)^y = A^y ⊗ B^y`. The identity follows
from spectral decomposition: on the joint eigenbasis `eA i ⊗ₜ eB j`, the LHS has eigenvalues
`(λᵢμⱼ)^y` and the RHS has `λᵢ^y · μⱼ^y`, which agree by `Real.mul_rpow`.

For the `^`-notation (`CFC.rpow`) form, bridge via `CFC.rpow_eq_cfc_real` (which rewrites
`a ^ y` to `cfc (fun x : ℝ ↦ x ^ y) a` for `0 ≤ a`). -/
theorem cfc_rpow_const_tensorMap
    {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {dE dF : ℕ}
    (hdE : Module.finrank ℂ E = dE) (hdF : Module.finrank ℂ F = dF)
    (hA_pos : ∀ i, 0 < hA.isSymmetric.eigenvalues hdE i)
    (hB_pos : ∀ j, 0 < hB.isSymmetric.eigenvalues hdF j) (y : ℝ) :
    cfc (fun x : ℝ ↦ x ^ y) (TensorProduct.mapL A B) =
      TensorProduct.mapL (cfc (fun x : ℝ ↦ x ^ y) A) (cfc (fun x : ℝ ↦ x ^ y) B) := by
  have hev : (hA.tensorMapL hB).isSymmetric.eigenvalues
        (rfl : Module.finrank ℂ (E ⊗[ℂ] F) = Module.finrank ℂ (E ⊗[ℂ] F)) =
      (LinearMap.IsSymmetric.tensorMap hA.isSymmetric hB.isSymmetric).eigenvalues rfl :=
    LinearMap.IsSymmetric.eigenvalues_congr _ _ (TensorProduct.toLinearMap_mapL A B) _
  refine ContinuousLinearMap.coe_injective
    ((OrthonormalBasis.tensorProduct (hA.isSymmetric.eigenvectorBasis hdE)
      (hB.isSymmetric.eigenvectorBasis hdF)).toBasis.ext fun ⟨i, j⟩ ↦ ?_)
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    ContinuousLinearMap.coe_coe]
  have hmu : (TensorProduct.mapL A B)
        (hA.isSymmetric.eigenvectorBasis hdE i ⊗ₜ[ℂ] hB.isSymmetric.eigenvectorBasis hdF j) =
      ((hA.isSymmetric.eigenvalues hdE i * hB.isSymmetric.eigenvalues hdF j : ℝ) : ℂ) •
        (hA.isSymmetric.eigenvectorBasis hdE i ⊗ₜ[ℂ] hB.isSymmetric.eigenvectorBasis hdF j) := by
    rw [← ContinuousLinearMap.coe_coe, TensorProduct.toLinearMap_mapL]
    exact LinearMap.IsSymmetric.tensorMap_apply_eigenvectorBasis_smul
      hA.isSymmetric hB.isSymmetric hdE hdF i j
  rw [(hA.tensorMapL hB).cfc_rpow_const_apply_smul_of_apply_eq_smul
      (n := Module.finrank ℂ (E ⊗[ℂ] F)) rfl
      (fun k ↦ hev ▸ LinearMap.IsSymmetric.tensorMap_eigenvalues_pos
        hA.isSymmetric hB.isSymmetric hdE hdF rfl hA_pos hB_pos k) y hmu,
    TensorProduct.mapL_tmul,
    hA.cfc_rpow_const_apply_eigenvectorBasis hdE hA_pos y i,
    hB.cfc_rpow_const_apply_eigenvectorBasis hdF hB_pos y j,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 1
  exact_mod_cast Real.mul_rpow (hA_pos i).le (hB_pos j).le

end IsSelfAdjoint

/-! ### `TensorProduct.mapL`-nonneg + CFC-tensor distributivity (sqrt, ringInverse, conjSqrt, M₀) -/

namespace TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The tensor product preserves invertibility: `IsUnit (mapL A B)` for invertible `A, B`,
with explicit inverse `mapL (Ring.inverse A) (Ring.inverse B)`. -/
theorem isUnit_mapL {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (mapL A B) :=
  ⟨⟨mapL A B, mapL (Ring.inverse A) (Ring.inverse B),
    by simp [← mapL_mul, Ring.mul_inverse_cancel _ hA, Ring.mul_inverse_cancel _ hB],
    by simp [← mapL_mul, Ring.inverse_mul_cancel _ hA, Ring.inverse_mul_cancel _ hB]⟩, rfl⟩

/-- The tensor product distributes over `Ring.inverse`: for invertible `A, B`,
`Ring.inverse (mapL A B) = mapL (Ring.inverse A) (Ring.inverse B)`. -/
theorem ringInverse_mapL {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsUnit A) (hB : IsUnit B) :
    Ring.inverse (mapL A B) = mapL (Ring.inverse A) (Ring.inverse B) := by
  refine (isUnit_mapL hA hB).mul_right_cancel ?_
  simp [Ring.inverse_mul_cancel _ (isUnit_mapL hA hB), ← mapL_mul,
    Ring.inverse_mul_cancel _ hA, Ring.inverse_mul_cancel _ hB]

variable [CompleteSpace E] [CompleteSpace F]

/-- The tensor product of nonneg operators is nonneg. Proof: `mapL A B = (mapL √A √B) *
(mapL √A √B)`, and the latter is `IsSelfAdjoint.mul_self_nonneg`. -/
theorem mapL_nonneg {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ mapL A B := by
  rw [← CFC.sqrt_mul_sqrt_self A hA, ← CFC.sqrt_mul_sqrt_self B hB, mapL_mul]
  exact ((CFC.sqrt_nonneg A).isSelfAdjoint.tensorMapL
    (CFC.sqrt_nonneg B).isSelfAdjoint).mul_self_nonneg

/-- **N&C Exercise 2.31**: the tensor product of two *positive operators* is positive.
`mapL A B` is a positive operator (`ContinuousLinearMap.IsPositive`, i.e. symmetric with
`0 ≤ re ⟪·, ·⟫` — N&C's defining property of a positive operator) whenever both `A` and `B` are.
The `IsPositive`-phrased companion of `mapL_nonneg`, bridged by `nonneg_iff_isPositive`. -/
theorem mapL_isPositive {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    (mapL A B).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp
    (mapL_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hB))

/-- The tensor product preserves strict positivity: `mapL A B` is strictly positive whenever
both `A` and `B` are. Combination of `mapL_nonneg` and `isUnit_mapL`. -/
@[aesop safe apply]
theorem mapL_isStrictlyPositive {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (mapL A B) :=
  ⟨mapL_nonneg hA.nonneg hB.nonneg, isUnit_mapL hA.isUnit hB.isUnit⟩

/-- The tensor product distributes over `CFC.sqrt`: `sqrt (mapL A B) = mapL (sqrt A) (sqrt B)`
for nonneg `A, B`. Via `sqrt_unique`: `(mapL √A √B)² = mapL A B` (by `mapL_mul` and
`sqrt_mul_sqrt_self`), and `0 ≤ mapL √A √B` (by `mapL_nonneg`). -/
theorem sqrt_mapL {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.sqrt (mapL A B) = mapL (CFC.sqrt A) (CFC.sqrt B) := by
  refine CFC.sqrt_unique ?_ (mapL_nonneg (CFC.sqrt_nonneg A) (CFC.sqrt_nonneg B))
  rw [← mapL_mul, CFC.sqrt_mul_sqrt_self A hA, CFC.sqrt_mul_sqrt_self B hB]

/-- The tensor product distributes over `CFC.conjSqrt`: `conjSqrt (mapL A B) (mapL C D)
= mapL (conjSqrt A C) (conjSqrt B D)` for nonneg `A, B`. -/
theorem conjSqrt_mapL {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (C : E →L[ℂ] E) (D : F →L[ℂ] F) :
    CFC.conjSqrt (mapL A B) (mapL C D) = mapL (CFC.conjSqrt A C) (CFC.conjSqrt B D) := by
  rw [CFC.conjSqrt_apply, CFC.conjSqrt_apply, CFC.conjSqrt_apply, sqrt_mapL hA hB,
    ← mapL_mul, ← mapL_mul]

/-- **Tensor distributivity of the operator geometric mean**: for strictly positive `A₁ : E →L E`
and `A₂ : F →L F`, and nonneg `B₁, B₂`, `M₀(A₁ ⊗ A₂, B₁ ⊗ B₂) = M₀(A₁, B₁) ⊗ M₀(A₂, B₂)`.
Consumed by the midpoint identity `mapL_rpow_midpoint_eq_geometricMean`. -/
theorem geometricMean_mapL {A₁ : E →L[ℂ] E} {A₂ : F →L[ℂ] F} {B₁ : E →L[ℂ] E} {B₂ : F →L[ℂ] F}
    (hA₁ : IsStrictlyPositive A₁) (hA₂ : IsStrictlyPositive A₂) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    CFC.geometricMean (mapL A₁ A₂) (mapL B₁ B₂) =
      mapL (CFC.geometricMean A₁ B₁) (CFC.geometricMean A₂ B₂) := by
  simp only [CFC.geometricMean_def, ringInverse_mapL hA₁.isUnit hA₂.isUnit,
    conjSqrt_mapL hA₁.ringInverse.nonneg hA₂.ringInverse.nonneg,
    sqrt_mapL (CFC.conjSqrt_nonneg _ hB₁) (CFC.conjSqrt_nonneg _ hB₂),
    conjSqrt_mapL hA₁.nonneg hA₂.nonneg]

/-- **Midpoint identity for `mapL`-of-rpow**: for strictly positive `X, Y` and any real
exponents `q₁, q₂, r₁, r₂`,

  `mapL (X ^ ((q₁+q₂)/2)) (Y ^ ((r₁+r₂)/2)) = M₀(mapL (X^q₁) (Y^r₁), mapL (X^q₂) (Y^r₂))`.

Direct combination of `geometricMean_rpow_rpow` (same-base GM) and `geometricMean_mapL`
(β.5 tensor distributivity). Key step in Carlen §6.1's midpoint-closure of the Lieb T1 joint
concavity property. -/
theorem mapL_rpow_midpoint_eq_geometricMean
    {X : E →L[ℂ] E} (hX : IsStrictlyPositive X)
    {Y : F →L[ℂ] F} (hY : IsStrictlyPositive Y) (q₁ q₂ r₁ r₂ : ℝ) :
    mapL (X ^ ((q₁ + q₂) / 2)) (Y ^ ((r₁ + r₂) / 2)) =
      CFC.geometricMean (mapL (X ^ q₁) (Y ^ r₁)) (mapL (X ^ q₂) (Y ^ r₂)) := by
  rw [← CFC.geometricMean_rpow_rpow hX q₁ q₂, ← CFC.geometricMean_rpow_rpow hY r₁ r₂]
  exact (geometricMean_mapL (hX.rpow X q₁) (hY.rpow Y r₁)
    (hX.rpow X q₂).nonneg (hY.rpow Y r₂).nonneg).symm

end TensorProduct
