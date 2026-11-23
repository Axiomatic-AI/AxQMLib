/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC
public import ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec

/-!
# Matrix transpose of operators on Euclidean space

For an operator `T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι`, define the **transpose**
`EuclideanSpace.transposeOp T` as the operator whose matrix in the canonical basis is the
transpose (NOT the conjugate-transpose / adjoint) of `T`'s matrix. Following the
`EuclideanSpace.conjVec` docstring, this is conjugation of the adjoint (`= star`) by the
componentwise complex conjugation `conjVec`:

`transposeOp T := conjVec ∘ (star T) ∘ conjVec`.

The basis-dependence is localized to `EuclideanSpace`'s canonical coordinate frame (Mathlib's
idiom for basis-dependent linear algebra, cf. `Matrix.toEuclideanCLM`); an abstract
finite-dimensional space is handled by transporting along an `OrthonormalBasis.repr`.

## Main results

- `EuclideanSpace.transposeOp`, `transposeOp_apply`: the definition.
- `transposeOp_transposeOp`: `transposeOp (transposeOp T) = T` (involution).
- `transposeOp_mul`: anti-multiplicativity.
- `transposeOp_spectrum`: preserves the real spectrum.
- `transposeOp_isSelfAdjoint`, `transposeOp_isStrictlyPositive`: preservation.
- `cfc_transposeOp`: commutes with `cfc` on self-adjoint operators.

## Motivation

This packages the structural infrastructure for the **Choi–Jamiołkowski bridge** in Lieb's
Theorem 1 (trace form): `⟨choiVec K, mapL A B (choiVec K)⟩ = Tr(K† A K · transposeOp B)`, where
the transpose (not adjoint) appears because the Choi pairing is the Frobenius/Hadamard trace. The
trace form follows from the v-form by reparametrizing `B → transposeOp B`, which needs the
CFC-commute `(transposeOp B)^r = transposeOp (B^r)` (`cfc_transposeOp`).
-/

@[expose] public section

open scoped InnerProductSpace

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι]

local notation "𝒞" => EuclideanSpace.conjVec

/-- The transpose of an operator on `EuclideanSpace ℂ ι`: conjugation of the adjoint (`star`) by
the componentwise complex conjugation, `conjVec ∘ (star T) ∘ conjVec`. Its matrix in the canonical
basis is the transpose (not conjugate-transpose) of `T`'s. -/
noncomputable def transposeOp (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ 𝒞 (star T (𝒞 x))
      map_add' := fun x y ↦ by simp [map_add]
      map_smul' := fun c x ↦ by simp [conjVec_smul, map_smul] }

@[simp] theorem transposeOp_apply (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (x : EuclideanSpace ℂ ι) :
    transposeOp T x = 𝒞 (star T (𝒞 x)) := rfl

/-- The adjoint (`star`) commutes with the transpose: `star (transposeOp T) = transposeOp (star T)`.
Proved via the `conjVec` anti-isometry: both sides pair to `(⟪𝒞 v, T (𝒞 z)⟫)⋆`. -/
theorem star_transposeOp (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    star (transposeOp T) = transposeOp (star T) := by
  refine ContinuousLinearMap.ext fun z ↦ ext_inner_left ℂ fun v ↦ ?_
  have hL : ⟪𝒞 (star T (𝒞 v)), z⟫_ℂ = star ⟪𝒞 v, T (𝒞 z)⟫_ℂ := by
    conv_lhs => rw [← conjVec_conjVec z]
    rw [inner_conjVec, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have hR : ⟪v, 𝒞 (T (𝒞 z))⟫_ℂ = star ⟪𝒞 v, T (𝒞 z)⟫_ℂ := by
    conv_lhs => rw [← conjVec_conjVec v]
    rw [inner_conjVec]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    transposeOp_apply, transposeOp_apply, star_star, hL, hR]

/-- Involution: `transposeOp (transposeOp T) = T`. -/
theorem transposeOp_transposeOp (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    transposeOp (transposeOp T) = T := by
  ext x
  rw [transposeOp_apply, star_transposeOp, transposeOp_apply, conjVec_conjVec, star_star,
    conjVec_conjVec]

@[simp] theorem transposeOp_add (T S : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    transposeOp (T + S) = transposeOp T + transposeOp S := by
  ext x; simp [star_add]

@[simp] theorem transposeOp_smul (c : ℂ) (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    transposeOp (c • T) = c • transposeOp T := by
  ext x; simp [star_smul, conjVec_smul]

@[simp] theorem transposeOp_zero :
    transposeOp (0 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) = 0 := by
  ext x; simp

@[simp] theorem transposeOp_one :
    transposeOp (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) = 1 := by
  ext x; simp [conjVec_conjVec]

/-- The transpose is **anti-multiplicative**:
`transposeOp (X * Y) = transposeOp Y * transposeOp X`. -/
theorem transposeOp_mul (X Y : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    transposeOp (X * Y) = transposeOp Y * transposeOp X := by
  ext x
  simp only [transposeOp_apply, star_mul, mul_apply_eq_comp, conjVec_conjVec]

/-- The transpose preserves invertibility: the inverse of `transposeOp B` is `transposeOp B⁻¹`. -/
theorem transposeOp_isUnit {B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} (hB : IsUnit B) :
    IsUnit (transposeOp B) := by
  obtain ⟨u, rfl⟩ := hB
  exact ⟨⟨transposeOp ↑u, transposeOp ↑u⁻¹,
    by rw [← transposeOp_mul, u.inv_mul, transposeOp_one],
    by rw [← transposeOp_mul, u.mul_inv, transposeOp_one]⟩, rfl⟩

/-- Invertibility transfers in both directions across the transpose (via the involution). -/
theorem transposeOp_isUnit_iff (B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    IsUnit (transposeOp B) ↔ IsUnit B :=
  ⟨fun h ↦ transposeOp_transposeOp B ▸ transposeOp_isUnit h, transposeOp_isUnit⟩

@[simp] theorem transposeOp_sub (X Y : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    transposeOp (X - Y) = transposeOp X - transposeOp Y := by
  ext x; simp [star_sub]

@[simp] theorem transposeOp_algebraMap (r : ℝ) :
    transposeOp (algebraMap ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) r) =
      algebraMap ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) r := by
  rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, transposeOp_smul, transposeOp_one,
    Complex.coe_smul]

/-- **The transpose preserves the real spectrum.** Used to transport the `ContinuousOn`-on-spectrum
hypothesis of the CFC in `cfc_transposeOp`. -/
theorem transposeOp_spectrum (B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    spectrum ℝ (transposeOp B) = spectrum ℝ B := by
  ext r
  simp only [spectrum.mem_iff]
  rw [show algebraMap ℝ _ r - transposeOp B = transposeOp (algebraMap ℝ _ r - B) by
        rw [transposeOp_sub, transposeOp_algebraMap], transposeOp_isUnit_iff]

/-- **Eigenvector correspondence**: for self-adjoint `Y`,
`transposeOp Y (conjVec v) = conjVec (Y v)`. -/
theorem transposeOp_apply_conjVec {Y : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hY : IsSelfAdjoint Y) (v : EuclideanSpace ℂ ι) :
    transposeOp Y (𝒞 v) = 𝒞 (Y v) := by
  rw [transposeOp_apply, conjVec_conjVec, hY.star_eq]

/-- `conjVec` of an eigenvector of self-adjoint `Y` (real eigenvalue `μ`) is an eigenvector of
`transposeOp Y` with the same eigenvalue. -/
theorem transposeOp_conjVec_eq_smul {Y : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hY : IsSelfAdjoint Y) {v : EuclideanSpace ℂ ι} {μ : ℝ} (hv : Y v = (μ : ℂ) • v) :
    transposeOp Y (𝒞 v) = (μ : ℂ) • 𝒞 v := by
  rw [transposeOp_apply_conjVec hY, hv, conjVec_smul, Complex.star_def, Complex.conj_ofReal]

/-- The transpose preserves self-adjointness (`star_transposeOp`). -/
theorem transposeOp_isSelfAdjoint {Y : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hY : IsSelfAdjoint Y) : IsSelfAdjoint (transposeOp Y) := by
  change star (transposeOp Y) = transposeOp Y
  rw [star_transposeOp, hY.star_eq]

/-- The transpose preserves nonnegativity (Loewner order): conjugation by the antiunitary
`conjVec` preserves positivity, `⟪x, transposeOp B x⟫ = (⟪conjVec x, B (conjVec x)⟫)⋆ ≥ 0`. -/
theorem transposeOp_nonneg {B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} (hB : 0 ≤ B) :
    0 ≤ transposeOp B := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hB ⊢
  have hBsa : IsSelfAdjoint B := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hB.1
  refine ⟨(transposeOp_isSelfAdjoint hBsa).isSymmetric, fun x ↦ ?_⟩
  have key : (transposeOp B).reApplyInnerSelf x = B.reApplyInnerSelf (𝒞 x) := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.reApplyInnerSelf_apply,
      transposeOp_apply, hBsa.star_eq, conjVec_inner, RCLike.star_def, RCLike.conj_re]
  rw [key]
  exact hB.2 (𝒞 x)

/-- The transpose preserves strict positivity. -/
theorem transposeOp_isStrictlyPositive {B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB : IsStrictlyPositive B) : IsStrictlyPositive (transposeOp B) :=
  ⟨transposeOp_nonneg hB.nonneg, transposeOp_isUnit hB.isUnit⟩

/-- **CFC commutes with the transpose** on self-adjoint operators:
`cfc f (transposeOp Y) = transposeOp (cfc f Y)`. Specialized to `f = (· ^ r)` this is the
`(transposeOp B)^r = transposeOp (B^r)` reparametrization for the trace-form Lieb T1.

Proof: conjugated eigenvectors `conjVec eₖ` of `Y` are eigenvectors of `transposeOp Y` with the
same real eigenvalue (`transposeOp_conjVec_eq_smul`); spectral mapping makes both sides act as
`f λₖ` on them, and they span (the conjugate of an eigenbasis). -/
theorem cfc_transposeOp {Y : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} (hY : IsSelfAdjoint Y)
    {f : ℝ → ℝ} (hf : ContinuousOn f (spectrum ℝ Y)) :
    cfc f (transposeOp Y) = transposeOp (cfc f Y) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ (EuclideanSpace ℂ ι) = n := ⟨_, rfl⟩
  have hYT := transposeOp_isSelfAdjoint hY
  have hcfcY : IsSelfAdjoint (cfc f Y) := cfc_predicate f Y
  have hfT : ContinuousOn f (spectrum ℝ (transposeOp Y)) := by
    rw [transposeOp_spectrum]; exact hf
  set e := hY.isSymmetric.eigenvectorBasis hn
  set lam := hY.isSymmetric.eigenvalues hn
  have hkey : ∀ k, cfc f (transposeOp Y) (𝒞 (e k)) = transposeOp (cfc f Y) (𝒞 (e k)) := fun k ↦ by
    have heig : Y (e k) = (lam k : ℂ) • e k := hY.apply_eigenvectorBasis_cast hn k
    rw [hYT.cfc_apply_smul_of_apply_eq_smul hn hfT (transposeOp_conjVec_eq_smul hY heig),
      transposeOp_apply_conjVec hcfcY, hY.cfc_apply_smul_of_apply_eq_smul hn hf heig,
      conjVec_smul, Complex.star_def, Complex.conj_ofReal]
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [← conjVec_conjVec x, ← e.sum_repr' (𝒞 x), conjVec_sum]
  simp only [conjVec_smul, map_sum, ContinuousLinearMap.map_smul]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [hkey k]

end EuclideanSpace
