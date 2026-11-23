/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Positive/negative-part decomposition of a self-adjoint operator

Every self-adjoint operator `A` on a complex Hilbert space is the difference `A = Q - R` of
two positive operators `Q, R` whose supports (ranges) are orthogonal subspaces. This is the
operator form of the Jordan–Hahn decomposition, and the ingredient Nielsen & Chuang use in
Exercise 9.7 (p. 405) to write a difference of density operators `ρ - σ = Q - R` with `Q, R`
positive on orthogonal supports.

The witnesses are the continuous-functional-calculus **positive and negative parts** `A⁺` and
`A⁻` (`CFC.posPart` / `CFC.negPart`), for which Mathlib already proves `A⁺ - A⁻ = A`
(`CFC.posPart_sub_negPart`, needing self-adjointness) and `A⁺ * A⁻ = 0`
(`CFC.posPart_mul_negPart`). The genuinely new content here is the bridge from the C⋆-order
`0 ≤ A⁺` (which the CFC delivers) to the operator-theoretic `A⁺.IsPositive`
(`ContinuousLinearMap.nonneg_iff_isPositive`), and the passage from the product identity
`Q * R = 0` to the orthogonality of the ranges of two self-adjoint operators.

The orthogonal-supports fact `isOrtho_range_of_isSelfAdjoint_of_mul_eq_zero` is elementary
adjoint algebra and holds over any `RCLike` field. The positivity of the parts and the
decomposition itself are stated over `ℂ`, because the continuous functional calculus
`ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint` — and hence `CFC.posPart` on
operators — is currently available in Mathlib only for `𝕜 = ℂ`.

## Main results

* `ContinuousLinearMap.isOrtho_range_of_isSelfAdjoint_of_mul_eq_zero` — if `Q` is self-adjoint
  and `Q * R = 0` then `range Q ⟂ range R`; the general fact (over any `RCLike` field) that a
  vanishing product forces orthogonal ranges (the operator form of "orthogonal supports").
* `ContinuousLinearMap.isPositive_posPart` / `ContinuousLinearMap.isPositive_negPart` — the
  positive and negative parts `A⁺`, `A⁻` of an operator are positive operators.
* `ContinuousLinearMap.exists_isPositive_sub_of_isSelfAdjoint` — the decomposition itself: a
  self-adjoint `A` is `Q - R` with `Q, R` positive, `Q * R = 0`, and `range Q ⟂ range R`.
-/

open scoped InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **A vanishing product forces orthogonal ranges.** If `Q` is self-adjoint and `Q * R = 0`,
then the range of `Q` is orthogonal to the range of `R`. Indeed for `a b`,
`⟪Q a, R b⟫ = ⟪a, Q (R b)⟫ = ⟪a, (Q * R) b⟫ = 0` using self-adjointness of `Q`. For two positive
operators this is the operator expression of having supports on orthogonal subspaces. Pure
adjoint algebra, so it holds over any `RCLike` field. -/
theorem isOrtho_range_of_isSelfAdjoint_of_mul_eq_zero {Q R : E →L[𝕜] E}
    (hQ : IsSelfAdjoint Q) (h : Q * R = 0) :
    LinearMap.range (Q : E →ₗ[𝕜] E) ⟂ LinearMap.range (R : E →ₗ[𝕜] E) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  have hcomp : inner 𝕜 ((Q : E →ₗ[𝕜] E) a) ((R : E →ₗ[𝕜] E) b) = inner 𝕜 a ((Q * R) b) := by
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hQ]
    rfl
  rw [hcomp, h]
  simp

end RCLike

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The **positive part** `A⁺` of an operator is a positive operator. The continuous functional
calculus makes `A⁺` nonnegative in the C⋆-order (`CFC.posPart_nonneg`), which for operators is
exactly `IsPositive` (`ContinuousLinearMap.nonneg_iff_isPositive`). -/
theorem isPositive_posPart (A : E →L[ℂ] E) : (A⁺).IsPositive :=
  nonneg_iff_isPositive.mp (CFC.posPart_nonneg A)

/-- The **negative part** `A⁻` of an operator is a positive operator (the negative part is a
*positive* operator whose subtraction recovers `A`). Dual to `isPositive_posPart`. -/
theorem isPositive_negPart (A : E →L[ℂ] E) : (A⁻).IsPositive :=
  nonneg_iff_isPositive.mp (CFC.negPart_nonneg A)

/-- **Positive/negative-part decomposition of a self-adjoint operator** (the operator form of
the Jordan–Hahn decomposition; Nielsen & Chuang Exercise 9.7). A self-adjoint operator `A` on a
complex Hilbert space can be written `A = Q - R` with `Q` and `R` positive operators whose
supports are orthogonal: `Q * R = 0` and `range Q ⟂ range R`. The witnesses are the positive and
negative parts `A⁺`, `A⁻`. -/
theorem exists_isPositive_sub_of_isSelfAdjoint (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ Q R : E →L[ℂ] E, Q.IsPositive ∧ R.IsPositive ∧ A = Q - R ∧ Q * R = 0 ∧
      LinearMap.range (Q : E →ₗ[ℂ] E) ⟂ LinearMap.range (R : E →ₗ[ℂ] E) :=
  ⟨A⁺, A⁻, isPositive_posPart A, isPositive_negPart A,
    (CFC.posPart_sub_negPart A hA).symm, CFC.posPart_mul_negPart A,
    isOrtho_range_of_isSelfAdjoint_of_mul_eq_zero (isPositive_posPart A).isSelfAdjoint
      (CFC.posPart_mul_negPart A)⟩

end Complex

end ContinuousLinearMap
