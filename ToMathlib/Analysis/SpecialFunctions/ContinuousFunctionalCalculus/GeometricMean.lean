/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Operator geometric mean

This file defines the operator geometric mean of two positive elements in a C⋆-algebra,
$M_0(a, b) := a^{1/2} (a^{-1/2} b a^{-1/2})^{1/2} a^{1/2}$, via the continuous functional
calculus. For commuting strictly positive `a, b` this reduces to `sqrt (a * b)`.

The definition is the Pusz–Woronowicz form (Carlen Definition 3.7): it is the largest `X ≥ 0`
such that the `2 × 2` block operator `[[a, X], [X, b]]` is positive semidefinite. The
maximality characterization and joint concavity (`GeometricMeanMaximality`) and
tensor-distributivity (`CFCTensor`) are developed separately.

## Main declarations

* `CFC.geometricMean a b` — the operator geometric mean of `a` and `b`.

## Main results

* `CFC.geometricMean_self` — `M₀(a, a) = a` for strictly positive `a`.
* `CFC.geometricMean_one_left` / `_one_right` — boundary cases with one argument equal to `1`.
* `CFC.geometricMean_nonneg` — the geometric mean is nonnegative.
* `CFC.geometricMean_mul_ringInverse_mul_geometricMean` — `M₀(a, b) · a⁻¹ · M₀(a, b) = b`.
-/

namespace CFC

open Ring

public section GeometricMean

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul A]

/-- The operator geometric mean of two elements `a, b` of a C⋆-algebra:
`M₀(a, b) := a^{1/2} (a^{-1/2} b a^{-1/2})^{1/2} a^{1/2}`.

For strictly positive commuting `a, b` this reduces to `sqrt (a * b)`. When `a` is not
nonnegative (or `a` is nonnegative but not strictly positive), the definition returns `0`. -/
@[expose]
noncomputable def geometricMean (a b : A) : A :=
  conjSqrt a (sqrt (conjSqrt a⁻¹ʳ b))

lemma geometricMean_def (a b : A) :
    geometricMean a b = conjSqrt a (sqrt (conjSqrt a⁻¹ʳ b)) := rfl

/-- Factored form: `M₀(a, b) = √a · √(√a⁻¹ · b · √a⁻¹) · √a`. The block-PSD factorization
in the maximality argument routes through this form. -/
lemma geometricMean_eq_mul (a b : A) :
    geometricMean a b = sqrt a * sqrt (conjSqrt a⁻¹ʳ b) * sqrt a := rfl

lemma geometricMean_of_not_nonneg_left {a b : A} (ha : ¬0 ≤ a) :
    geometricMean a b = 0 := by
  simp [geometricMean, conjSqrt_of_not_nonneg ha]

lemma geometricMean_nonneg (a b : A) : 0 ≤ geometricMean a b :=
  (map_zero (conjSqrt a)) ▸ conjSqrt_monotone (sqrt_nonneg _)

@[simp]
lemma geometricMean_zero_right (a : A) : geometricMean a 0 = 0 := by
  simp [geometricMean]

@[simp]
lemma geometricMean_zero_left (b : A) : geometricMean (0 : A) b = 0 := by
  simp [geometricMean, conjSqrt_apply]

end SeparatelyContinuousMul

variable [IsSemitopologicalRing A] [T2Space A]

@[simp]
lemma geometricMean_self {a : A} (ha : IsStrictlyPositive a) : geometricMean a a = a := by
  rw [geometricMean, conjSqrt_ringInverse_self a, sqrt_one, conjSqrt_one a ha.nonneg]

@[simp]
lemma geometricMean_one_left (b : A) : geometricMean (1 : A) b = sqrt b := by
  simp [geometricMean, conjSqrt_apply]

lemma geometricMean_one_right {a : A} (ha : IsStrictlyPositive a) :
    geometricMean a 1 = sqrt a := by
  rw [geometricMean, conjSqrt_one a⁻¹ʳ ha.ringInverse.nonneg, sqrt_ringInverse,
    conjSqrt_apply, Ring.mul_inverse_cancel _ ha.sqrt.isUnit, one_mul]

/-- Key algebraic identity: `M₀(a, b) · a⁻¹ · M₀(a, b) = b` for strictly positive `a` and
nonnegative `b`. This is the "round-trip" property of `conjSqrt` lifted to the geometric mean,
and underlies the block factorization `[[a, M₀], [M₀, b]] = T*T` in the maximality argument. -/
lemma geometricMean_mul_ringInverse_mul_geometricMean
    {a b : A} (ha : IsStrictlyPositive a) (hb : 0 ≤ b) :
    geometricMean a b * Ring.inverse a * geometricMean a b = b := by
  have hZ : 0 ≤ conjSqrt a⁻¹ʳ b := map_zero (conjSqrt a⁻¹ʳ) ▸ conjSqrt_monotone hb
  have hsa : sqrt a * Ring.inverse a * sqrt a = 1 := by
    have h := conjSqrt_ringInverse_self (Ring.inverse a) ha.ringInverse
    rwa [Ring.inverse_inverse ha.isUnit] at h
  calc geometricMean a b * Ring.inverse a * geometricMean a b
      = sqrt a * sqrt (conjSqrt a⁻¹ʳ b) * (sqrt a * Ring.inverse a * sqrt a) *
          sqrt (conjSqrt a⁻¹ʳ b) * sqrt a := by rw [geometricMean_eq_mul]; noncomm_ring
    _ = sqrt a * (sqrt (conjSqrt a⁻¹ʳ b) * sqrt (conjSqrt a⁻¹ʳ b)) * sqrt a := by
          rw [hsa]; noncomm_ring
    _ = sqrt a * conjSqrt a⁻¹ʳ b * sqrt a := by rw [sqrt_mul_sqrt_self _ hZ]
    _ = b := conjSqrt_conjSqrt_ringInverse a b ha

/-- **Same-base GM identity**: for strictly positive `a` in a C⋆-algebra, the geometric mean of
two real powers of `a` is the power at the midpoint of the exponents:
`M₀(a^p, a^q) = a^{(p+q)/2}`. Direct consequence of the multiplicativity of `rpow` on a single
base (`rpow_add` for `IsUnit a`) plus `sqrt_eq_rpow`. -/
lemma geometricMean_rpow_rpow {a : A} (ha : IsStrictlyPositive a) (p q : ℝ) :
    geometricMean (a ^ p) (a ^ q) = a ^ ((p + q) / 2) := by
  rw [geometricMean_eq_mul, ha.inverse_rpow, conjSqrt_apply, ha.sqrt_rpow (-p),
    ← rpow_add ha.isUnit, ← rpow_add ha.isUnit, ha.sqrt_rpow, ha.sqrt_rpow,
    ← rpow_add ha.isUnit, ← rpow_add ha.isUnit]
  congr 1
  ring

end GeometricMean

end CFC
