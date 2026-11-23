/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Interval bounds for the real spectrum of a nonnegative element

The real spectrum of a nonnegative element of a normed ℝ-algebra lies in `Icc 0 (‖a‖ * ‖1‖)`,
or in `Icc 0 ‖a‖` when `‖1‖ = 1`.
-/

variable {𝕜 : Type*} {A : Type*}

@[expose] public section

namespace spectrum

section SpectrumCompact

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- For a nonnegative element `a` of a normed ℝ-algebra, the real spectrum of `a` lies in
`Icc 0 (‖a‖ * ‖(1 : A)‖)`. Combines `spectrum_nonneg_of_nonneg` (for the lower bound) with
`norm_le_norm_mul_of_mem` (for the upper bound). No `NormOneClass` hypothesis. -/
theorem subset_Icc_norm_mul_of_nonneg [NormedAlgebra ℝ A] [PartialOrder A]
    [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    spectrum ℝ a ⊆ Set.Icc 0 (‖a‖ * ‖(1 : A)‖) := fun k hk ↦ by
  have h_nonneg : 0 ≤ k := spectrum_nonneg_of_nonneg ha hk
  refine ⟨h_nonneg, ?_⟩
  calc k = ‖k‖ := (Real.norm_of_nonneg h_nonneg).symm
    _ ≤ ‖a‖ * ‖(1 : A)‖ := norm_le_norm_mul_of_mem hk

/-- For a nonnegative element `a` of a normed ℝ-algebra with `‖1‖ = 1`, the real spectrum
of `a` lies in `Icc 0 ‖a‖`. Combines `spectrum_nonneg_of_nonneg` (for the lower bound) with
`norm_le_norm_of_mem` (for the upper bound). -/
theorem subset_Icc_norm_of_nonneg [NormOneClass A] [NormedAlgebra ℝ A] [PartialOrder A]
    [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    spectrum ℝ a ⊆ Set.Icc 0 ‖a‖ := fun k hk ↦ by
  have h_nonneg : 0 ≤ k := spectrum_nonneg_of_nonneg ha hk
  refine ⟨h_nonneg, ?_⟩
  calc k = ‖k‖ := (Real.norm_of_nonneg h_nonneg).symm
    _ ≤ ‖a‖ := norm_le_norm_of_mem hk

end SpectrumCompact

end spectrum
