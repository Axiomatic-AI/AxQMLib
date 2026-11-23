/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# A normal element of a C⋆-algebra is self-adjoint iff its spectrum is real

For a *normal* element `a` (`IsStarNormal a`) of a complex C⋆-algebra, `a` is self-adjoint if and
only if every point of its spectrum is real.

## Main results

* `isSelfAdjoint_iff_forall_spectrum_im_eq_zero`: for `a : A` with `[CStarAlgebra A]` and
  `IsStarNormal a`, `IsSelfAdjoint a ↔ ∀ z ∈ spectrum ℂ a, z.im = 0`.

The forward implication is `IsSelfAdjoint.im_eq_zero_of_mem_spectrum` and needs no normality; the
converse runs the continuous functional calculus for normal elements
(`QuasispectrumRestricts.isSelfAdjoint`), for which normality is essential.
-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A]

/-- A normal element `a` of a complex C⋆-algebra is self-adjoint if and only if every point of its
spectrum is real. The forward direction holds for any self-adjoint element; the converse recovers
self-adjointness from a real spectrum via the functional calculus, using normality. -/
theorem isSelfAdjoint_iff_forall_spectrum_im_eq_zero {a : A} (ha : IsStarNormal a) :
    IsSelfAdjoint a ↔ ∀ z ∈ spectrum ℂ a, z.im = 0 := by
  refine ⟨fun hsa z hz => hsa.im_eq_zero_of_mem_spectrum hz, fun hreal => ?_⟩
  have hsub : spectrum ℂ a ⊆ Set.range (algebraMap ℝ ℂ) := fun z hz =>
    ⟨z.re, by simp [Complex.ext_iff, hreal z hz]⟩
  have hsr : SpectrumRestricts a Complex.reCLM :=
    SpectrumRestricts.of_subset_range_algebraMap (fun r => by simp) hsub
  exact (quasispectrumRestricts_iff_spectrumRestricts.mpr hsr).isSelfAdjoint a
