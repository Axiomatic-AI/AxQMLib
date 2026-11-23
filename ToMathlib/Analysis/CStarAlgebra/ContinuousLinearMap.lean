/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Global continuous functional calculus instance for `E →L[ℂ] E`

This file promotes the generic `IsStarNormal.instContinuousFunctionalCalculus` theorem (made
`local instance` only in `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`,
presumably to avoid synthesis cost on arbitrary C⋆-algebras) to a global instance specifically
for `E →L[ℂ] E`. The `IsSelfAdjoint`-over-ℝ continuous functional calculus then fires
automatically via `IsSelfAdjoint.instIsometricContinuousFunctionalCalculus` and the generic
`IsSelfAdjoint.instContinuousFunctionalCalculus` chain. This makes `cfc f T` usable on
`T : E →L[ℂ] E` for `f : ℂ → ℂ` (under `IsStarNormal T`) and for `f : ℝ → ℝ` (under
`IsSelfAdjoint T`) directly, without manually invoking the local-instance attribute.
-/

@[expose] public section

/-- The continuous functional calculus for star-normal continuous linear operators on a complex
Hilbert space. This is a global-instance promotion of the generic
`IsStarNormal.instContinuousFunctionalCalculus` theorem, specialized to the operator algebra
`E →L[ℂ] E`. -/
instance ContinuousLinearMap.instContinuousFunctionalCalculus_isStarNormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    ContinuousFunctionalCalculus ℂ (E →L[ℂ] E) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
