/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Additional API for `CFC.conjSqrt`

Nonnegativity of `conjSqrt c a` for `0 ≤ a`, and the squaring identity
`(conjSqrt a x) * (conjSqrt a x) = conjSqrt a (x * a * x)` for `0 ≤ a`.
-/

namespace CFC

open Ring

@[expose] public section ConjSqrt

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul A]

lemma conjSqrt_nonneg (c : A) {a : A} (ha : 0 ≤ a) : 0 ≤ conjSqrt c a :=
  map_zero (conjSqrt c) ▸ conjSqrt_monotone ha

end SeparatelyContinuousMul

variable [IsSemitopologicalRing A] [T2Space A]

/-- Squaring the `conjSqrt` map: `(conjSqrt a x) * (conjSqrt a x) = conjSqrt a (x * a * x)`
for `0 ≤ a`. Direct consequence of `conjSqrt_apply` + `sqrt_mul_sqrt_self`. -/
lemma conjSqrt_mul_self (a x : A) (ha : 0 ≤ a := by cfc_tac) :
    conjSqrt a x * conjSqrt a x = conjSqrt a (x * a * x) := by
  rw [conjSqrt_apply]
  calc (sqrt a * x * sqrt a) * (sqrt a * x * sqrt a)
      = sqrt a * x * (sqrt a * sqrt a) * x * sqrt a := by noncomm_ring
    _ = sqrt a * (x * a * x) * sqrt a := by rw [sqrt_mul_sqrt_self a ha]; noncomm_ring

end ConjSqrt

end CFC
