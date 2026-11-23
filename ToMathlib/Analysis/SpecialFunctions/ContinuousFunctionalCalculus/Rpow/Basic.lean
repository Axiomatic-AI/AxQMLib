/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# `sqrt`/`Ring.inverse` of `rpow`, without the `x ≠ 0` restriction

`IsStrictlyPositive.sqrt_rpow` and `IsStrictlyPositive.inverse_rpow` drop the `x ≠ 0`
hypothesis from `CFC.sqrt_rpow`/`CFC.inverse_rpow` by handling `x = 0` directly via `rpow_zero`.
-/

@[expose] public section

namespace CFC

section Unital

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

section unital_vs_nonunital

open Ring
variable [IsSemitopologicalRing A] [T2Space A]
open scoped ContinuousFunctionalCalculus

/-- The strict-positivity form of `sqrt_rpow`: for strictly positive `a`,
`sqrt (a^x) = a^(x/2)` for any real `x`. -/
lemma _root_.IsStrictlyPositive.sqrt_rpow {a : A} (ha : IsStrictlyPositive a) (x : ℝ) :
    sqrt (a ^ x) = a ^ (x / 2) :=
  CFC.sqrt_rpow ha.isUnit

/-- The strict-positivity form of `inverse_rpow`: for strictly positive `a`,
`Ring.inverse (a^x) = a^(-x)` for any real `x`. -/
lemma _root_.IsStrictlyPositive.inverse_rpow {a : A} (ha : IsStrictlyPositive a) (x : ℝ) :
    Ring.inverse (a ^ x) = a ^ (-x) :=
  CFC.inverse_rpow a x ha

end unital_vs_nonunital

end Unital

end CFC
