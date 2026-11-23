/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Polar form of the complex conjugate
-/

public section

open Filter Metric Set
open scoped ComplexConjugate Real Topology

namespace Complex

/-- Polar form of the complex conjugate: `conj z = ‖z‖ * exp (-arg z * I)`, the conjugate
counterpart of `Complex.norm_mul_exp_arg_mul_I`. -/
theorem star_eq_norm_mul_exp_neg_arg_mul_I (z : ℂ) :
    star z = (‖z‖ : ℂ) * exp (-(arg z : ℂ) * I) := by
  change (starRingEnd ℂ) z = _
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [map_mul, conj_ofReal, ← exp_conj, map_mul, conj_ofReal, conj_I]
  ring_nf

end Complex
