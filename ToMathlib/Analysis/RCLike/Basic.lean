/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Extra `RCLike` lemmas

Extends `Mathlib.Analysis.RCLike.Basic` with a handful of small conjugation/real-part facts.
-/

public section

open scoped ComplexConjugate

namespace RCLike

variable {K : Type*} [RCLike K]

theorem isSelfAdjoint_ofReal (r : ℝ) : IsSelfAdjoint ((r : ℝ) : K) := by
  rw [isSelfAdjoint_iff, star_def, conj_ofReal]

/-- `push_cast`-friendly reverse of `RCLike.mul_conj`: the real-coerced squared norm
equals `z * conj z`. Saves the consumer's `push_cast; rw [← RCLike.mul_conj]` pair. -/
theorem ofReal_norm_sq_eq_mul_conj (z : K) : ((‖z‖ ^ 2 : ℝ) : K) = z * conj z := by
  rw [mul_conj]; push_cast; ring

/-- The real part distributes over finite sums. Lifts `RCLike.reLm`'s `map_sum` through the
function-coercion. -/
theorem re_sum {α : Type*} (s : Finset α) (f : α → K) :
    re (∑ i ∈ s, f i) = ∑ i ∈ s, re (f i) :=
  map_sum (reLm (K := K)) f s

end RCLike
