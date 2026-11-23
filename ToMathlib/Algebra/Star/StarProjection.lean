/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Star.StarProjection

/-!
# Star projections: adjoint absorption

Two small facts about `IsStarProjection`: a star projection absorbs itself against its own
adjoint on either side, `star p * p = p` and `p * star p = p`.
-/

@[expose] public section

variable {R : Type*}

namespace IsStarProjection

variable {p : R}

/-- A star projection absorbs itself on the right of its adjoint: `star p * p = p`. -/
theorem star_mul_self [Mul R] [Star R] (hp : IsStarProjection p) : star p * p = p := by
  rw [hp.isSelfAdjoint.star_eq]; exact hp.isIdempotentElem

/-- A star projection absorbs itself on the left of its adjoint: `p * star p = p`. -/
theorem mul_star_self [Mul R] [Star R] (hp : IsStarProjection p) : p * star p = p := by
  rw [hp.isSelfAdjoint.star_eq]; exact hp.isIdempotentElem

end IsStarProjection
