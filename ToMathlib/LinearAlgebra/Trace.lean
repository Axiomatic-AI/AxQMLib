/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# Additional API for `LinearMap.trace`

* `LinearMap.trace_eq_zero_of_not_exists_finset_basis` /
  `LinearMap.trace_apply_eq_zero_of_not_exists_finset_basis`: named forms of the `dif_neg`
  branch of the definition of `trace`.
-/

@[expose] public section

noncomputable section

universe u v

namespace LinearMap

open Module

section

variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]

/-- The trace of an endomorphism vanishes when there is no finite basis. The named form of
the `dif_neg`-on-the-`trace`-definition pattern. -/
theorem trace_eq_zero_of_not_exists_finset_basis
    (h : ¬ ∃ s : Finset M, Nonempty (Basis s R M)) :
    trace R M = 0 := by
  rw [trace, dite_eq_right h]

/-- Apply-form of `trace_eq_zero_of_not_exists_finset_basis`. -/
theorem trace_apply_eq_zero_of_not_exists_finset_basis
    (h : ¬ ∃ s : Finset M, Nonempty (Basis s R M)) (f : M →ₗ[R] M) :
    trace R M f = 0 := by
  rw [trace_eq_zero_of_not_exists_finset_basis R h, LinearMap.zero_apply]

end

end LinearMap
