/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Ring isomorphisms preserve `Ring.inverse`

A ring isomorphism preserves `Ring.inverse`.
-/

@[expose] public section

namespace RingEquiv

variable {R S : Type*} [Semiring R] [Semiring S]

section GroupPower

/-- A ring isomorphism preserves `Ring.inverse`. -/
protected theorem map_ringInverse (f : R ≃+* S) (x : R) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  by_cases h : IsUnit x
  · refine (h.map (f : R →* S)).mul_right_cancel ?_
    change f (Ring.inverse x) * f x = Ring.inverse (f x) * f x
    rw [← map_mul, Ring.inverse_mul_cancel x h, map_one, eq_comm,
      Ring.inverse_mul_cancel (f x) (h.map (f : R →* S))]
  · rw [Ring.inverse_non_unit _ h,
      Ring.inverse_non_unit _ (fun hu ↦ h (f.symm_apply_apply x ▸ hu.map f.symm.toRingHom)),
      map_zero]

end GroupPower

end RingEquiv
