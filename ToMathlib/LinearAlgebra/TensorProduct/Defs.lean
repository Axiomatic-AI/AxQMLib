/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Tensor products of scalar-weighted finite sums

Distributes the tensor product of two scalar-weighted finite sums into a doubly-indexed sum.
-/

@[expose] public section

namespace TensorProduct

variable {R : Type*} [CommSemiring R]
variable {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The tensor product of two scalar-weighted finite sums distributes into a doubly-indexed sum:
`(s • ∑ a ∈ sa, f a) ⊗ₜ (t • ∑ b ∈ sb, g b) = (s * t) • ∑ a ∈ sa, ∑ b ∈ sb, f a ⊗ₜ g b`. -/
theorem smul_sum_tmul_smul_sum {α β : Type*} (s t : R) (sa : Finset α) (sb : Finset β)
    (f : α → M) (g : β → N) :
    (s • ∑ a ∈ sa, f a) ⊗ₜ[R] (t • ∑ b ∈ sb, g b)
      = (s * t) • ∑ a ∈ sa, ∑ b ∈ sb, f a ⊗ₜ[R] g b := by
  rw [← smul_tmul', tmul_smul, smul_smul, sum_tmul]
  simp only [tmul_sum]

end TensorProduct
