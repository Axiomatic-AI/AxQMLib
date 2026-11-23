/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finrank of a `PiTensorProduct`

For a finite family `M : ι → Type*` of finite free modules over a commutative semiring `R`
satisfying the strong rank condition, the finite rank of the `ι`-ary tensor product `⨂[R] i, M i`
is the product of the finite ranks of the factors.

## Main results

* `Module.finrank_piTensorProduct` — `finrank R (⨂[R] i, M i) = ∏ i, finrank R (M i)`.
-/

@[expose] public section

open scoped TensorProduct

/-- The finite rank of a tensor product `⨂[R] i, M i` over a finite index type `ι` is the product
`∏ i, finrank R (M i)` of the finite ranks of the factors. Obtained from the tensor-product basis
`Basis.piTensorProduct`, whose index type is `Π i, (basis index of M i)`, together with
`Fintype.card_pi`. -/
theorem Module.finrank_piTensorProduct {ι R : Type*} {M : ι → Type*} [CommSemiring R]
    [StrongRankCondition R] [Fintype ι] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] :
    Module.finrank R (⨂[R] i, M i) = ∏ i, Module.finrank R (M i) := by
  classical
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct fun i => Module.finBasis R (M i))]
  simp [Fintype.card_pi]

end
