/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Nielsen & Chuang, Exercise 2.3 (Matrix representation for operator products)

Show matrix rep of composition BA is the matrix product of reps of B and A.

The result is *already present in Mathlib* as a standard lemma: the exercise is discharged by the
existing declaration below, whose correspondence with N&C's notation is recorded here.

## The declaration

`LinearMap.toMatrix_comp`, in `Mathlib/LinearAlgebra/Matrix/ToLin.lean`, states — for
`g : M₁ →ₗ[R] M₂` and `f : M₂ →ₗ[R] M₃` over a commutative semiring `R`, with (finite) bases
`v₁, v₂, v₃` of `M₁, M₂, M₃` — that
`LinearMap.toMatrix v₁ v₃ (f ∘ₗ g) = LinearMap.toMatrix v₂ v₃ f * LinearMap.toMatrix v₁ v₂ g`.
N&C's statement is over finite-dimensional complex vector spaces; the Mathlib lemma is strictly
more general (arbitrary `R`, arbitrary finite bases), so this is a faithful generalisation, not a
weakening — N&C's case is the instance `R = ℂ`.

## Correspondence with N&C

N&C fix the matrix representation of a linear operator by `A|vⱼ⟩ = ∑ᵢ Aᵢⱼ |wᵢ⟩` (eq. 2.12): the
input basis indexes the columns and the output basis the rows. This is exactly `LinearMap.toMatrix`,
whose `(i, j)` entry is the `i`-th coordinate, in the output basis, of the image of the `j`-th input
basis vector. N&C's composition `BA` means "`B` after `A`" (`(BA)|v⟩ ≡ B(A|v⟩)`, p. 64), i.e.
`B ∘ₗ A`. The dictionary from N&C to Mathlib is therefore:

* `A : V → W`  ↦  `g : M₁ →ₗ[R] M₂`, with input basis `v₁ = (|vⱼ⟩)` and output basis `v₂ = (|wᵢ⟩)`;
* `B : W → X`  ↦  `f : M₂ →ₗ[R] M₃`, with input basis `v₂ = (|wⱼ⟩)` and output basis `v₃ = (|xₖ⟩)`;
* `BA = B ∘ A`  ↦  `f ∘ₗ g`.

Under this dictionary `LinearMap.toMatrix_comp` reads `[BA] = [B] · [A]` — the matrix of `BA` with
respect to bases `(v₁, v₃)` is the product of the matrix of `B` (bases `(v₂, v₃)`) with that of `A`
(bases `(v₁, v₂)`) — which is precisely the exercise's claim.
-/
