/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Diagonal

/-!
# Nielsen & Chuang, Exercise 2.4 (Matrix representation for identity)

Show the identity operator has the identity matrix representation.

The result is *already present in Mathlib* as a standard lemma: the exercise is discharged by the
existing declarations below, whose correspondence with N&C's statement is recorded here.

## The declarations

`LinearMap.toMatrix_id`, in `Mathlib/LinearAlgebra/Matrix/ToLin.lean`, states — for a (finite)
basis `v₁ : Module.Basis n R M₁` of a module `M₁` over a commutative semiring `R` — that
`LinearMap.toMatrix v₁ v₁ LinearMap.id = 1`. That is: the matrix representation of the identity
operator, taken with **the same basis `v₁` for both input and output**, is the identity matrix `1`.

`Matrix.one_apply`, in `Mathlib/Data/Matrix/Diagonal.lean`, spells out N&C's description of that
matrix entrywise: `(1 : Matrix n n R) i j = if i = j then 1 else 0` — one along the diagonal
(`i = j`) and zero everywhere else. The two together are exactly the exercise's claim.

N&C's statement is over a finite-dimensional complex vector space; the Mathlib lemma is strictly
more general (arbitrary commutative semiring `R`, arbitrary finite basis `n`), so this is a faithful
generalisation, not a weakening — N&C's case is the instance `R = ℂ`.

## Correspondence with N&C

N&C fix the matrix representation of a linear operator by `A|vⱼ⟩ = ∑ᵢ Aᵢⱼ |wᵢ⟩` (eq. 2.12): the
input basis indexes the columns and the output basis the rows. This is exactly `LinearMap.toMatrix`,
whose `(i, j)` entry is the `i`-th coordinate, in the output basis, of the image of the `j`-th input
basis vector. Under this dictionary:

* the identity operator on `V` ↦ `LinearMap.id`;
* "the same input and output bases" ↦ using one basis `v₁` in **both** slots of
  `LinearMap.toMatrix`.

The hypothesis "same input and output bases" is essential and is honoured precisely by the repeated
`v₁ v₁`: with *distinct* input/output bases `b, b'` the identity's matrix is instead the
change-of-basis matrix `b'.toMatrix ⇑b` (`LinearMap.toMatrix_id_eq_basis_toMatrix`), which is not
the identity in general. Reading `LinearMap.toMatrix_id` with N&C's dictionary therefore gives
`[I] = 1` — the identity operator's matrix, with respect to a single basis, is one on the diagonal
and zero off it — which is precisely the exercise's claim.
-/
