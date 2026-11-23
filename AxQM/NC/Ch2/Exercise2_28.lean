/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Nielsen & Chuang, Exercise 2.28 (Transpose, conjugation, adjoint distribute over `⊗`)

Show transpose, conjugation, adjoint distribute over the tensor product.

This is pure linear algebra about the tensor (Kronecker) product of matrices — the three
entrywise/transpose involutions commute with `⊗`.

N&C introduce `⊗` on operators abstractly (`(A ⊗ B)(|v⟩ ⊗ |w⟩) ≡ A|v⟩ ⊗ B|w⟩`, eq. 2.45) and then,
immediately before this exercise, give its concrete matrix form — the **Kronecker product** (eq.
2.50), whose `((i₁,i₂),(j₁,j₂))` entry is `Aᵢ₁ⱼ₁ Bᵢ₂ⱼ₂`. Mathlib's `⊗ₖ`
(`Matrix.kroneckerMap (· * ·)`, notation scoped in `Matrix.Kronecker`) is exactly that matrix
representation, so the exercise's three claims are the following `⊗ₖ` lemmas in
`Mathlib/LinearAlgebra/Matrix/Kronecker.lean` and `ToMathlib/LinearAlgebra/Matrix/Kronecker.lean`.

## The formalisation

* **Transpose — `(A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ`.** `Matrix.kroneckerMap_transpose`, stated generically for any
  entrywise combiner `f`, gives `kroneckerMap f Aᵀ Bᵀ = (kroneckerMap f A B)ᵀ`. Specialising
  `f := (· * ·)` and reading it right-to-left is precisely `(A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ`.

* **Complex conjugation — `(A ⊗ B)* = A* ⊗ B*`.** `Matrix.map_star_kronecker` gives
  `(x ⊗ₖ y).map star = x.map star ⊗ₖ y.map star`. N&C's entrywise complex conjugate `A*` is the
  matrix `A.map star` (each entry replaced by its conjugate, no transpose). This lemma is in
  `ToMathlib/LinearAlgebra/Matrix/Kronecker.lean`, in the style of
  `Matrix.conjTranspose_kronecker` below (proof `ext; simp`).

* **Adjoint — `(A ⊗ B)† = A† ⊗ B†`.** `Matrix.conjTranspose_kronecker` gives
  `(x ⊗ₖ y)ᴴ = xᴴ ⊗ₖ yᴴ`. N&C's adjoint `A† = (A*)ᵀ` is the conjugate transpose `Aᴴ`.

All three hold under `[CommMagma R] [StarMul R]` (conjugation/adjoint) resp. for an arbitrary
combiner (transpose), over arbitrary index types. N&C's case — complex matrices `R = ℂ` (a field
whose `star` is complex conjugation) with finite indices — is an instance, so these are faithful
generalisations, not weakenings.

## Correspondence with N&C

The dictionary N&C `↦` Mathlib is: tensor product `A ⊗ B` ↦ Kronecker product `A ⊗ₖ B`;
transpose `Aᵀ` ↦ `Aᵀ` (`Matrix.transpose`); complex conjugate `A*` ↦ `A.map star`; adjoint
`A† = (A*)ᵀ` ↦ `Aᴴ` (`Matrix.conjTranspose`). Under it the three displayed equalities of eq. (2.53)
read off as the three lemmas above, and the third is the composite of the first two exactly as in
N&C (`†` is `*` followed by `ᵀ`).
-/
