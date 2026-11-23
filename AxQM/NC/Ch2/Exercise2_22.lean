/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.SymmetricEigenvectorOrthogonal

/-!
# Nielsen & Chuang, Exercise 2.22 (Eigenvectors with distinct eigenvalues are orthogonal)

Prove two eigenvectors of a Hermitian operator with different eigenvalues are orthogonal.

A **Hermitian** (self-adjoint) operator `T` satisfies `⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y`. If
`T|v⟩ = μ|v⟩` and `T|w⟩ = ν|w⟩` with `μ ≠ ν`, symmetry gives `⟪T v, w⟫ = ⟪v, T w⟫`, i.e.
`μ*⟪v, w⟫ = ν⟪v, w⟫` (the eigenvalues of a Hermitian operator are real, so `μ* = μ`), whence
`(μ - ν)⟪v, w⟫ = 0` and, `μ` and `ν` being distinct, `⟪v, w⟩ = 0`: the eigenvectors are orthogonal.

Compare Exercises 2.17 and 2.18 on the eigenvalues of Hermitian and unitary operators.

## The declaration

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/SymmetricEigenvectorOrthogonal.lean`:

* `LinearMap.IsSymmetric.inner_eq_zero_of_hasEigenvector_of_ne` — the direct form of the exercise:
  for a symmetric operator `T : E →ₗ[𝕜] E` on an inner product space over `𝕜` (`RCLike 𝕜`), if
  `Module.End.HasEigenvector T μ v`, `Module.End.HasEigenvector T ν w`, and `μ ≠ ν`, then
  `inner 𝕜 v w = 0`.

## N&C ↦ Mathlib dictionary and fidelity

* **Hermitian operator** `T` is `LinearMap.IsSymmetric T`, defined as `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.
  For a bounded operator on a complex Hilbert space this is exactly self-adjointness; N&C's
  Hermitian matrix on `ℂⁿ` is the finite-dimensional instance `E = EuclideanSpace ℂ (Fin n)`. The
  statement is
  over an arbitrary inner product space with `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`, N&C's `ℂ` being the special
  case) and fixes no dimension — a faithful generalisation, not a weakening.
* An **eigenvector** `|v⟩ ≠ 0` with `T|v⟩ = μ|v⟩` is `Module.End.HasEigenvector T μ v`
  (`Module.End.HasEigenvector.apply_eq_smul : T v = μ • v`, with the vector nonzero by definition).
  Using `HasEigenvector` for both vectors captures N&C's "eigenvectors" faithfully.
* **Different eigenvalues** is `μ ≠ ν`; **orthogonal** is `inner 𝕜 v w = 0`, the vanishing of the
  inner product.

The proof rests on `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` (the eigenvalues of a symmetric
operator are real) to turn the conjugate `μ*` arising from conjugate-linearity of the inner product
in its first argument back into `μ`, so that distinctness of `μ` and `ν` cancels the scalar factor.
Mathlib's `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` states the same fact for eigenspaces
(they form an orthogonal family); this declaration is the complementary eigenvector idiom the
exercise is phrased in.
-/
