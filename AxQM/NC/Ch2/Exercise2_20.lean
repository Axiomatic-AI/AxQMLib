/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.MatrixBasisChange

/-!
# Nielsen & Chuang, Exercise 2.20 (Basis changes)

Characterize the relationship between two matrix reps A' and A'' under basis change.

**Answer.** The two representations are related by the *unitary change-of-basis matrix* `U` with
entries `Uᵢⱼ = ⟨wᵢ|vⱼ⟩` (the coordinates of the `v`-basis in the `w`-basis). Explicitly

`A'' = U A' U†,   with U unitary (U†U = UU† = I).`

Since `U` is unitary this is a *unitary similarity transformation*: the matrix representation of an
operator is basis-dependent, but any two orthonormal-basis representations of the same operator are
unitarily conjugate. (Substituting the inner-product forms and using completeness of the bases,
`∑ₖ |vₖ⟩⟨vₖ| = ∑ₖ |wₖ⟩⟨wₖ| = I`, recovers `⟨wᵢ|A|wⱼ⟩ = ∑ₖₗ ⟨wᵢ|vₖ⟩⟨vₖ|A|vₗ⟩⟨vₗ|wⱼ⟩`, i.e.
`A'' = U A' U†`.)

Compare the adjoint and unitary exercises 2.13, 2.14, 2.15 and 2.18.

## The declarations

In `ToMathlib/Analysis/InnerProductSpace/MatrixBasisChange.lean`:

* `LinearMap.toMatrixOrthonormal_change_orthonormalBasis` — the direct form of the exercise: for
  orthonormal bases `v w : OrthonormalBasis ι 𝕜 E` of a finite-dimensional inner product space and
  `A : E →ₗ[𝕜] E`,
  `LinearMap.toMatrixOrthonormal w A = U * LinearMap.toMatrixOrthonormal v A * Uᴴ`,
  where `U := w.toBasis.toMatrix ⇑v` is the change-of-basis matrix.
* `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose` — the reusable core it is built on: the
  reverse change-of-basis matrix between orthonormal bases equals the conjugate transpose,
  `(a.toBasis.toMatrix ⇑b)ᴴ = b.toBasis.toMatrix ⇑a`.

## N&C ↦ Mathlib dictionary and fidelity

* `V` is the finite-dimensional inner product space `E` over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`;
  N&C's `ℂ` is the special case). N&C's `V = ℂᵈ` is the instance `E = EuclideanSpace 𝕜 (Fin d)`.
* The **orthonormal bases** `|vᵢ⟩`, `|wᵢ⟩` are `v w : OrthonormalBasis ι 𝕜 E` over a common index
  `ι`, matching N&C's use of the same index range `i` for both bases (same space, same dimension).
* The **matrix representation** `A'` with entries `A'ᵢⱼ = ⟨vᵢ|A|vⱼ⟩` is
  `LinearMap.toMatrixOrthonormal v A`, whose entries are exactly these inner products
  (`LinearMap.toMatrixOrthonormal_apply_apply`: `(toMatrixOrthonormal v A) i j = ⟪v i, A (v j)⟫`);
  likewise `A''` is `LinearMap.toMatrixOrthonormal w A`.
* The **change-of-basis matrix** `U` with `Uᵢⱼ = ⟨wᵢ|vⱼ⟩` is `w.toBasis.toMatrix ⇑v`; it is unitary
  by `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`. N&C's `U†` is `Uᴴ`
  (`Matrix.conjTranspose`), and unitarity gives `Uᴴ = U⁻¹`, so the identity
  `A'' = U A' Uᴴ` is precisely N&C's unitary similarity `A'' = U A' U†`.

The statement is a faithful transcription of the exercise, not a weakening: it fixes no dimension,
quantifies over arbitrary orthonormal bases and an arbitrary operator, and yields the exact
conjugation identity. The characterization is complete — the relationship is the explicit unitary
conjugation, with the unitarity of the conjugating matrix supplied by the cited Mathlib lemma.
-/
