/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Normal
public import ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import ToMathlib.Analysis.CStarAlgebra.Matrix
public import ToMathlib.LinearAlgebra.Matrix.Hermitian

/-!
# A normal matrix is Hermitian iff its spectrum is real

A *normal* complex square matrix `A` (`IsStarNormal A`, i.e. `Aᴴ * A = A * Aᴴ`) is Hermitian if and
only if every point of its spectrum — equivalently, every eigenvalue — is real.

## Main results

* `Matrix.isHermitian_iff_forall_spectrum_im_eq_zero`: for a normal `A : Matrix n n ℂ`,
  `A.IsHermitian ↔ ∀ z ∈ spectrum ℂ A, z.im = 0`.

## Implementation notes

This is the matrix transport corollary of the general C⋆-algebra fact
`isSelfAdjoint_iff_forall_spectrum_im_eq_zero`. `Matrix n n ℂ` carries a `CStarRing` structure (in
the `Matrix.Norms.L2Operator` scope) but is not registered as a `CStarAlgebra`, so we push the
statement along the star-algebra equivalence `Matrix.toEuclideanCLM` to the C⋆-algebra
`EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n`, where the general lemma applies. Spectrum,
`IsSelfAdjoint`, and `IsStarNormal` all transfer across the equivalence — the first by
`AlgEquiv.spectrum_eq`, the latter two because `Matrix.toEuclideanCLM` is a star ring isomorphism.

The statement is fixed to `ℂ`: over `ℝ` the `ℝ`-spectrum omits the genuinely complex eigenvalues, so
the characterization would no longer capture "real eigenvalues".
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A normal matrix is Hermitian iff it has real eigenvalues** (Nielsen & Chuang, Exercise 2.17).
For a normal complex matrix `A` (`IsStarNormal A`, i.e. `Aᴴ * A = A * Aᴴ`), `A` equals its conjugate
transpose exactly when every point of its spectrum — equivalently, every eigenvalue — is real. This
is the matrix transport corollary of `isSelfAdjoint_iff_forall_spectrum_im_eq_zero`. -/
theorem isHermitian_iff_forall_spectrum_im_eq_zero {A : Matrix n n ℂ} (hA : IsStarNormal A) :
    A.IsHermitian ↔ ∀ z ∈ spectrum ℂ A, z.im = 0 := by
  -- Transport to the C⋆-algebra of operators on `EuclideanSpace ℂ n` along `toEuclideanCLM`.
  set φ : Matrix n n ℂ ≃⋆ₐ[ℂ] _ := Matrix.toEuclideanCLM
  have hspec : spectrum ℂ (φ A) = spectrum ℂ A := AlgEquiv.spectrum_eq _ A
  -- `φ` is a star ring isomorphism, so it preserves normality and self-adjointness.
  have hφA : IsStarNormal (φ A) := hA.map φ
  have hHerm : A.IsHermitian ↔ IsSelfAdjoint (φ A) := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    simp only [isSelfAdjoint_iff, ← map_star, (EquivLike.injective φ).eq_iff]
  rw [hHerm, isSelfAdjoint_iff_forall_spectrum_im_eq_zero hφA, hspec]

end Matrix
