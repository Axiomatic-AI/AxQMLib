/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Matrix representations under a change of orthonormal basis

Let `E` be a finite-dimensional inner product space over `𝕜` (`RCLike 𝕜`) and let `A : E →ₗ[𝕜] E`
be an operator. Its matrix representation with respect to an orthonormal basis `v` is
`LinearMap.toMatrixOrthonormal v A`, whose entries are the inner products
`(LinearMap.toMatrixOrthonormal v A) i j = ⟪v i, A (v j)⟫`
(`LinearMap.toMatrixOrthonormal_apply_apply`). This file records how that matrix transforms when the
basis is changed to another orthonormal basis `w` — Nielsen & Chuang, Exercise 2.20.

Writing `U := w.toBasis.toMatrix ⇑v` for the change-of-basis matrix (its entries are
`U i j = ⟪w i, v j⟫`), `U` is *unitary* (`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`)
and the two representations are related by the unitary similarity

`LinearMap.toMatrixOrthonormal w A = U * LinearMap.toMatrixOrthonormal v A * Uᴴ`.

Because `U` is unitary, `Uᴴ = U⁻¹`, so this is exactly the conjugation of the representation in
basis `v` by the unitary matrix connecting the two orthonormal bases.

## Main results

* `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose`: the change-of-basis matrix in the
  reverse direction is the conjugate transpose, `(a.toBasis.toMatrix ⇑b)ᴴ = b.toBasis.toMatrix ⇑a`.
  For orthonormal bases the inverse change of basis coincides with the adjoint.
* `LinearMap.toMatrixOrthonormal_change_orthonormalBasis`: the two matrix representations of an
  operator with respect to two orthonormal bases are related by conjugation by the (unitary)
  change-of-basis matrix — the answer to N&C Exercise 2.20.

The unitarity of the conjugating matrix `w.toBasis.toMatrix ⇑v` is already available as
`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`, so the content added here is the
conjugation identity itself, phrased with the conjugate transpose to make the unitary/adjoint
structure explicit. The general (arbitrary-basis) similarity is
`basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`; the orthonormal refinement is that the
conjugating matrix is unitary and the reverse change of basis is its conjugate transpose.
-/

@[expose] public section

open scoped Matrix

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

namespace OrthonormalBasis

/-- The change-of-basis matrix between two orthonormal bases, read in the reverse direction, is the
conjugate transpose: `(a.toBasis.toMatrix ⇑b)ᴴ = b.toBasis.toMatrix ⇑a`.

Equivalently, for orthonormal bases the inverse of the change-of-basis matrix is its adjoint — the
matrix form of the fact that the change-of-basis map is unitary. The proof combines the general
inverse relation `Module.Basis.toMatrix_mul_toMatrix_flip` (`U * (b→a) = 1`) with unitarity
`OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self` (`Uᴴ * U = 1`): a left inverse
and a right inverse of `U` agree. -/
theorem toMatrix_orthonormalBasis_conjTranspose (a b : OrthonormalBasis ι 𝕜 E) :
    (a.toBasis.toMatrix ⇑b)ᴴ = b.toBasis.toMatrix ⇑a := by
  classical
  have hflip : a.toBasis.toMatrix ⇑b * b.toBasis.toMatrix ⇑a = 1 := by
    simpa only [OrthonormalBasis.coe_toBasis] using
      Module.Basis.toMatrix_mul_toMatrix_flip a.toBasis b.toBasis
  exact left_inv_eq_right_inv (a.toMatrix_orthonormalBasis_conjTranspose_mul_self b) hflip

end OrthonormalBasis

variable [DecidableEq ι] [FiniteDimensional 𝕜 E]

namespace LinearMap

/-- **Nielsen & Chuang, Exercise 2.20 (Basis changes).** The matrix representations of an operator
`A : E →ₗ[𝕜] E` with respect to two orthonormal bases `v` and `w` of a finite-dimensional inner
product space are related by conjugation by the change-of-basis matrix `U := w.toBasis.toMatrix ⇑v`:

`LinearMap.toMatrixOrthonormal w A = U * LinearMap.toMatrixOrthonormal v A * Uᴴ`.

Entrywise, `(LinearMap.toMatrixOrthonormal v A) i j = ⟪v i, A (v j)⟫` and
`U i j = ⟪w i, v j⟫`, so this is precisely N&C's `A'' = U A' U†` relating
`A'ᵢⱼ = ⟨vᵢ|A|vⱼ⟩` and `A''ᵢⱼ = ⟨wᵢ|A|wⱼ⟩`. The conjugating matrix `U` is unitary
(`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`), so `Uᴴ = U⁻¹` and the relationship is a
unitary similarity transformation.

The proof rewrites the reverse change-of-basis matrix as `Uᴴ`
(`OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose`) and then applies the general
change-of-basis similarity for `LinearMap.toMatrix`
(`basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`). -/
theorem toMatrixOrthonormal_change_orthonormalBasis (v w : OrthonormalBasis ι 𝕜 E)
    (A : E →ₗ[𝕜] E) :
    toMatrixOrthonormal w A
      = w.toBasis.toMatrix ⇑v * toMatrixOrthonormal v A * (w.toBasis.toMatrix ⇑v)ᴴ := by
  rw [w.toMatrix_orthonormalBasis_conjTranspose v]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    w.toBasis v.toBasis w.toBasis v.toBasis A).symm

end LinearMap
