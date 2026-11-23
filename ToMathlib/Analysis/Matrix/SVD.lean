/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import ToMathlib.Analysis.InnerProductSpace.PiL2

/-! # Singular value decomposition of a square matrix

For a square matrix `A` over an `RCLike` field, this file proves the **singular value
decomposition** in matrix form: there exist unitary matrices `U`, `V` and a diagonal matrix `D`
with non-negative real entries such that `A = U * D * V`
(`Matrix.exists_unitary_mul_diagonal_mul_unitary`). The diagonal entries of `D` are the *singular
values* of `A`.

This is Corollary 2.4 of Nielsen & Chuang, *Quantum Computation and Quantum Information*.

## Relation to `Mathlib.Analysis.InnerProductSpace.SingularValues`

That file develops the SVD for a *linear map* `T : E →ₗ[𝕜] F` in vector form
(`LinearMap.svd_apply`: `T x = ∑ᵢ σᵢ • ⟨uᵢ, x⟩ • vᵢ`), together with `LinearMap.singularValues`,
the right singular basis `LinearMap.svdRight`, and the left singular vectors `LinearMap.svdLeft`.
That API does **not** directly yield the matrix corollary here, for a specific reason: `svdLeft`
is orthonormal only on the *support* `{i | σᵢ ≠ 0}` and is junk where `σᵢ = 0`
(`LinearMap.svdLeft_eq_zero_of_singularValues_eq_zero`), so it is a partial isometry, not a full
unitary. The matrix statement `A = U * D * V` demands a genuinely unitary left factor `U`, which
requires completing the nonzero left singular vectors to an orthonormal basis — a step that API
does not perform. The proof below therefore builds `U` directly via
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, rather than routing through
`LinearMap.svd_apply`. The two developments remain compatible: the diagonal entries produced here
agree (as a multiset) with `LinearMap.singularValues (Matrix.toEuclideanLin A)`, both being the
square roots of the eigenvalues of `Aᴴ * A`.

## Implementation notes

The proof does not go through the polar decomposition (a unitary matrix polar decomposition,
N&C Theorem 2.3, is not yet in the library). Instead it applies the spectral theorem directly to
the positive semidefinite matrix `M = Aᴴ * A`. Writing `star W * M * W = diagonal μ` with `W`
unitary (`Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`) and eigenvalues `μ ≥ 0`, and
setting `σ i = √(μ i)`, the columns of `B = A * W` satisfy `Bᴴ * B = diagonal μ`, so they are
orthogonal with squared norms `μ i = σ i ^ 2`. Normalising the columns with `σ i ≠ 0` gives an
orthonormal family, which extends to an orthonormal basis
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`); the associated unitary is the left
factor `U`, and one checks `U * diagonal σ = B`, whence `A = U * diagonal σ * Wᴴ`.

## Tags

singular value decomposition, SVD, matrix
-/

@[expose] public section

open Matrix Finset RCLike Module
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Singular value decomposition** (Nielsen & Chuang, Corollary 2.4). Every square matrix `A`
over an `RCLike` field factors as `A = U * D * V`, where `U` and `V` are unitary matrices and `D`
is a diagonal matrix with non-negative real entries (the *singular values* of `A`). -/
theorem exists_unitary_mul_diagonal_mul_unitary (A : Matrix n n 𝕜) :
    ∃ (U V : Matrix n n 𝕜) (d : n → ℝ),
      U ∈ unitaryGroup n 𝕜 ∧ V ∈ unitaryGroup n 𝕜 ∧
        (∀ i, 0 ≤ d i) ∧ A = U * diagonal (RCLike.ofReal ∘ d) * V := by
  classical
  -- The Gram matrix `M = Aᴴ * A` is positive semidefinite Hermitian.
  have hMpsd : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have hMherm : (Aᴴ * A).IsHermitian := hMpsd.isHermitian
  set μ : n → ℝ := hMherm.eigenvalues with hμ
  have hμ0 : ∀ i, 0 ≤ μ i := hMpsd.eigenvalues_nonneg
  set W : Matrix n n 𝕜 := (hMherm.eigenvectorUnitary : Matrix n n 𝕜) with hW
  have hWmem : W ∈ unitaryGroup n 𝕜 := SetLike.coe_mem _
  have hWW : W * star W = 1 := mem_unitaryGroup_iff.mp hWmem
  have hWWs : star W * W = 1 := mem_unitaryGroup_iff'.mp hWmem
  -- The singular values.
  set σ : n → ℝ := fun i => Real.sqrt (μ i) with hσ
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => Real.sqrt_nonneg _
  have hσsq : ∀ i, σ i * σ i = μ i := fun i => Real.mul_self_sqrt (hμ0 i)
  have hσne : ∀ j, μ j ≠ 0 → (σ j : 𝕜) ≠ 0 := fun j hj => by
    rw [Ne, RCLike.ofReal_eq_zero]; exact fun h => hj (by rw [← hσsq j, h, mul_zero])
  -- Diagonalisation of `M`.
  have hdiag : star W * (Aᴴ * A) * W = diagonal (RCLike.ofReal ∘ μ) := by
    have h := hMherm.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa only [← hW, ← hμ] using h
  set B : Matrix n n 𝕜 := A * W with hB
  have hBB : Bᴴ * B = diagonal (RCLike.ofReal ∘ μ) := by
    rw [hB, conjTranspose_mul, ← hdiag]
    simp only [mul_assoc, Matrix.star_eq_conjTranspose]
  -- Columns of `B` as Euclidean vectors, and their pairwise inner products.
  set bcol : n → EuclideanSpace 𝕜 n := fun j => (WithLp.toLp 2 (Bᵀ j)) with hbcol
  have hbcol_of : ∀ j i, (bcol j).ofLp i = B i j := by
    intro j i; simp [hbcol, Matrix.transpose_apply]
  have hbcol_inner : ∀ j k, inner 𝕜 (bcol j) (bcol k) = (Bᴴ * B) j k :=
    fun j k => inner_matrix_col_col B B j k
  -- The normalised columns and their support.
  set w : n → EuclideanSpace 𝕜 n := fun j => ((σ j : 𝕜))⁻¹ • bcol j with hw
  set s : Set n := {j | μ j ≠ 0} with hs
  have hw_ortho : Orthonormal 𝕜 (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨k, hk⟩
    simp only [hs, Set.mem_ofPred_eq] at hj hk
    simp only [Set.domRestrict_apply, hw]
    rw [inner_smul_left, inner_smul_right, hbcol_inner, hBB, map_inv₀, RCLike.conj_ofReal]
    by_cases hjk : j = k
    · subst hjk
      have hσj := hσne j hj
      rw [ite_eq_left rfl, Matrix.diagonal_apply_eq, Function.comp_apply, ← hσsq j,
          RCLike.ofReal_mul,
        inv_mul_cancel_left₀ hσj, inv_mul_cancel₀ hσj]
    · rw [Matrix.diagonal_apply_ne _ hjk, mul_zero, mul_zero,
        ite_eq_right (fun h => hjk (congrArg Subtype.val h))]
  -- Complete the orthonormal family to an orthonormal basis.
  obtain ⟨c, hc⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace hw_ortho
  set U : Matrix n n 𝕜 := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix c.toBasis with hU
  have hUmem : U ∈ unitaryGroup n 𝕜 :=
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary c
  have hUentry : ∀ i j, U i j = (c j).ofLp i := fun _ _ => rfl
  -- `U * diagonal σ = B`.
  have hkey : U * diagonal (RCLike.ofReal ∘ σ) = B := by
    ext i j
    rw [Matrix.mul_diagonal, hUentry, Function.comp_apply]
    by_cases hj : μ j = 0
    · have hσj0 : σ j = 0 := by simp only [hσ, hj, Real.sqrt_zero]
      have hbc0 : bcol j = 0 := by
        rw [← inner_self_eq_zero (𝕜 := 𝕜), hbcol_inner, hBB]
        simp [Matrix.diagonal_apply_eq, hj]
      have hBij : B i j = 0 := by rw [← hbcol_of j i, hbc0]; simp
      rw [hBij, hσj0]; simp
    · have hjs : j ∈ s := by rw [hs, Set.mem_ofPred_eq]; exact hj
      have hσj := hσne j hj
      rw [hc j hjs, hw, PiLp.smul_apply, hbcol_of, smul_eq_mul]
      rw [mul_right_comm, inv_mul_cancel₀ hσj, one_mul]
  -- Assemble the decomposition.
  refine ⟨U, star W, σ, hUmem, ?_, hσ0, ?_⟩
  · rw [mem_unitaryGroup_iff, star_star]; exact hWWs
  · calc A = A * W * star W := by rw [mul_assoc, hWW, mul_one]
      _ = B * star W := by rw [hB]
      _ = U * diagonal (RCLike.ofReal ∘ σ) * star W := by rw [hkey]

end Matrix
