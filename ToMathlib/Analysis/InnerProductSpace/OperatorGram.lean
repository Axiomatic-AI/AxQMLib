/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.GramMatrix
public import ToMathlib.Analysis.InnerProductSpace.Matricization
public import ToMathlib.Analysis.InnerProductSpace.MinimalOperatorSum
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # The operation-element Gram matrix `Wⱼₖ = tr(Eⱼ† Eₖ)` and the minimal orthogonal family

This file carries out Nielsen & Chuang's **Exercise 8.10** route to Theorem 8.3 (the minimal
operator-sum representation). Given a finite family of operation elements `E : ι → (H →L[ℂ] G)`,
N&C define the matrix

  `Wⱼₖ ≡ tr(Eⱼ† Eₖ)`,

observe that `W` is Hermitian of rank at most `d²` (on a `d`-dimensional system `G = H`), and
diagonalize it — `u W u†` diagonal for some unitary `u` — to produce at most `d²` non-zero
operation elements `{Fⱼ}` for the *same* quantum operation. This file supplies the `W` matrix, its
Hermitian/rank facts, and the diagonalized family with all three of N&C's properties.

The entries `tr(Eⱼ† Eₖ)` are the **Hilbert–Schmidt inner products** of the operation elements.
Rather than equip `H →L[ℂ] G` with the HS inner product directly, `W` is defined as the ordinary
Gram matrix (`Matrix.gram`) of the **Choi vectors** `vec Eⱼ = (matricize b).symm Eⱼ ∈ G ⊗ H`, whose
inner product is the HS pairing `tr(Eⱼ† Eₖ)` by the matricization bridge
(`TensorProduct.matricize_inner_eq_trace_adjoint_comp`). This reuses the Gram-matrix API
(`Matrix.isHermitian_gram`) for free, and turns the rank bound into a statement about the ambient
space `G ⊗ H`, of dimension `dim G · dim H` (`= d²` when `G = H`). The diagonalized family is
obtained by recombining `E` with the eigenvector unitary `u` of `W`,
`Fₐ = ∑ᵢ uᵢₐ • Eᵢ`; its Gram matrix is then `u† W u`, the diagonal matrix of `W`'s eigenvalues
(the general congruence identity `Matrix.gram_smul_sum` reduces this to the matrix spectral theorem
`Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`).

## Main definitions

* `ContinuousLinearMap.krausGram` — the operation-element Gram matrix `Wⱼₖ = tr(Eⱼ† Eₖ)`.
* `ContinuousLinearMap.krausDiagonalize` — the Gram-diagonalized family `{Fⱼ}` of operation
  elements, `Fₐ = ∑ᵢ uᵢₐ • Eᵢ`.

## Main results

* `ContinuousLinearMap.krausGram_apply` — `W`'s entries are the Hilbert–Schmidt traces
  `Wⱼₖ = tr(Eⱼ† Eₖ)` (N&C's defining formula).
* `ContinuousLinearMap.krausGram_isHermitian` — `W` is Hermitian, being a Gram matrix.
* `ContinuousLinearMap.krausGram_rank_le` — `rank W ≤ dim G · dim H`, and
  `ContinuousLinearMap.krausGram_rank_le_sq` — on a `d`-dimensional system (`G = H`),
  `rank W ≤ d²`: **N&C Exercise 8.10's rank bound.** The rank step is the general Gram-matrix fact
  `Matrix.rank_gram_le` (`rank (Matrix.gram 𝕜 v) ≤ dim E`, in `GramMatrix`).
* `ContinuousLinearMap.krausGram_krausDiagonalize` — the Gram matrix of the diagonalized family is
  diagonal (the eigenvalues of `W`): **the `u W u†` diagonal step**.
* `ContinuousLinearMap.krausSumₗ_krausDiagonalize` — the diagonalized family induces the *same*
  operator-sum map as `E` (unitary freedom, N&C Theorem 8.2).
* `ContinuousLinearMap.krausDiagonalize_trace_orthogonal` — the `{Fⱼ}` are Hilbert–Schmidt
  **orthogonal**, `tr(Fⱼ† Fₖ) = 0` for `j ≠ k`.
* `ContinuousLinearMap.krausDiagonalize_card_ne_zero_le_sq` — at most `d²` of the `{Fⱼ}` are
  non-zero (with `krausDiagonalize_card_ne_zero_le` the `dim G · dim H` form, N&C Exercise 8.11):
  **completing N&C's Exercise 8.10 proof of Theorem 8.3.**
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
  {ιb ι : Type*} [Fintype ιb] [Fintype ι]

/-- **The operation-element Gram matrix** of a finite family of operation elements
`E : ι → (H →L[ℂ] G)`, with entries the Hilbert–Schmidt inner products `Wⱼₖ = tr(Eⱼ† Eₖ)` — the
matrix `W` of Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 8.10.

Defined as the Gram matrix (`Matrix.gram`) of the Choi vectors `vec Eⱼ = (matricize b).symm Eⱼ` in
`G ⊗ H`, for an orthonormal basis `b` of the input space `H`; `krausGram_apply` identifies the
entries with the operator traces `tr(Eⱼ† Eₖ)`. -/
noncomputable def krausGram (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) : Matrix ι ι ℂ :=
  Matrix.gram ℂ (fun j => (TensorProduct.matricize b).symm (E j))

omit [Fintype ι] in
/-- **The Gram matrix entries are the Hilbert–Schmidt traces** `Wⱼₖ = tr(Eⱼ† Eₖ)` — Nielsen &
Chuang's defining formula for `W` (Exercise 8.10). The Choi vectors `vec Eⱼ` have inner product
`⟪vec Eⱼ, vec Eₖ⟫ = tr(Eⱼ† Eₖ)` by the matricization bridge
(`TensorProduct.matricize_inner_eq_trace_adjoint_comp`). -/
theorem krausGram_apply [CompleteSpace H] [CompleteSpace G]
    (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) (j k : ι) :
    krausGram b E j k
      = LinearMap.trace ℂ H ((adjoint (E j)).toLinearMap ∘ₗ (E k).toLinearMap) := by
  rw [krausGram, Matrix.gram_apply, TensorProduct.matricize_inner_eq_trace_adjoint_comp b,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

omit [Fintype ι] [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- **The operation-element Gram matrix is Hermitian** (N&C Exercise 8.10): `W† = W`, since
`Wₖⱼ = tr(Eₖ† Eⱼ) = conj (tr(Eⱼ† Eₖ)) = conj Wⱼₖ`. A special case of `Matrix.isHermitian_gram`. -/
theorem krausGram_isHermitian (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    (krausGram b E).IsHermitian :=
  Matrix.isHermitian_gram ℂ _

omit [Fintype ι] in
/-- **The rank of the operation-element Gram matrix is at most `dim G · dim H`.** The Choi vectors
`vec Eⱼ` live in `G ⊗ H`, of dimension `dim G · dim H`, so the Gram matrix has rank at most that
(`Matrix.rank_gram_le`, `Module.finrank_tensorProduct`). -/
theorem krausGram_rank_le [Finite ι] (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    (krausGram b E).rank ≤ Module.finrank ℂ G * Module.finrank ℂ H := by
  rw [krausGram, ← Module.finrank_tensorProduct]
  exact Matrix.rank_gram_le _

omit [Fintype ι] in
/-- **The rank of the operation-element Gram matrix on a `d`-dimensional system is at most `d²`**
(Nielsen & Chuang, Exercise 8.10). For operation elements `E : ι → (H →L[ℂ] H)` with input and
output space both `H`, `rank W ≤ (dim H)²` — the bound that, after diagonalizing `W`, yields the
`≤ d²` operation elements of Theorem 8.3. -/
theorem krausGram_rank_le_sq [Finite ι] (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] H) :
    (krausGram b E).rank ≤ Module.finrank ℂ H ^ 2 := by
  rw [pow_two]
  exact krausGram_rank_le b E

variable [DecidableEq ι]

/-- **The Gram-diagonalized family of operation elements** `{Fₐ}` of Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 8.10. Diagonalize the Hermitian Gram matrix
`W = krausGram b E` by its eigenvector unitary `u` (`Matrix.IsHermitian.eigenvectorUnitary`, so
`u† W u` is diagonal), and define the recombined operation elements

  `Fₐ ≡ ∑ᵢ uᵢₐ • Eᵢ`.

These are N&C's "new set of operation elements `{Fⱼ}`" obtained from `u`: they induce the *same*
operator-sum map as `E` (`krausSumₗ_krausDiagonalize`), are Hilbert–Schmidt **orthogonal**
(`tr(Fₐ† F_c) = 0` for `a ≠ c`, `krausDiagonalize_trace_orthogonal`), and at most `rank W ≤ d²` of
them are non-zero (`krausDiagonalize_card_ne_zero_le`), completing the Exercise 8.10 route to
Theorem 8.3. -/
noncomputable def krausDiagonalize (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    ι → H →L[ℂ] G :=
  fun a => ∑ i, ((krausGram_isHermitian b E).eigenvectorUnitary : Matrix ι ι ℂ) i a • E i

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- **Diagonalizing `W` orthogonalizes the operation elements** (Nielsen & Chuang, Exercise 8.10).
The Gram matrix of the diagonalized family `krausDiagonalize b E` is the diagonal matrix of the
(real) eigenvalues of `W = krausGram b E`. This is the statement that `u† W u` is diagonal
(`Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`), transported to the Gram matrix of the
recombined family via the general congruence identity `Matrix.gram_smul_sum`
(`gram (fun a => ∑ᵢ uᵢₐ • vᵢ) = uᴴ * gram v * u`). -/
theorem krausGram_krausDiagonalize (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    krausGram b (krausDiagonalize b E)
      = Matrix.diagonal (RCLike.ofReal ∘ (krausGram_isHermitian b E).eigenvalues) := by
  rw [← (krausGram_isHermitian b E).conjStarAlgAut_star_eigenvectorUnitary,
    Unitary.conjStarAlgAut_star_apply]
  simp only [krausGram, krausDiagonalize, map_sum, map_smul]
  rw [Matrix.gram_smul_sum, Matrix.star_eq_conjTranspose]

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- **The diagonalized family induces the same operator-sum map** (Nielsen & Chuang, Exercise 8.10):
`krausSumₗ (krausDiagonalize b E) = krausSumₗ E`, so `{Fⱼ}` is a set of operation elements for the
*same* quantum operation `E`. Since `Fₐ = ∑ᵢ uᵢₐ • Eᵢ` with `u` unitary (hence `uᵀ` unitary,
`Matrix.transpose_mem_unitaryGroup_iff`), this is the unitary freedom in the operator-sum
representation (`ContinuousLinearMap.krausSumₗ_eq_of_unitary_smul`, N&C Theorem 8.2). -/
theorem krausSumₗ_krausDiagonalize [CompleteSpace H] [CompleteSpace G]
    (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    krausSumₗ (krausDiagonalize b E) = krausSumₗ E := by
  refine krausSumₗ_eq_of_unitary_smul
    (u := ((krausGram_isHermitian b E).eigenvectorUnitary : Matrix ι ι ℂ).transpose)
    (Matrix.transpose_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)) (fun a => ?_)
  simp only [krausDiagonalize, Matrix.transpose_apply]

/-- **The diagonalized operation elements are Hilbert–Schmidt orthogonal** (Nielsen & Chuang,
Exercise 8.10): `tr(Fₐ† F_c) = 0` for `a ≠ c`. The off-diagonal entries of their Gram matrix vanish,
since it is diagonal (`krausGram_krausDiagonalize`). -/
theorem krausDiagonalize_trace_orthogonal [CompleteSpace H] [CompleteSpace G]
    (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) {a c : ι} (hac : a ≠ c) :
    LinearMap.trace ℂ H
        ((adjoint (krausDiagonalize b E a)).toLinearMap ∘ₗ (krausDiagonalize b E c).toLinearMap)
      = 0 := by
  rw [← krausGram_apply b (krausDiagonalize b E) a c, krausGram_krausDiagonalize,
    Matrix.diagonal_apply_ne _ hac]

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- A diagonalized operation element `Fₐ` is non-zero exactly when the corresponding eigenvalue of
`W = krausGram b E` is non-zero: its squared Hilbert–Schmidt norm is `⟪vec Fₐ, vec Fₐ⟫ = λₐ`. -/
theorem krausDiagonalize_ne_zero_iff (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) (a : ι) :
    krausDiagonalize b E a ≠ 0 ↔ (krausGram_isHermitian b E).eigenvalues a ≠ 0 := by
  have hnorm : (⟪(TensorProduct.matricize b).symm (krausDiagonalize b E a),
        (TensorProduct.matricize b).symm (krausDiagonalize b E a)⟫_ℂ)
      = RCLike.ofReal ((krausGram_isHermitian b E).eigenvalues a) := by
    have hg : krausGram b (krausDiagonalize b E) a a
        = ⟪(TensorProduct.matricize b).symm (krausDiagonalize b E a),
            (TensorProduct.matricize b).symm (krausDiagonalize b E a)⟫_ℂ := by
      rw [krausGram, Matrix.gram_apply]
    rw [← hg, krausGram_krausDiagonalize, Matrix.diagonal_apply_eq, Function.comp_apply]
  refine not_congr ?_
  rw [← (TensorProduct.matricize b).symm.map_eq_zero_iff, ← inner_self_eq_zero (𝕜 := ℂ), hnorm,
    RCLike.ofReal_eq_zero]

/-- **At most `dim G · dim H` of the diagonalized operation elements are non-zero** (Nielsen &
Chuang, Exercise 8.11, the `d`-to-`d′` form). The number of non-zero `Fₐ` equals the number of
non-zero eigenvalues of `W`, which is `rank W` (`Matrix.IsHermitian.rank_eq_card_non_zero_eigs`), at
most `dim G · dim H` (`krausGram_rank_le`). -/
theorem krausDiagonalize_card_ne_zero_le (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] G) :
    Nat.card {a // krausDiagonalize b E a ≠ 0} ≤ Module.finrank ℂ G * Module.finrank ℂ H := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (krausDiagonalize_ne_zero_iff b E)),
    Nat.card_eq_fintype_card, ← (krausGram_isHermitian b E).rank_eq_card_non_zero_eigs]
  exact krausGram_rank_le b E

/-- **At most `d²` diagonalized operation elements are non-zero, on a `d`-dimensional system**
(Nielsen & Chuang, Exercise 8.10): the count of non-zero `Fₐ` is `rank W ≤ d²`. Together with
`krausSumₗ_krausDiagonalize` (same operation) and `krausDiagonalize_trace_orthogonal`
(orthogonality), this exhibits N&C's "at most `d²` non-zero operation elements `{Fⱼ}` for `E`",
proving Theorem 8.3 via the Gram-matrix route. -/
theorem krausDiagonalize_card_ne_zero_le_sq (b : OrthonormalBasis ιb ℂ H) (E : ι → H →L[ℂ] H) :
    Nat.card {a // krausDiagonalize b E a ≠ 0} ≤ Module.finrank ℂ H ^ 2 := by
  rw [pow_two]
  exact krausDiagonalize_card_ne_zero_le b E

end ContinuousLinearMap
