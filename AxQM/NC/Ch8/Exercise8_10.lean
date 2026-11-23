/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.OperatorGram

/-!
# Nielsen & Chuang, Exercise 8.10 (proof of Theorem 8.3 via the operation-element Gram matrix)

Prove Theorem 8.3 via W_jk=tr(E_j†E_k) Hermitian rank ≤d²; diagonalize to get ≤d² operation
elements.

## Where this is formalised

The exercise is a piece of finite-dimensional linear algebra about the operator-sum (Kraus) map
`ρ ↦ ∑ᵢ Eᵢ ρ Eᵢ†` (`ContinuousLinearMap.krausSumₗ`) of a family of operators
`E : ι → (H →L[ℂ] G)`: it builds the Gram matrix `Wⱼₖ = tr(Eⱼ† Eₖ)`, diagonalises it, and exhibits
an orthogonal family of at most `d²` non-zero operators inducing the same map. Its statements are
over `Matrix`, `ContinuousLinearMap`, `LinearMap.trace` and `Matrix.unitaryGroup`, for a *general*
space `H`. Compare `AxQM/NC/Ch8/Theorem8_3.lean`.

## The formalisation (in `ToMathlib/Analysis/InnerProductSpace/OperatorGram.lean`)

The route is distinct from `Theorem8_3`'s existing proof
(`ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank_sq`), which uses the *dual* Choi-operator
rank-one reduction; here we follow N&C's actual `W`-matrix diagonalisation.

* `ContinuousLinearMap.krausGram` — the operation-element Gram matrix `Wⱼₖ = tr(Eⱼ† Eₖ)`, with
  `krausGram_apply` (its entries are the Hilbert–Schmidt traces), `krausGram_isHermitian` (`W` is
  Hermitian), and `krausGram_rank_le` / `krausGram_rank_le_sq` (`rank W ≤ dim G · dim H`, and `≤ d²`
  on a `d`-dimensional system): **N&C's "`W` is Hermitian and of rank at most `d²`".**
* `ContinuousLinearMap.krausDiagonalize` — N&C's "new set of operation elements `{Fⱼ}`": the
  family `Fₐ = ∑ᵢ uᵢₐ • Eᵢ` obtained by recombining `E` with the eigenvector unitary `u` of `W`.
  Its properties are the exercise's conclusions:
  * `ContinuousLinearMap.krausGram_krausDiagonalize` — `u W u†` is diagonal: the Gram matrix of
    `{Fⱼ}` is the diagonal matrix of `W`'s eigenvalues.
  * `ContinuousLinearMap.krausSumₗ_krausDiagonalize` — `{Fⱼ}` are operation elements for the
    *same* quantum operation, `krausSumₗ (krausDiagonalize b E) = krausSumₗ E` (unitary freedom,
    Theorem 8.2).
  * `ContinuousLinearMap.krausDiagonalize_trace_orthogonal` — the `{Fⱼ}` are Hilbert–Schmidt
    orthogonal, `tr(Fⱼ† Fₖ) = 0` for `j ≠ k`.
  * `ContinuousLinearMap.krausDiagonalize_card_ne_zero_le_sq` — at most `d²` of the `{Fⱼ}` are
    non-zero (`krausDiagonalize_card_ne_zero_le`: the `dim G · dim H` form, N&C Exercise 8.11),
    completing the proof of Theorem 8.3.

The diagonalisation step is the matrix spectral theorem
(`Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`) applied to `krausGram_isHermitian`,
transported to the Gram matrix of the recombined family by the general Gram congruence identity
`Matrix.gram_smul_sum` (`gram (fun a => ∑ᵢ Mᵢₐ • vᵢ) = Mᴴ * gram v * M`, in
`ToMathlib/Analysis/InnerProductSpace/GramMatrix.lean`); the count uses
`Matrix.IsHermitian.rank_eq_card_non_zero_eigs`, and the same-operation step is the unitary-freedom
lemma `ContinuousLinearMap.krausSumₗ_eq_of_unitary_smul`.
-/
