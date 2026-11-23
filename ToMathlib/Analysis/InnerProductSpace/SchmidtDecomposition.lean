/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Matricization
public import ToMathlib.Analysis.InnerProductSpace.Orthonormal
public import ToMathlib.Analysis.InnerProductSpace.SingularValues
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Schmidt decomposition of a bipartite tensor

Every vector `Ψ : E ⊗[𝕜] F` in a tensor product of finite-dimensional inner product spaces
admits a **Schmidt decomposition**

  `Ψ = ∑ i, σᵢ • eᵢ ⊗ₜ fᵢ`,

where the `σᵢ > 0` are the *nonzero* singular values (the **Schmidt coefficients**) of the
matricized coefficient operator `M = matricize b Ψ : F →L[𝕜] E`, and the `eᵢ` (in `E`) and
`fᵢ` (in `F`) form genuine orthonormal families (the **Schmidt bases**). The sum runs over
`Fin (finrank 𝕜 (range M))`, i.e. exactly the number of nonzero Schmidt coefficients (the
Schmidt number). Moreover `∑ i, σᵢ² = ‖Ψ‖²`.

This is the mathematical core of Nielsen–Chuang's Theorem 2.7. The construction is the singular
value decomposition of `M`: `eᵢ` are the left singular vectors (`M.svdLeft`), `fᵢ` are the
`b`-conjugates of the right singular vectors, and `σᵢ` the singular values. Reindexing to the
support turns the SVD's "orthonormal on the support, junk off it" left singular vectors into a
genuinely orthonormal family with strictly positive coefficients, matching the textbook statement
in which the Schmidt bases are honest orthonormal sets.

## Main results

* `TensorProduct.orthonormal_conjBasis` — the `b`-conjugate `v ↦ ∑ k, ⟪v, b k⟫ • b k` of an
  orthonormal family is orthonormal (it is an antiunitary w.r.t. the basis `b`).
* `TensorProduct.matricize_eq_sum_singularValues_smul_svdLeft_tmul` — the full SVD reconstruction
  `Ψ = ∑ i, σᵢ • (svdLeft i) ⊗ₜ (conjugate of svdRight i)` over `Fin (finrank 𝕜 F)`.
* `TensorProduct.exists_orthonormal_schmidt` — the Schmidt decomposition: existence of positive
  coefficients, orthonormal Schmidt bases, `∑ σᵢ² = ‖Ψ‖²`, and `Ψ = ∑ σᵢ • eᵢ ⊗ₜ fᵢ`.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Module

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **The `b`-conjugate of an orthonormal family is orthonormal.** For an orthonormal basis
`b` of `F` and an orthonormal family `w`, the family `i ↦ ∑ k, ⟪w i, b k⟫ • b k` (the
componentwise conjugate of `w` in the basis `b`) is orthonormal. Indeed
`⟪∑ₖ⟪wᵢ,bₖ⟫bₖ, ∑ₗ⟪wⱼ,bₗ⟫bₗ⟫ = ⟪wⱼ, wᵢ⟫` (an antiunitary reverses the inner product), which is
`δᵢⱼ` by orthonormality of `w`. This is the abstract-space analogue of `EuclideanSpace.conjVec`,
absorbing the antilinearity of `inner` in the SVD reconstruction below. -/
theorem orthonormal_conjBasis (b : OrthonormalBasis ι 𝕜 F) {ι' : Type*} {w : ι' → F}
    (hw : Orthonormal 𝕜 w) :
    Orthonormal 𝕜 (fun i => ∑ k, inner 𝕜 (w i) (b k) • b k) := by
  classical
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  have hexp : (inner 𝕜 (∑ k, inner 𝕜 (w i) (b k) • b k) (∑ l, inner 𝕜 (w j) (b l) • b l) : 𝕜)
      = inner 𝕜 (w j) (w i) := by
    simp_rw [sum_inner, inner_smul_left, inner_sum, inner_smul_right, b.inner_eq_ite,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, inner_conj_symm]
    rw [← b.sum_inner_mul_inner (w j) (w i)]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hexp, hw j i]
  exact if_congr eq_comm rfl rfl

/-- **SVD reconstruction of a matricized tensor.** Writing `M := matricize b Ψ : F →L[𝕜] E`,
the bipartite vector `Ψ` reconstructs from the singular value decomposition of `M` as

  `Ψ = ∑ i, σᵢ • (M.svdLeft i) ⊗ₜ (∑ k, ⟪M.svdRight i, b k⟫ • b k)`,

summed over `Fin (finrank 𝕜 F)`. The left factors are the left singular vectors; the right
factors are the `b`-conjugates of the right singular vectors (the conjugation absorbs the
antilinearity of `inner` in `matricize`). Proof: expand `Ψ = ∑ₖ M(bₖ) ⊗ₜ bₖ`
(`matricize_symm_apply`), rewrite each `M(bₖ)` by `svd_apply`, swap the sums, and collect the
`bₖ` under the tensor's right slot. -/
theorem matricize_eq_sum_singularValues_smul_svdLeft_tmul
    (b : OrthonormalBasis ι 𝕜 F) (Ψ : E ⊗[𝕜] F) :
    Ψ = ∑ i : Fin (finrank 𝕜 F),
      ((matricize b Ψ).singularValues i.val : 𝕜) • (matricize b Ψ).svdLeft i ⊗ₜ[𝕜]
        (∑ k, inner 𝕜 ((matricize b Ψ).svdRight i) (b k) • b k) := by
  set M := matricize b Ψ with hM
  have hΨ : Ψ = ∑ k, M (b k) ⊗ₜ[𝕜] b k := by
    rw [hM, ← matricize_symm_apply b (matricize b Ψ), (matricize b).symm_apply_apply]
  rw [hΨ]
  simp_rw [M.svd_apply, TensorProduct.sum_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.tmul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]

/-- **Schmidt decomposition of a bipartite tensor (Nielsen–Chuang Theorem 2.7, abstract form).**
Every `Ψ : E ⊗[𝕜] F` decomposes as `Ψ = ∑ i, σᵢ • eᵢ ⊗ₜ fᵢ` for strictly positive Schmidt
coefficients `σᵢ`, orthonormal Schmidt bases `e` (in `E`) and `f` (in `F`), with
`∑ i, σᵢ² = ‖Ψ‖²`. The number of terms `n` is the Schmidt number (the number of nonzero
singular values of the matricized coefficient operator). -/
theorem exists_orthonormal_schmidt (Ψ : E ⊗[𝕜] F) :
    ∃ (n : ℕ) (σ : Fin n → ℝ) (e : Fin n → E) (f : Fin n → F),
      (∀ i, 0 < σ i) ∧ Orthonormal 𝕜 e ∧ Orthonormal 𝕜 f ∧
      (∑ i, σ i ^ 2 = ‖Ψ‖ ^ 2) ∧ Ψ = ∑ i, (σ i : 𝕜) • e i ⊗ₜ[𝕜] f i := by
  classical
  set b := stdOrthonormalBasis 𝕜 F with hb
  set T := (matricize b Ψ).toLinearMap with hT
  -- `r` = Schmidt number = rank of the coefficient operator.
  set r := finrank 𝕜 (LinearMap.range T) with hr
  have hrN : r ≤ finrank 𝕜 F := T.finrank_range_le
  have hlt : ∀ j : Fin r, (Fin.castLE hrN j).val < r := fun j => j.isLt
  -- SVD reconstruction of `Ψ`, at LinearMap-level projections (defeq to the CLM ones).
  have hfull : Ψ = ∑ i : Fin (finrank 𝕜 F),
      (T.singularValues i.val : 𝕜) • T.svdLeft i ⊗ₜ[𝕜]
        (∑ k, inner 𝕜 (T.svdRight i) (b k) • b k) :=
    matricize_eq_sum_singularValues_smul_svdLeft_tmul b Ψ
  -- σᵢ > 0 ⇔ i.val < r.
  have hpos : ∀ i : Fin (finrank 𝕜 F), 0 < T.singularValues i.val ↔ i.val < r := fun i =>
    T.singularValues_pos_iff_lt_finrank_range
  -- σᵢ = 0 above the rank, so the SVD sum collapses to the support `Fin r`.
  have hsv0 : ∀ i : Fin (finrank 𝕜 F), r ≤ i.val → T.singularValues i.val = 0 := by
    intro i hi
    by_contra h
    exact absurd ((hpos i).1 (lt_of_le_of_ne (T.singularValues_nonneg i.val) (Ne.symm h)))
      (not_lt.2 hi)
  -- prefix-support reduction: a family vanishing above `r` sums over `Fin r` via `castLE`.
  have hreduce : ∀ (p : Fin (finrank 𝕜 F) → E ⊗[𝕜] F), (∀ i, r ≤ i.val → p i = 0) →
      ∑ i, p i = ∑ j : Fin r, p (Fin.castLE hrN j) := by
    intro p hp
    have hmap : ∑ j : Fin r, p (Fin.castLE hrN j)
        = ∑ i ∈ Finset.univ.map ⟨Fin.castLE hrN, Fin.castLE_injective hrN⟩, p i :=
      (Finset.sum_map Finset.univ ⟨Fin.castLE hrN, Fin.castLE_injective hrN⟩ p).symm
    rw [hmap]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    refine hp i ?_
    by_contra hltc
    rw [not_le] at hltc
    exact hi (Finset.mem_map.2 ⟨⟨i.val, hltc⟩, Finset.mem_univ _, by simp⟩)
  -- The reduced Schmidt decomposition.
  have hdecomp : Ψ = ∑ j : Fin r, (T.singularValues (Fin.castLE hrN j).val : 𝕜) •
      T.svdLeft (Fin.castLE hrN j) ⊗ₜ[𝕜]
        (∑ k, inner 𝕜 (T.svdRight (Fin.castLE hrN j)) (b k) • b k) := by
    rw [hfull]
    exact hreduce _ fun i hi => by simp [hsv0 i hi]
  -- Orthonormality of the reduced right Schmidt basis (conjugate family on the support).
  have hfo : Orthonormal 𝕜 (fun j : Fin r =>
      ∑ k, inner 𝕜 (T.svdRight (Fin.castLE hrN j)) (b k) • b k) :=
    (orthonormal_conjBasis b T.svdRight.orthonormal).comp _ (Fin.castLE_injective hrN)
  -- Orthonormality of the reduced left Schmidt basis (left singular vectors on the support).
  have heo : Orthonormal 𝕜 (fun j : Fin r => T.svdLeft (Fin.castLE hrN j)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [T.inner_svdLeft_svdLeft_full]
    have hne : T.singularValues (Fin.castLE hrN i).val ≠ 0 := ne_of_gt ((hpos _).2 (hlt i))
    have hiff : (Fin.castLE hrN i = Fin.castLE hrN j) ↔ (i = j) :=
      (Fin.castLE_injective hrN).eq_iff
    exact if_congr ((and_iff_left hne).trans hiff) rfl rfl
  -- Orthonormality of the diagonal tensor family `eⱼ ⊗ fⱼ`.
  have htmul : Orthonormal 𝕜 (fun j : Fin r => T.svdLeft (Fin.castLE hrN j) ⊗ₜ[𝕜]
      (∑ k, inner 𝕜 (T.svdRight (Fin.castLE hrN j)) (b k) • b k)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [TensorProduct.inner_tmul, orthonormal_iff_ite.mp heo, orthonormal_iff_ite.mp hfo]
    by_cases h : i = j <;> simp [h]
  refine ⟨r, fun j => T.singularValues (Fin.castLE hrN j).val,
    fun j => T.svdLeft (Fin.castLE hrN j),
    fun j => ∑ k, inner 𝕜 (T.svdRight (Fin.castLE hrN j)) (b k) • b k,
    fun j => (hpos _).2 (hlt j), heo, hfo, ?_, hdecomp⟩
  -- ∑ σⱼ² = ‖Ψ‖² from the decomposition and orthonormality of `eⱼ ⊗ fⱼ`.
  conv_rhs => rw [hdecomp]
  rw [htmul.norm_sum_smul_sq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.norm_ofReal, abs_of_pos ((hpos _).2 (hlt j))]

end TensorProduct
