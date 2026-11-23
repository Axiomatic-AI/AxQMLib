/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Spectrum
public import ToMathlib.Analysis.InnerProductSpace.Positive

/-!
# Weyl's monotonicity theorem for eigenvalues of symmetric operators

For self-adjoint (symmetric) operators on a finite-dimensional inner product space, the sorted
eigenvalue function `LinearMap.IsSymmetric.eigenvalues` (decreasing, indexed by `Fin n`) is
monotone with respect to the quadratic-form order: if `A ≤ B` in the sense that
`re ⟪A x, x⟫ ≤ re ⟪B x, x⟫` for all `x`, then `λᵢ(A) ≤ λᵢ(B)` for every index `i`, where the
eigenvalues are paired in the common sorted order.

This is **Weyl's monotonicity theorem**, the special case of the Courant–Fischer min–max
principle needed for eigenvalue perturbation. The proof is the standard dimension-counting
argument: the top-`(i+1)` eigenspace of `A` (dimension `i+1`) and the bottom-`(n-i)` eigenspace
of `B` (dimension `n-i`) have dimensions summing to `n+1 > n`, hence intersect in a nonzero
vector `x`; the Rayleigh quotient of `A` on `x` is `≥ λᵢ(A)`, that of `B` is `≤ λᵢ(B)`, and the
order hypothesis chains them.

## Main results

* `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum`: the Rayleigh decomposition
  `re ⟪T x, x⟫ = ∑ⱼ λⱼ · ‖⟪bⱼ, x⟫‖²` in an orthonormal eigenbasis `b`.
* `LinearMap.IsSymmetric.eigenvalues_mono`: Weyl's monotonicity theorem in quadratic-form order.
* `LinearMap.IsSymmetric.eigenvalues_mono_of_sub_isPositive`: the corollary phrased via
  `(B - A).IsPositive` (the operator `B - A` is positive semidefinite).

These are the operator-analysis input to the eigenvalue/trace-norm bound `∑ᵢ|λᵢ(A) − λᵢ(B)| ≤
‖A − B‖₁` (Mirsky's inequality), itself the spectral core of Fannes' inequality
(Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 11.6, eq. (11.46)).
-/

@[expose] public section

open RCLike

namespace OrthonormalBasis

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- If `x` lies in the span of the sub-family `{b j | p j}` of an orthonormal basis `b`, then the
coordinate `⟪b k, x⟫` of `x` along any basis vector `b k` whose index fails `p` vanishes. This is
the coordinate form of "`x` is orthogonal to the complementary eigenspace". -/
theorem inner_eq_zero_of_mem_span_subtype {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    {p : ι → Prop} {x : E} {k : ι}
    (hx : x ∈ Submodule.span 𝕜 (Set.range fun j : {j // p j} => b j.1)) (hk : ¬ p k) :
    inner 𝕜 (b k) x = 0 := by
  classical
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hkj : k ≠ (j : ι) := by rintro rfl; exact hk j.2
  rw [inner_smul_right, b.orthonormal.2 hkj, mul_zero]

end OrthonormalBasis

namespace LinearMap.IsSymmetric

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} {n : ℕ}

/-- **Rayleigh decomposition**: in the orthonormal eigenbasis of a symmetric operator `T`, the
real Rayleigh quantity `re ⟪T x, x⟫` is the eigenvalue-weighted sum of squared coordinate norms,
`∑ⱼ λⱼ · ‖⟪bⱼ, x⟫‖²`. -/
theorem re_inner_apply_self_eq_sum (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (x : E) :
    re (inner 𝕜 (T x) x) =
      ∑ j, hT.eigenvalues hn j * ‖inner 𝕜 (hT.eigenvectorBasis hn j) x‖ ^ 2 := by
  have key : inner 𝕜 (T x) x =
      ((∑ j, hT.eigenvalues hn j * ‖inner 𝕜 (hT.eigenvectorBasis hn j) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [hT.spectral_sum_apply hn x, sum_inner, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
      RCLike.conj_mul]
    push_cast
    ring
  rw [key, RCLike.ofReal_re]

/-- **Rayleigh lower bound on a top eigenspace.** If every coordinate of `x` whose eigenvalue is
`< c` vanishes, then `c ‖x‖² ≤ re ⟪T x, x⟫`. Applied with `c = λᵢ(T)` and `x` in the span of the
top `i+1` eigenvectors, this lower-bounds the Rayleigh quotient by `λᵢ`. -/
theorem le_re_inner_of_coord_vanish (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {x : E}
    {c : ℝ} (hx : ∀ j, hT.eigenvalues hn j < c → inner 𝕜 (hT.eigenvectorBasis hn j) x = 0) :
    c * ‖x‖ ^ 2 ≤ re (inner 𝕜 (T x) x) := by
  rw [hT.re_inner_apply_self_eq_sum hn x, ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : hT.eigenvalues hn j < c
  · rw [hx j h]; simp
  · exact mul_le_mul_of_nonneg_right (not_lt.mp h) (sq_nonneg _)

/-- **Rayleigh upper bound on a bottom eigenspace.** If every coordinate of `x` whose eigenvalue
is `> c` vanishes, then `re ⟪T x, x⟫ ≤ c ‖x‖²`. Applied with `c = λᵢ(T)` and `x` in the span of
the bottom `n - i` eigenvectors, this upper-bounds the Rayleigh quotient by `λᵢ`. -/
theorem re_inner_le_of_coord_vanish (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {x : E}
    {c : ℝ} (hx : ∀ j, c < hT.eigenvalues hn j → inner 𝕜 (hT.eigenvectorBasis hn j) x = 0) :
    re (inner 𝕜 (T x) x) ≤ c * ‖x‖ ^ 2 := by
  rw [hT.re_inner_apply_self_eq_sum hn x, ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : c < hT.eigenvalues hn j
  · rw [hx j h]; simp
  · exact mul_le_mul_of_nonneg_right (not_lt.mp h) (sq_nonneg _)

/-- **Weyl's monotonicity theorem** (quadratic-form order). For symmetric operators `A, B` on a
finite-dimensional inner product space with `re ⟪A x, x⟫ ≤ re ⟪B x, x⟫` for all `x`, the sorted
eigenvalues (decreasing, paired by index) satisfy `λᵢ(A) ≤ λᵢ(B)` for every `i`.

Proof: the span `U` of the top `i+1` eigenvectors of `A` has dimension `i+1`, the span `W` of the
bottom `n-i` eigenvectors of `B` has dimension `n-i`, so `dim U + dim W = n+1 > n` forces a
nonzero `x ∈ U ⊓ W`. On `U`, `λᵢ(A) ‖x‖² ≤ re ⟪A x, x⟫`; on `W`, `re ⟪B x, x⟫ ≤ λᵢ(B) ‖x‖²`; the
hypothesis chains these, and `‖x‖² > 0` cancels. -/
theorem eigenvalues_mono {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hle : ∀ x, re (inner 𝕜 (A x) x) ≤ re (inner 𝕜 (B x) x)) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : hA.eigenvalues hn i ≤ hB.eigenvalues hn i := by
  set U := Submodule.span 𝕜 (Set.range fun j : {j : Fin n // j ≤ i} => hA.eigenvectorBasis hn j.1)
    with hU
  set W := Submodule.span 𝕜 (Set.range fun j : {j : Fin n // i ≤ j} => hB.eigenvectorBasis hn j.1)
    with hW
  -- The two eigenspaces have dimensions `i+1` and `n-i` respectively.
  have hUfr : Module.finrank 𝕜 U = Fintype.card {j : Fin n // j ≤ i} :=
    finrank_span_eq_card
      ((hA.eigenvectorBasis hn).orthonormal.comp _ Subtype.val_injective).linearIndependent
  have hWfr : Module.finrank 𝕜 W = Fintype.card {j : Fin n // i ≤ j} :=
    finrank_span_eq_card
      ((hB.eigenvectorBasis hn).orthonormal.comp _ Subtype.val_injective).linearIndependent
  -- Their dimensions sum to `n + 1`.
  have hcard : Fintype.card {j : Fin n // j ≤ i} + Fintype.card {j : Fin n // i ≤ j} = n + 1 := by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← Finset.card_union_add_card_inter]
    have hu : Finset.univ.filter (· ≤ i) ∪ Finset.univ.filter (i ≤ ·)
        = (Finset.univ : Finset (Fin n)) := by
      rw [← Finset.filter_or]
      exact Finset.filter_true_of_mem fun x _ => le_total x i
    have hin : Finset.univ.filter (· ≤ i) ∩ Finset.univ.filter (i ≤ ·) = {i} := by
      rw [← Finset.filter_and]
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => h ▸ ⟨le_refl _, le_refl _⟩⟩
    rw [hu, hin, Finset.card_univ, Fintype.card_fin, Finset.card_singleton]
  -- Dimension counting: `U` and `W` cannot be disjoint.
  have hne : U ⊓ W ≠ ⊥ := by
    intro hbot
    have hle2 := Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot)
    rw [hUfr, hWfr, hcard, hn] at hle2
    omega
  obtain ⟨x, hxUW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hxUW
  obtain ⟨hxU, hxW⟩ := hxUW
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxnorm : 0 < ‖x‖ ^ 2 := by positivity
  -- On `U`, the Rayleigh quotient of `A` is at least `λᵢ(A)`.
  have hlow : hA.eigenvalues hn i * ‖x‖ ^ 2 ≤ re (inner 𝕜 (A x) x) := by
    refine hA.le_re_inner_of_coord_vanish hn fun j hj => ?_
    refine (hA.eigenvectorBasis hn).inner_eq_zero_of_mem_span_subtype hxU fun hji => ?_
    exact absurd (hA.eigenvalues_antitone hn hji) (not_le.mpr hj)
  -- On `W`, the Rayleigh quotient of `B` is at most `λᵢ(B)`.
  have hupp : re (inner 𝕜 (B x) x) ≤ hB.eigenvalues hn i * ‖x‖ ^ 2 := by
    refine hB.re_inner_le_of_coord_vanish hn fun j hj => ?_
    refine (hB.eigenvectorBasis hn).inner_eq_zero_of_mem_span_subtype hxW fun hij => ?_
    exact absurd (hB.eigenvalues_antitone hn hij) (not_le.mpr hj)
  have hchain : hA.eigenvalues hn i * ‖x‖ ^ 2 ≤ hB.eigenvalues hn i * ‖x‖ ^ 2 :=
    hlow.trans ((hle x).trans hupp)
  exact le_of_mul_le_mul_right hchain hxnorm

/-- **Weyl's monotonicity theorem** (positivity form). If `A, B` are symmetric and `B - A` is a
positive semidefinite operator, then `λᵢ(A) ≤ λᵢ(B)` for every index `i` (sorted eigenvalues,
paired by index). -/
theorem eigenvalues_mono_of_sub_isPositive {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (hP : (B - A).IsPositive) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hA.eigenvalues hn i ≤ hB.eigenvalues hn i := by
  refine hA.eigenvalues_mono hB (fun x => ?_) hn i
  have hnn := hP.re_inner_nonneg_left x
  rw [LinearMap.sub_apply, inner_sub_left, map_sub] at hnn
  linarith

end LinearMap.IsSymmetric
