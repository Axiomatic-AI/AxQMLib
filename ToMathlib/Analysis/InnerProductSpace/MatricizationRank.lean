/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Matricization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank bounds: sub/triangle inequalities, and the rank of matricized/diagonalised operators

Six finite-dimensional rank facts, used to compute the Schmidt number of a bipartite pure state.
Three **bound** it: by the number of terms in a product decomposition (Nielsen–Chuang, Problem
2.2(2)), and — via the rank triangle inequality — by the Schmidt numbers of a superposition's
summands (Problem 2.2(3)). Two **characterise simplicity**: a matricized elementary tensor is
rank `≤ 1`, and conversely a rank-`≤ 1` matricization comes from an elementary tensor (the
Schmidt-number-`1` ⇔ product-state core, Exercise 2.78). One **reads a rank off a diagonalisation**:
the rank of a spectral sum `∑ᵢ cᵢ |vᵢ⟩⟨vᵢ|` over an orthonormal family is the number of non-zero
coefficients (used for the rank of a reduced density operator).

## Main results

* `LinearMap.finrank_range_sum_le` — **subadditivity of rank over a finite sum**: the rank
  (`finrank` of the range) of a finite sum `∑ i ∈ s, f i` of linear maps into a
  finite-dimensional space is at most the sum of the ranks of the summands. This is the
  `finrank`-valued analogue of `LinearMap.rank_finset_sum_le` (which is `Cardinal`-valued).
* `LinearMap.finrank_range_add_le` — **binary subadditivity of rank**: `finrank (range (f + g))
  ≤ finrank (range f) + finrank (range g)`. The binary form of `finrank_range_sum_le`; the
  `finrank`-valued analogue of `LinearMap.rank_add_le`.
* `LinearMap.finrank_range_le_finrank_range_add_add` — the **rank triangle inequality**:
  `finrank (range f) ≤ finrank (range (f + g)) + finrank (range g)`. Applied with the two
  summands exchanged it yields the reverse-triangle bound `|rank f − rank g| ≤ rank (f + g)`.
* `TensorProduct.finrank_range_matricize_tmul_le_one` — the matricization
  `matricize b (x ⊗ₜ y)` of an elementary tensor is a **rank-`≤ 1` operator**: its range is
  contained in the line `𝕜 ∙ x` (each column is a scalar multiple of `x`), so its rank is
  at most one.
* `TensorProduct.exists_tmul_of_finrank_range_matricize_le_one` — the **converse**: a tensor
  whose matricization has rank `≤ 1` is an elementary tensor `x ⊗ₜ y`. Together the two say a
  bipartite tensor is simple iff its matricization is rank `≤ 1`.
* `InnerProductSpace.finrank_range_sum_smul_rankOne_self` — the rank of a spectral sum
  `∑ᵢ cᵢ |vᵢ⟩⟨vᵢ|` of rank-one self-projectors over an orthonormal family, with `cᵢ ≠ 0`, is the
  number of terms. Reads the rank off a diagonalised (reduced) density operator.
-/

open scoped InnerProductSpace TensorProduct

@[expose] public section

namespace LinearMap

variable {K : Type*} {V V' : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

/-- **Subadditivity of rank over a finite sum**: the rank (`finrank` of the range) of a
finite sum `∑ i ∈ s, f i` of linear maps into a finite-dimensional space is at most the sum
of the ranks of the summands. The `finrank`-valued form of `LinearMap.rank_finset_sum_le`. -/
theorem finrank_range_sum_le {ι : Type*} (s : Finset ι) (f : ι → V →ₗ[K] V') :
    Module.finrank K ↥(LinearMap.range (∑ i ∈ s, f i))
      ≤ ∑ i ∈ s, Module.finrank K ↥(LinearMap.range (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, LinearMap.range_zero, finrank_bot]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans ?_
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

/-- **Binary subadditivity of rank**: the rank (`finrank` of the range) of a sum of two
linear maps into a finite-dimensional space is at most the sum of their ranks. The binary
form of `LinearMap.finrank_range_sum_le`; the `finrank`-valued analogue of the two-argument
`LinearMap.rank_add_le`. -/
theorem finrank_range_add_le (f g : V →ₗ[K] V') :
    Module.finrank K ↥(LinearMap.range (f + g))
      ≤ Module.finrank K ↥(LinearMap.range f) + Module.finrank K ↥(LinearMap.range g) :=
  (Submodule.finrank_mono (LinearMap.range_add_le f g)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- **Rank triangle inequality** (one side): the rank of `f` is bounded above by the rank of
the sum `f + g` plus the rank of `g`, because `f = (f + g) + (-g)` and rank is subadditive
(`finrank_range_add_le`) and negation-invariant (`LinearMap.range_neg`). Applying this with the
two summands exchanged yields `|rank f − rank g| ≤ rank (f + g)`, the reverse-triangle bound
that pins a rank below by the rank of a perturbation of it. -/
theorem finrank_range_le_finrank_range_add_add (f g : V →ₗ[K] V') :
    Module.finrank K ↥(LinearMap.range f)
      ≤ Module.finrank K ↥(LinearMap.range (f + g))
          + Module.finrank K ↥(LinearMap.range g) :=
  calc Module.finrank K ↥(LinearMap.range f)
      = Module.finrank K ↥(LinearMap.range ((f + g) + -g)) := by rw [add_neg_cancel_right]
    _ ≤ Module.finrank K ↥(LinearMap.range (f + g))
          + Module.finrank K ↥(LinearMap.range (-g)) := finrank_range_add_le _ _
    _ = Module.finrank K ↥(LinearMap.range (f + g))
          + Module.finrank K ↥(LinearMap.range g) := by rw [LinearMap.range_neg]

end LinearMap

namespace TensorProduct

variable {𝕜 : Type*} {E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι]

/-- The matricization `matricize b (x ⊗ₜ y)` of an elementary tensor is a **rank-`≤ 1`
operator**: every value `matricize b (x ⊗ₜ y) φ = ∑ k, ⟪b k, φ⟫ • ⟪b k, y⟫ • x` is a scalar
multiple of `x`, so its range lies in the line `𝕜 ∙ x` and its rank is at most one. -/
theorem finrank_range_matricize_tmul_le_one (b : OrthonormalBasis ι 𝕜 F) (x : E) (y : F) :
    Module.finrank 𝕜 ↥(LinearMap.range (matricize b (x ⊗ₜ[𝕜] y)).toLinearMap) ≤ 1 := by
  have hle : Module.finrank 𝕜 ↥(𝕜 ∙ x) ≤ 1 := by
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      rw [Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      norm_num
    · simp [finrank_span_singleton hx]
  refine (Submodule.finrank_mono ?_).trans hle
  intro w hw
  obtain ⟨z, rfl⟩ := hw
  rw [ContinuousLinearMap.coe_coe, matricize_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.restrictRight_tmul, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

/-- **Converse of `finrank_range_matricize_tmul_le_one`**: a bipartite tensor whose
matricization is a **rank-`≤ 1` operator is an elementary tensor**. If the range of
`matricize b Ψ` is at most one-dimensional it is a line `𝕜 ∙ x` (`finrank_le_one_iff_isPrincipal`),
so each column `matricize b Ψ (b k) = cₖ • x` is a multiple of `x`; reconstructing `Ψ` from its
columns (`matricize_symm_apply`) then factors `x` out of every term,
`Ψ = ∑ k, (cₖ • x) ⊗ₜ b k = x ⊗ₜ (∑ k, cₖ • b k)`. Together with the forward bound this makes
"`Ψ` is a simple tensor" equivalent to "`matricize b Ψ` has rank `≤ 1`" — the linear-algebra core
of the Schmidt-number-`1` characterisation of product states (Nielsen–Chuang, Exercise 2.78). -/
theorem exists_tmul_of_finrank_range_matricize_le_one [FiniteDimensional 𝕜 E]
    (Ψ : E ⊗[𝕜] F) (b : OrthonormalBasis ι 𝕜 F)
    (h : Module.finrank 𝕜 ↥(LinearMap.range (matricize b Ψ).toLinearMap) ≤ 1) :
    ∃ (x : E) (y : F), Ψ = x ⊗ₜ[𝕜] y := by
  classical
  have hprin : (LinearMap.range (matricize b Ψ).toLinearMap).IsPrincipal :=
    (Submodule.finrank_le_one_iff_isPrincipal _).mp h
  obtain ⟨x, hx⟩ := hprin.principal
  have hmem : ∀ k, (matricize b Ψ) (b k) ∈ Submodule.span 𝕜 {x} := by
    intro k; rw [← hx]; exact LinearMap.mem_range_self _ (b k)
  choose c hc using fun k => Submodule.mem_span_singleton.mp (hmem k)
  refine ⟨x, ∑ k, c k • b k, ?_⟩
  have hsymm : Ψ = ∑ k : ι, (matricize b Ψ) (b k) ⊗ₜ[𝕜] b k := by
    conv_lhs => rw [← (matricize b).symm_apply_apply Ψ]
    rw [matricize_symm_apply]
  rw [hsymm, tmul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← hc k, smul_tmul]

end TensorProduct

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The **rank of a spectral sum of rank-one self-projectors** `∑ᵢ cᵢ |vᵢ⟩⟨vᵢ|` over an
orthonormal family `v : Fin n → E` with all coefficients `cᵢ ≠ 0` is exactly `n`. The operator
has the `vᵢ` as eigenvectors (eigenvalue `cᵢ`), so its range is the `n`-dimensional span of the
orthonormal family: each `vⱼ = P (cⱼ⁻¹ • vⱼ)` lies in the range, and every value is a combination
of the `vᵢ`. Used to read the Schmidt number off the diagonalised reduced density operator
`ρ = ∑ᵢ λᵢ² |iᴬ⟩⟨iᴬ|` (Nielsen–Chuang §2.5). -/
theorem finrank_range_sum_smul_rankOne_self {n : ℕ} (v : Fin n → E) (c : Fin n → 𝕜)
    (hv : Orthonormal 𝕜 v) (hc : ∀ i, c i ≠ 0) :
    Module.finrank 𝕜 (LinearMap.range
      (∑ i, c i • (InnerProductSpace.rankOne 𝕜 (v i) (v i)).toLinearMap)) = n := by
  classical
  have hrange : LinearMap.range
      (∑ i, c i • (InnerProductSpace.rankOne 𝕜 (v i) (v i)).toLinearMap)
      = Submodule.span 𝕜 (Set.range v) := by
    apply le_antisymm
    · rw [LinearMap.range_le_iff_comap, eq_top_iff]
      intro x _
      rw [Submodule.mem_comap, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
        InnerProductSpace.rankOne_apply, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨(c j)⁻¹ • v j, ?_⟩
      rw [LinearMap.sum_apply, Finset.sum_eq_single j]
      · simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
          InnerProductSpace.rankOne_apply, inner_smul_right, orthonormal_iff_ite.mp hv, smul_smul,
          ite_true, mul_one]
        rw [mul_inv_cancel₀ (hc j), one_smul]
      · intro i _ hij
        simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
          InnerProductSpace.rankOne_apply, inner_smul_right, orthonormal_iff_ite.mp hv,
          ite_eq_right hij, mul_zero, zero_smul, smul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
  rw [hrange, finrank_span_eq_card hv.linearIndependent, Fintype.card_fin]

end InnerProductSpace
