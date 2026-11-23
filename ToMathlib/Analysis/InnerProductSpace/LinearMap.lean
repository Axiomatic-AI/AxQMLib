/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Additional API for `reApplyInnerSelf` and `rankOne`

Extra lemmas about `ContinuousLinearMap.reApplyInnerSelf` (scaling by a real scalar, additivity
over finite sums, and its value on a rank-one self-projector) and about `InnerProductSpace.rankOne`
(sesquilinearity, absorbing scalars, a sum/difference cross-term identity, and bilinearity/
additivity over finite sums).
-/

@[expose] public section

open RCLike Real ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]

section ReApplyInnerSelf_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem ContinuousLinearMap.reApplyInnerSelf_ofReal_smul (T : E →L[𝕜] E) (x : E) (r : ℝ) :
    ((r : 𝕜) • T).reApplyInnerSelf x = r * T.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, _root_.smul_apply,
    inner_smul_left, conj_ofReal, re_ofReal_mul]

theorem ContinuousLinearMap.reApplyInnerSelf_sum {ι : Type*} (s : Finset ι)
    (T : ι → E →L[𝕜] E) (x : E) :
    (∑ i ∈ s, T i).reApplyInnerSelf x = ∑ i ∈ s, (T i).reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, _root_.sum_apply,
    sum_inner, map_sum]

end ReApplyInnerSelf_Seminormed

namespace InnerProductSpace

variable {G : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]

open ContinuousLinearMap

/-- Sesquilinearity of `rankOne` in both arguments: scalars on the left factor through linearly,
scalars on the right factor through conjugate-linearly. -/
lemma rankOne_smul_smul (s t : 𝕜) (x : E) (y : F) :
    rankOne 𝕜 (s • x) (t • y) = (s * starRingEnd 𝕜 t) • rankOne 𝕜 x y := by
  ext z
  simp [rankOne_apply, smul_smul, mul_assoc]

/-- Same scalar in both arguments:
`rankOne 𝕜 (s • x) (s • x) = (s * star s) • rankOne 𝕜 x x`. -/
lemma rankOne_smul_smul_self (s : 𝕜) (x : F) :
    rankOne 𝕜 (s • x) (s • x) = (s * starRingEnd 𝕜 s) • rankOne 𝕜 x x :=
  rankOne_smul_smul s s x x

/-- A scalar on the rank-one operator absorbs into the left (linear) factor:
`c • rankOne 𝕜 x y = rankOne 𝕜 (c • x) y`. -/
lemma smul_rankOne (c : 𝕜) (x : E) (y : F) :
    c • rankOne 𝕜 x y = rankOne 𝕜 (c • x) y := by
  ext z; simp [rankOne_apply, smul_smul]

/-- Absorbing a real square root scalar into a rank-one self-projector picks up the squared scalar.
Used to identify `rankOne 𝕜 (√r • x) (√r • x)` with `r • rankOne 𝕜 x x` for `0 ≤ r`. -/
lemma rankOne_real_sqrt_smul_self {r : ℝ} (hr : 0 ≤ r) (x : F) :
    rankOne 𝕜 ((Real.sqrt r : 𝕜) • x) ((Real.sqrt r : 𝕜) • x)
      = (r : 𝕜) • rankOne 𝕜 x x := by
  rw [rankOne_smul_smul_self, RCLike.conj_ofReal, ← RCLike.ofReal_mul, Real.mul_self_sqrt hr]

/-- **Cross-term cancellation for a normalised sum/difference pair.** The sum of the rank-one
projectors onto the two normalised combinations `(x ± y)/√2` equals the sum of the projectors onto
`x` and `y`: `|(x+y)/√2⟩⟨(x+y)/√2| + |(x−y)/√2⟩⟨(x−y)/√2| = |x⟩⟨x| + |y⟩⟨y|`, the `|x⟩⟨y|`, `|y⟩⟨x|`
cross terms cancelling between the two.  (Two orthonormal states differing only by a sign span the
same subspace as the two states they superpose.) -/
theorem rankOne_sqrtTwoInv_add_sub_self (x y : F) :
    rankOne 𝕜 ((Real.sqrt 2 : 𝕜)⁻¹ • (x + y)) ((Real.sqrt 2 : 𝕜)⁻¹ • (x + y))
      + rankOne 𝕜 ((Real.sqrt 2 : 𝕜)⁻¹ • (x - y)) ((Real.sqrt 2 : 𝕜)⁻¹ • (x - y))
      = rankOne 𝕜 x x + rankOne 𝕜 y y := by
  have hc : (Real.sqrt 2 : 𝕜)⁻¹ * (starRingEnd 𝕜) ((Real.sqrt 2 : 𝕜)⁻¹) = (1 / 2 : 𝕜) := by
    rw [map_inv₀, RCLike.conj_ofReal, ← mul_inv, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), RCLike.ofReal_ofNat]
    norm_num
  rw [rankOne_smul_smul, rankOne_smul_smul, hc]
  ext z
  simp only [_root_.add_apply, _root_.smul_apply, rankOne_apply,
    inner_add_left, inner_sub_left, smul_add, smul_sub, smul_smul]
  module

/-- **Bilinearity of `rankOne` over finite sums of smul-combinations**: distributing both
arguments of `rankOne` as linear combinations produces a double sum, with the antilinearity
in the second argument appearing as `star (d j)` on the scalar:
`rankOne 𝕜 (∑ i, c i • a i) (∑ j, d j • b j)`
  `= ∑ i, ∑ j, (c i * star (d j)) • rankOne 𝕜 (a i) (b j)`. -/
lemma rankOne_sum_smul_sum_smul {ι ι' : Type*} (s : Finset ι) (s' : Finset ι')
    (a : ι → E) (b : ι' → F) (c : ι → 𝕜) (d : ι' → 𝕜) :
    rankOne 𝕜 (∑ i ∈ s, c i • a i) (∑ j ∈ s', d j • b j) =
      ∑ i ∈ s, ∑ j ∈ s', (c i * starRingEnd 𝕜 (d j)) • rankOne 𝕜 (a i) (b j) := by
  ext z
  simp only [rankOne_apply, sum_inner, inner_smul_left,
    _root_.sum_apply, _root_.smul_apply,
    Finset.smul_sum, Finset.sum_mul, Finset.sum_smul, smul_smul]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring_nf

/-- **Bi-additivity of `rankOne` over finite sums.** The rank-one operator of two finite sums is the
double sum of the rank-one operators of the summands: `|∑ₖ uₖ⟩⟨∑ₗ vₗ| = ∑ₖ ∑ₗ |uₖ⟩⟨vₗ|`. The
coefficient-free special case of `rankOne_sum_smul_sum_smul` (both scalar families constantly
`1`). -/
lemma rankOne_sum_sum {W : Type*} [SeminormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    {ι : Type*} [Fintype ι] (u v : ι → W) :
    (rankOne 𝕜 (∑ k, u k) (∑ l, v l) : W →L[𝕜] W) = ∑ k, ∑ l, rankOne 𝕜 (u k) (v l) := by
  have h := rankOne_sum_smul_sum_smul (𝕜 := 𝕜) Finset.univ Finset.univ u v
    (fun _ => (1 : 𝕜)) (fun _ => (1 : 𝕜))
  simpa only [one_smul, starRingEnd_apply, star_one, one_mul] using h

end InnerProductSpace

namespace ContinuousLinearMap

open InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The `reApplyInnerSelf` of a rank-one self projector `|d⟩⟨d|`: the real part of
`⟪|d⟩⟨d| x, x⟫` is `‖⟪d, x⟫‖²`. -/
theorem reApplyInnerSelf_rankOne_self (d x : E) :
    (rankOne 𝕜 d d).reApplyInnerSelf x = ‖inner 𝕜 d x‖ ^ 2 := by
  rw [reApplyInnerSelf_apply, rankOne_apply, inner_smul_left, RCLike.conj_mul]
  simp

end ContinuousLinearMap
