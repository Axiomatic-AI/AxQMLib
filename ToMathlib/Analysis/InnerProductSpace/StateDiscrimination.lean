/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.POVM
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# A POVM that distinguishes linearly independent states with certainty

Given a finite family `v : ι → E` of **linearly independent** vectors in a finite-dimensional
inner product space, this file constructs a POVM `POVM.distinguishing 𝕜 v` on the outcome set
`Option ι` — one "informative" outcome `some i` per state, plus one "inconclusive" outcome
`none` — with the *unambiguous discrimination* property: the Born probability of outcome
`some i` vanishes on every state `v j` with `j ≠ i`, and is strictly positive on `v i`. Hence
observing `some i` guarantees the input was `v i` (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Exercise 2.64).

## Construction

The key object is the **detector vector** `POVM.detector 𝕜 v i`: the component of `v i`
orthogonal to the span of the *other* family members `{v j | j ≠ i}`, obtained by orthogonally
projecting `v i` onto that span's orthogonal complement. By construction
`⟪detector 𝕜 v i, v j⟫ = 0` for `j ≠ i`; linear independence forces
`v i ∉ span {v j | j ≠ i}`, so the detector is nonzero and
`⟪detector 𝕜 v i, v i⟫ = ‖detector 𝕜 v i‖² ≠ 0`.

The informative effects are rescaled rank-one projectors onto the detectors,
`Eᵢ = c • |detector 𝕜 v i⟩⟨detector 𝕜 v i|`, with a single scale
`c = (1 + ∑ⱼ ‖detector 𝕜 v j‖²)⁻¹` chosen small enough that `∑ᵢ Eᵢ ≤ 1`; the inconclusive
effect is `E_none = 1 - ∑ᵢ Eᵢ`, positive by that bound. Because
`⟪ψ, Eᵢ ψ⟫ = c ‖⟪detector 𝕜 v i, ψ⟫‖²`, the discrimination property is immediate from the
detector's orthogonality.

## Main definitions

* `POVM.detector` — the detector vector for outcome `i`.
* `POVM.distinguishing` — the discriminating POVM on `Option ι`.

## Main results

* `POVM.distinguishing_reApplyInnerSelf_eq_zero` / `POVM.distinguishing_reApplyInnerSelf_pos` —
  the discrimination property at the effect level.

The two general building blocks used here — `ContinuousLinearMap.reApplyInnerSelf_rankOne_self`
(the `reApplyInnerSelf` of a rank-one self projector) and `POVM.toPMF_rankOne_self` (a POVM's
Born probability on a pure state) — carry no discrimination content and live upstream, beside
their siblings in `Mathlib.Analysis.InnerProductSpace.LinearMap` and
`ToMathlib.Analysis.InnerProductSpace.POVM` respectively.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th
anniv. ed.). Cambridge University Press. §2.2.6, Exercise 2.64.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap

noncomputable section

namespace POVM

variable {ι : Type*} [Fintype ι]
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The **detector vector** for outcome `i` in the family `v`: the orthogonal projection of
`v i` onto the orthogonal complement of the span of the other members `{v j | j ≠ i}`. It is
orthogonal to every `v j` with `j ≠ i`, and (when `v` is linearly independent) nonzero. -/
def detector (v : ι → E) (i : ι) : E :=
  (Submodule.span 𝕜 (v '' {j | j ≠ i}))ᗮ.starProjection (v i)

omit [Fintype ι] in
/-- The detector `detector 𝕜 v i` is orthogonal to every other family member `v j` (`j ≠ i`). -/
theorem detector_inner_eq_zero (v : ι → E) {i j : ι} (hij : j ≠ i) :
    inner 𝕜 (detector 𝕜 v i) (v j) = 0 :=
  Submodule.inner_left_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_image_of_mem v hij))
    (Submodule.starProjection_apply_mem _ _)

omit [Fintype ι] in
/-- When `v` is linearly independent, the detector `detector 𝕜 v i` is nonzero: it vanishes iff
`v i` lies in the span of the other members, which linear independence forbids. -/
theorem detector_ne_zero {v : ι → E} (hv : LinearIndependent 𝕜 v) (i : ι) :
    detector 𝕜 v i ≠ 0 := by
  rw [detector, Ne, Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  exact hv.notMem_span_image (by simp)

omit [Fintype ι] in
/-- When `v` is linearly independent, the detector is *not* orthogonal to its own state:
`⟪detector 𝕜 v i, v i⟫ = ⟪detector 𝕜 v i, detector 𝕜 v i⟫ ≠ 0`. -/
theorem inner_detector_self_ne_zero {v : ι → E} (hv : LinearIndependent 𝕜 v) (i : ι) :
    inner 𝕜 (detector 𝕜 v i) (v i) ≠ 0 := by
  have hdecomp : detector 𝕜 v i
      = v i - (Submodule.span 𝕜 (v '' {j | j ≠ i})).starProjection (v i) := by
    rw [detector, Submodule.starProjection_orthogonal', _root_.sub_apply,
      one_apply_eq_self]
  have hmem : v i - detector 𝕜 v i ∈ Submodule.span 𝕜 (v '' {j | j ≠ i}) := by
    rw [hdecomp, sub_sub_cancel]; exact Submodule.starProjection_apply_mem _ _
  have h0 : inner 𝕜 (detector 𝕜 v i) (v i - detector 𝕜 v i) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hmem (Submodule.starProjection_apply_mem _ _)
  rw [inner_sub_right, sub_eq_zero] at h0
  rw [h0]
  exact inner_self_ne_zero.mpr (detector_ne_zero 𝕜 hv i)

/-- The scale factor `c = (1 + ∑ⱼ ‖detector 𝕜 v j‖²)⁻¹` of the informative effects, chosen so
that `∑ᵢ Eᵢ ≤ 1`. -/
def distinguishingScale (v : ι → E) : ℝ := (1 + ∑ j, ‖detector 𝕜 v j‖ ^ 2)⁻¹

theorem distinguishingScale_pos (v : ι → E) : 0 < distinguishingScale 𝕜 v := by
  rw [distinguishingScale]; positivity

/-- The **informative effect** for outcome `i`: the rank-one projector onto the detector
`detector 𝕜 v i`, rescaled by `distinguishingScale 𝕜 v`. -/
def distinguishingEffect (v : ι → E) (i : ι) : E →L[𝕜] E :=
  (distinguishingScale 𝕜 v : 𝕜) • rankOne 𝕜 (detector 𝕜 v i) (detector 𝕜 v i)

theorem distinguishingEffect_isPositive (v : ι → E) (i : ι) :
    (distinguishingEffect 𝕜 v i).IsPositive :=
  (isPositive_rankOne_self (detector 𝕜 v i)).smul_of_nonneg
    (RCLike.ofReal_nonneg.mpr (distinguishingScale_pos 𝕜 v).le)

/-- The **inconclusive effect** `1 - ∑ᵢ Eᵢ` is a positive operator: the scale was chosen so
that `∑ᵢ ⟪Eᵢ x, x⟫ = c ∑ᵢ ‖⟪detector 𝕜 v i, x⟫‖² ≤ c (∑ᵢ ‖detector 𝕜 v i‖²) ‖x‖² ≤ ‖x‖²`. -/
theorem distinguishing_isPositive_none (v : ι → E) :
    ((1 : E →L[𝕜] E) - ∑ i, distinguishingEffect 𝕜 v i).IsPositive := by
  have hcpos : 0 < distinguishingScale 𝕜 v := distinguishingScale_pos 𝕜 v
  refine isPositive_def.mpr ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.toLinearMap_sub]
    exact isPositive_one.isSymmetric.sub
      (isPositive_sum _ fun i _ => distinguishingEffect_isPositive 𝕜 v i).isSymmetric
  · intro x
    have hkey : ((1 : E →L[𝕜] E) - ∑ i, distinguishingEffect 𝕜 v i).reApplyInnerSelf x
        = ‖x‖ ^ 2 - ∑ i, distinguishingScale 𝕜 v * ‖inner 𝕜 (detector 𝕜 v i) x‖ ^ 2 := by
      rw [reApplyInnerSelf_apply, _root_.sub_apply, inner_sub_left, map_sub,
        one_apply_eq_self, inner_self_eq_norm_sq]
      congr 1
      rw [← reApplyInnerSelf_apply, reApplyInnerSelf_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [distinguishingEffect, reApplyInnerSelf_ofReal_smul, reApplyInnerSelf_rankOne_self]
    rw [hkey, sub_nonneg]
    calc ∑ i, distinguishingScale 𝕜 v * ‖inner 𝕜 (detector 𝕜 v i) x‖ ^ 2
        ≤ ∑ i, distinguishingScale 𝕜 v * (‖detector 𝕜 v i‖ ^ 2 * ‖x‖ ^ 2) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ hcpos.le
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _ = distinguishingScale 𝕜 v * (∑ j, ‖detector 𝕜 v j‖ ^ 2) * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
      _ ≤ 1 * ‖x‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [distinguishingScale, inv_mul_le_iff₀ (by positivity)]
          nlinarith [Finset.sum_nonneg
            (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖detector 𝕜 v j‖)]
      _ = ‖x‖ ^ 2 := one_mul _

/-- **The discriminating POVM** for a family `v` of states (Nielsen & Chuang, Exercise 2.64).
The outcome set is `Option ι`: outcome `some i` has effect `Eᵢ = c • |detector 𝕜 v i⟩⟨…|`
(the "state `i` detected" effect), and the single outcome `none` has the inconclusive effect
`1 - ∑ᵢ Eᵢ`. Positivity of the informative effects is `distinguishingEffect_isPositive`, of the
inconclusive effect `distinguishing_isPositive_none`, and completeness is telescoping. -/
def distinguishing (v : ι → E) : POVM (Option ι) 𝕜 E where
  elements o := o.elim (1 - ∑ i, distinguishingEffect 𝕜 v i) (distinguishingEffect 𝕜 v)
  isPositive o := by
    cases o with
    | none => exact distinguishing_isPositive_none 𝕜 v
    | some i => exact distinguishingEffect_isPositive 𝕜 v i
  sum_eq_one := by
    rw [Fintype.sum_option]
    change (1 - ∑ i, distinguishingEffect 𝕜 v i) + ∑ i, distinguishingEffect 𝕜 v i = 1
    rw [sub_add_cancel]

@[simp]
theorem distinguishing_elements_some (v : ι → E) (i : ι) :
    (distinguishing 𝕜 v).elements (some i) = distinguishingEffect 𝕜 v i := rfl

@[simp]
theorem distinguishing_elements_none (v : ι → E) :
    (distinguishing 𝕜 v).elements none = 1 - ∑ i, distinguishingEffect 𝕜 v i := rfl

/-- **Unambiguous discrimination, off-diagonal half.** The Born probability of the informative
outcome `some i` vanishes on any other state `v j` (`j ≠ i`): so observing `some i` rules out
every state but `v i`. -/
theorem distinguishing_reApplyInnerSelf_eq_zero (v : ι → E) {i j : ι} (hij : j ≠ i) :
    ((distinguishing 𝕜 v).elements (some i)).reApplyInnerSelf (v j) = 0 := by
  rw [distinguishing_elements_some, distinguishingEffect, reApplyInnerSelf_ofReal_smul,
    reApplyInnerSelf_rankOne_self, detector_inner_eq_zero 𝕜 v hij, norm_zero]
  simp

/-- **Unambiguous discrimination, diagonal half.** The Born probability of the informative
outcome `some i` on its own state `v i` is strictly positive (Nielsen & Chuang's requirement
`⟪ψᵢ, Eᵢ ψᵢ⟫ > 0`); combined with `distinguishing_reApplyInnerSelf_eq_zero`, outcome `some i`
occurs *only* for the state `v i`. -/
theorem distinguishing_reApplyInnerSelf_pos {v : ι → E} (hv : LinearIndependent 𝕜 v) (i : ι) :
    0 < ((distinguishing 𝕜 v).elements (some i)).reApplyInnerSelf (v i) := by
  rw [distinguishing_elements_some, distinguishingEffect, reApplyInnerSelf_ofReal_smul,
    reApplyInnerSelf_rankOne_self]
  exact mul_pos (distinguishingScale_pos 𝕜 v)
    (pow_pos (norm_pos_iff.mpr (inner_detector_self_ne_zero 𝕜 hv i)) 2)

end POVM
