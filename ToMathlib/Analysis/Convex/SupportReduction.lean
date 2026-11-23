/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Support reduction of a nonnegative combination minimizing a linear objective

Let `V` be a finite-dimensional real vector space and `v : ι → V` a finite family of points all
lying on the affine hyperplane `{x | φ x = 1}` for a fixed linear functional `φ : V →ₗ[ℝ] ℝ` (think
of `V` as the self-adjoint operators, `φ` the trace, and each `v i` a rank-one projection
`|ψᵢ⟩⟨ψᵢ|`). Given nonnegative weights `w : ι → ℝ` and an auxiliary linear objective
`∑ i, w i * t i`, one can always replace `w` by nonnegative weights `w'` with the **same** weighted
barycenter `∑ i, w' i • v i`, the **same** total weight `∑ i, w' i`, an objective
`∑ i, w' i * t i` that is **no larger**, and support of size at most `finrank ℝ V`.

This is the constructive core of Carathéodory's theorem refined to *simultaneously* minimize a
linear objective (the refinement usually attributed to Fenchel–Eggleston, phrased here for a fixed
hyperplane rather than via boundary points). Because the points lie on `{φ = 1}`, a linear
dependence among more than `finrank ℝ V` of them automatically has coefficients summing to zero
(apply `φ`), so one point can be eliminated while preserving *both* the barycenter and the total
weight; the sign of the elimination direction is chosen to keep the objective from increasing.
Iterating removes points until at most `finrank ℝ V` remain. In the quantum-information application
this yields the `d²` bound on the number of pure states needed to attain the Holevo χ of a channel
(Nielsen & Chuang, Exercise 12.11).

## Main statement

* `exists_reduced_weights_le_finrank`: the reduction described above.
-/

public section

open Finset

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ι : Type*} [Fintype ι]

/-- One elimination step for `exists_reduced_weights_le_finrank`: given a nontrivial affine
dependence `c` (coefficients summing to zero, weighted `v`-sum zero) supported inside the support of
`w`, with a strictly negative coefficient and a non-increasing effect on the objective
(`∑ i, c i * t i ≤ 0`), moving `w` along `c` until a weight vanishes yields nonnegative weights with
the same barycenter and total, an objective no larger, and strictly smaller support. -/
private lemma reduceWeights_step {v : ι → V} (t : ι → ℝ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {c : ι → ℝ} (hcv : ∑ i, c i • v i = 0) (hcsum : ∑ i, c i = 0)
    (hcsupp : ∀ i, c i ≠ 0 → w i ≠ 0) (hneg : ∃ i, c i < 0) (hobj : ∑ i, c i * t i ≤ 0) :
    ∃ w' : ι → ℝ, (∀ i, 0 ≤ w' i) ∧ (∑ i, w' i • v i = ∑ i, w i • v i) ∧
      (∑ i, w' i = ∑ i, w i) ∧ (∑ i, w' i * t i ≤ ∑ i, w i * t i) ∧
      (univ.filter fun i => w' i ≠ 0).card < (univ.filter fun i => w i ≠ 0).card := by
  classical
  set N := univ.filter (fun i => c i < 0) with hN
  have hNne : N.Nonempty := by
    obtain ⟨i, hi⟩ := hneg; exact ⟨i, mem_filter.2 ⟨mem_univ i, hi⟩⟩
  obtain ⟨i₁, hi₁N, hi₁min⟩ := Finset.exists_min_image N (fun i => w i / (-c i)) hNne
  have hci₁ : c i₁ < 0 := (mem_filter.1 hi₁N).2
  have hwi₁ : 0 < w i₁ := (hw i₁).lt_of_ne (Ne.symm (hcsupp i₁ (ne_of_lt hci₁)))
  set θ := w i₁ / (-c i₁) with hθ
  have hθpos : 0 < θ := by rw [hθ]; exact div_pos hwi₁ (neg_pos.2 hci₁)
  set w' : ι → ℝ := fun i => w i + θ * c i with hw'
  -- the freed coordinate `i₁` is zeroed out
  have hw'i₁ : w' i₁ = 0 := by
    have hnc0 : -c i₁ ≠ 0 := neg_ne_zero.2 (ne_of_lt hci₁)
    have hkey : θ * c i₁ = -w i₁ := by rw [hθ, div_mul_eq_mul_div, div_eq_iff hnc0]; ring
    simp only [hw']; rw [hkey]; ring
  -- the new weights are nonnegative
  have hnonneg : ∀ i, 0 ≤ w' i := by
    intro i
    by_cases hci : 0 ≤ c i
    · have : 0 ≤ θ * c i := mul_nonneg hθpos.le hci
      simp only [hw']; linarith [hw i]
    · rw [not_le] at hci
      have hiN : i ∈ N := mem_filter.2 ⟨mem_univ i, hci⟩
      have hri : θ ≤ w i / (-c i) := hi₁min i hiN
      have hpos : (0 : ℝ) < -c i := neg_pos.2 hci
      have hmul : θ * (-c i) ≤ w i := by
        have h := mul_le_mul_of_nonneg_right hri hpos.le
        rwa [div_mul_cancel₀ (w i) hpos.ne'] at h
      have hid : θ * c i = -(θ * (-c i)) := by ring
      simp only [hw']; linarith [hmul, hid]
  -- the barycenter is unchanged
  have hbary : ∑ i, w' i • v i = ∑ i, w i • v i := by
    simp only [hw', add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, hcv, smul_zero, add_zero]
  -- the total weight is unchanged
  have htot : ∑ i, w' i = ∑ i, w i := by
    simp only [hw']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcsum, mul_zero, add_zero]
  -- the objective does not increase
  have hobj' : ∑ i, w' i * t i ≤ ∑ i, w i * t i := by
    have heq : ∑ i, w' i * t i = ∑ i, w i * t i + θ * ∑ i, c i * t i := by
      simp only [hw', add_mul, mul_assoc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hprod : θ * ∑ i, c i * t i ≤ 0 := by
      nlinarith [mul_nonneg hθpos.le (neg_nonneg.2 hobj)]
    rw [heq]; linarith
  -- the support strictly shrinks: it lies inside the old support and loses `i₁`
  have hsub : (univ.filter fun i => w' i ≠ 0) ⊆ (univ.filter fun i => w i ≠ 0) := by
    intro i hi
    rw [mem_filter] at hi ⊢
    refine ⟨mem_univ i, ?_⟩
    intro hwi
    apply hi.2
    have hci : c i = 0 := by by_contra hcine; exact hcsupp i hcine hwi
    simp only [hw', hwi, hci, mul_zero, add_zero]
  have hi₁mem : i₁ ∈ (univ.filter fun i => w i ≠ 0) := mem_filter.2 ⟨mem_univ i₁, ne_of_gt hwi₁⟩
  have hi₁nmem : i₁ ∉ (univ.filter fun i => w' i ≠ 0) := by
    simp only [mem_filter, mem_univ, true_and, not_not]; exact hw'i₁
  exact ⟨w', hnonneg, hbary, htot, hobj',
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨i₁, hi₁mem, hi₁nmem⟩)⟩

/-- **Support reduction minimizing a linear objective** (a hyperplane-refined Carathéodory theorem).
Let `V` be a finite-dimensional real vector space, `φ : V →ₗ[ℝ] ℝ` a linear functional, and
`v : ι → V` a finite family of points all lying on the affine hyperplane `{x | φ x = 1}`
(`hv : ∀ i, φ (v i) = 1`). For nonnegative weights `w` and any `t : ι → ℝ`, there are nonnegative
weights `w'` with the same weighted barycenter `∑ i, w' i • v i`, the same total `∑ i, w' i`, an
objective `∑ i, w' i * t i` no larger than `∑ i, w i * t i`, and support — realized as a finite set
`s` with `w' i ≠ 0 ↔ i ∈ s` — of cardinality at most `finrank ℝ V` (the bound is on the actual
support; the `↔` keeps the statement free of a decidability instance).

Applied to the self-adjoint operators with `φ` the trace and `v i = |ψᵢ⟩⟨ψᵢ|` rank-one projections,
this is the convex-geometry heart of the `d²` bound on the ensemble size attaining a channel's
Holevo χ quantity (Nielsen & Chuang, Exercise 12.11). -/
theorem exists_reduced_weights_le_finrank [Module.Finite ℝ V] (φ : V →ₗ[ℝ] ℝ) {v : ι → V}
    (hv : ∀ i, φ (v i) = 1) (t : ι → ℝ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∃ w' : ι → ℝ, (∀ i, 0 ≤ w' i) ∧ (∑ i, w' i • v i = ∑ i, w i • v i) ∧
      (∑ i, w' i = ∑ i, w i) ∧ (∑ i, w' i * t i ≤ ∑ i, w i * t i) ∧
      ∃ s : Finset ι, (∀ i, w' i ≠ 0 ↔ i ∈ s) ∧ s.card ≤ Module.finrank ℝ V := by
  classical
  -- induct on a cardinality bound for the support of `w`
  suffices H : ∀ N : ℕ, ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) →
      (univ.filter fun i => w i ≠ 0).card ≤ N →
      ∃ w' : ι → ℝ, (∀ i, 0 ≤ w' i) ∧ (∑ i, w' i • v i = ∑ i, w i • v i) ∧
        (∑ i, w' i = ∑ i, w i) ∧ (∑ i, w' i * t i ≤ ∑ i, w i * t i) ∧
        (univ.filter fun i => w' i ≠ 0).card ≤ Module.finrank ℝ V by
    obtain ⟨w', h1, h2, h3, h4, h5⟩ := H _ w hw le_rfl
    exact ⟨w', h1, h2, h3, h4, univ.filter (fun i => w' i ≠ 0),
      fun i => ⟨fun hi => mem_filter.2 ⟨mem_univ i, hi⟩, fun hi => (mem_filter.1 hi).2⟩, h5⟩
  intro N
  induction N with
  | zero =>
    intro w hw hcard
    exact ⟨w, hw, rfl, rfl, le_rfl, le_trans hcard (Nat.zero_le _)⟩
  | succ N ih =>
    intro w hw hcard
    by_cases hle : (univ.filter fun i => w i ≠ 0).card ≤ Module.finrank ℝ V
    · exact ⟨w, hw, rfl, rfl, le_rfl, hle⟩
    · rw [not_le] at hle
      set s := univ.filter (fun i => w i ≠ 0) with hs
      -- more than `finrank` of the `v i` over the support are linearly dependent
      have hdep : ¬ LinearIndependent ℝ (fun i : s => v i) := by
        intro hli
        have hcard2 : Fintype.card (s : Type _) ≤ Module.finrank ℝ V := hli.fintype_card_le_finrank
        rw [Fintype.card_coe] at hcard2
        exact absurd hcard2 (not_le.2 hle)
      rw [Fintype.not_linearIndependent_iff] at hdep
      obtain ⟨g, hg0, i₀, hgi₀⟩ := hdep
      -- extend the dependence by zero outside the support
      set c : ι → ℝ := fun i => if h : i ∈ s then g ⟨i, h⟩ else 0 with hc
      have hgc : ∀ i : s, g i • v ↑i = c ↑i • v ↑i := fun i => by
        simp only [hc, dite_eq_left i.2, Subtype.coe_eta]
      have hcsupp : ∀ i, c i ≠ 0 → w i ≠ 0 := by
        intro i hci hwi
        have hins : i ∉ s := by
          simp only [hs, mem_filter, mem_univ, true_and, not_not]; exact hwi
        exact hci (by simp only [hc, dite_eq_right hins])
      have hcv : ∑ i, c i • v i = 0 := by
        have e1 : ∑ i, c i • v i = ∑ i ∈ s, c i • v i := by
          refine (Finset.sum_subset (subset_univ s) ?_).symm
          intro i _ hnotin
          simp only [hc, dite_eq_right hnotin, zero_smul]
        rw [e1, ← Finset.sum_coe_sort s (fun i => c i • v i), ← hg0]
        exact Finset.sum_congr rfl fun i _ => (hgc i).symm
      have hcsum : ∑ i, c i = 0 := by
        have key : ∑ i, c i = φ (∑ i, c i • v i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hv i, smul_eq_mul, mul_one]
        rw [key, hcv, map_zero]
      have hcne : ∃ i, c i ≠ 0 :=
        ⟨↑i₀, by simp only [hc, dite_eq_left i₀.2, Subtype.coe_eta]; exact hgi₀⟩
      -- from `∑ c = 0` and `c ≠ 0`, coefficients of both signs occur
      have hcneg : ∃ i, c i < 0 := by
        by_contra h; rw [not_exists] at h
        obtain ⟨j, hj⟩ := hcne
        have hnn : ∀ i, 0 ≤ c i := fun i => not_lt.1 (h i)
        exact hj ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 hcsum j (mem_univ j))
      have hcpos : ∃ i, 0 < c i := by
        by_contra h; rw [not_exists] at h
        obtain ⟨j, hj⟩ := hcne
        have hnp : ∀ i, c i ≤ 0 := fun i => not_lt.1 (h i)
        have hsum' : ∑ i, -c i = 0 := by rw [Finset.sum_neg_distrib, hcsum, neg_zero]
        have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => neg_nonneg.2 (hnp i)).1 hsum' j
          (mem_univ j)
        exact hj (by linarith [hz])
      -- choose the elimination direction so that the objective does not increase
      by_cases hobjle : ∑ i, c i * t i ≤ 0
      · obtain ⟨w'', h1, h2, h3, h4, h5⟩ := reduceWeights_step t hw hcv hcsum hcsupp hcneg hobjle
        rw [← hs] at h5
        obtain ⟨w', k1, k2, k3, k4, k5⟩ := ih w'' h1 (Nat.lt_succ_iff.mp (lt_of_lt_of_le h5 hcard))
        exact ⟨w', k1, k2.trans h2, k3.trans h3, k4.trans h4, k5⟩
      · rw [not_le] at hobjle
        have hcv' : ∑ i, (-c i) • v i = 0 := by
          simp only [neg_smul, Finset.sum_neg_distrib, hcv, neg_zero]
        have hcsum' : ∑ i, -c i = 0 := by rw [Finset.sum_neg_distrib, hcsum, neg_zero]
        have hcsupp' : ∀ i, -c i ≠ 0 → w i ≠ 0 := fun i hi => hcsupp i (neg_ne_zero.mp hi)
        have hcneg' : ∃ i, -c i < 0 := by obtain ⟨i, hi⟩ := hcpos; exact ⟨i, by linarith⟩
        have hobjle' : ∑ i, (-c i) * t i ≤ 0 := by
          have h : ∑ i, (-c i) * t i = -(∑ i, c i * t i) := by
            simp only [neg_mul, Finset.sum_neg_distrib]
          rw [h]; linarith
        obtain ⟨w'', h1, h2, h3, h4, h5⟩ :=
          reduceWeights_step t hw hcv' hcsum' hcsupp' hcneg' hobjle'
        rw [← hs] at h5
        obtain ⟨w', k1, k2, k3, k4, k5⟩ := ih w'' h1 (Nat.lt_succ_iff.mp (lt_of_lt_of_le h5 hcard))
        exact ⟨w', k1, k2.trans h2, k3.trans h3, k4.trans h4, k5⟩
