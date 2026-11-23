/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.CharP.Invertible
import Mathlib.Tactic.IntervalCases

/-!
# Sierpinski's midpoint-convex theorem (set version)

A closed subset of a real topological vector space that is closed under midpoints is convex.
This is the set version of Sierpinski's classical theorem; the proof proceeds by dyadic-rational
approximation in `[0, 1]`.

## Main results

* `Convex.of_isClosed_of_midpoint_mem` — closed + midpoint-stable ⇒ convex.
-/

@[expose] public section

open Set

/-- The dyadic combinations of `0` and `1` lie in any midpoint-stable subset of `ℝ` containing
both endpoints: `(k : ℝ) / 2^n ∈ T` for every `k ≤ 2^n`. -/
private lemma div_pow_two_mem_of_midpoint_mem {T : Set ℝ}
    (h0 : (0 : ℝ) ∈ T) (h1 : (1 : ℝ) ∈ T)
    (h_mid : ∀ ⦃u⦄, u ∈ T → ∀ ⦃v⦄, v ∈ T → midpoint ℝ u v ∈ T) :
    ∀ (n k : ℕ), k ≤ 2 ^ n → ((k : ℝ) / 2 ^ n) ∈ T := by
  intro n
  induction n with
  | zero => intro k hk; interval_cases k <;> simpa
  | succ n ih =>
    intro k hk
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have : ((2 * j : ℕ) : ℝ) / 2 ^ (n + 1) = (j : ℝ) / 2 ^ n := by
        push_cast; field_simp; ring
      rw [this]; exact ih j (by rw [pow_succ] at hk; omega)
    · have : ((2 * j + 1 : ℕ) : ℝ) / 2 ^ (n + 1) =
          midpoint ℝ ((j : ℝ) / 2 ^ n) ((j + 1 : ℕ) / 2 ^ n) := by
        rw [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv]
        push_cast; field_simp; ring
      rw [pow_succ] at hk
      rw [this]; exact h_mid (ih j (by omega)) (ih (j + 1) (by omega))

/-- The dyadic approximation `⌊t · 2^n⌋ / 2^n` of a nonneg real is within `1 / 2^n` of `t`. -/
private lemma abs_sub_floor_div_pow_two_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |t - (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n := by
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  have hlb : (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n ≤ t :=
    (div_le_iff₀ h2pos).mpr (Nat.floor_le (mul_nonneg ht h2pos.le))
  have hub : t < ((⌊t * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n :=
    (lt_div_iff₀ h2pos).mpr (Nat.lt_floor_add_one _)
  have hgap : ((⌊t * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n - (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n = 1 / 2 ^ n := by ring
  rw [abs_le]; constructor <;> linarith

/-- A closed subset of `ℝ` containing `0` and `1` and closed under midpoints contains `[0, 1]`.
This is the one-dimensional set version of Sierpinski's theorem, the inductive core of
`Convex.of_isClosed_of_midpoint_mem`. -/
private lemma Icc_zero_one_subset_of_isClosed_of_midpoint_mem {T : Set ℝ}
    (hT : IsClosed T) (h0 : (0 : ℝ) ∈ T) (h1 : (1 : ℝ) ∈ T)
    (h_mid : ∀ ⦃u⦄, u ∈ T → ∀ ⦃v⦄, v ∈ T → midpoint ℝ u v ∈ T) :
    Set.Icc (0 : ℝ) 1 ⊆ T := fun t ht ↦ by
  refine (Metric.mem_of_closed' hT).mpr fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  have hk_le : ⌊t * 2 ^ n⌋₊ ≤ 2 ^ n :=
    Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_right ht.2 h2pos.le)
  have hpow : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [div_pow]; simp
  refine ⟨(⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n,
    div_pow_two_mem_of_midpoint_mem h0 h1 h_mid n _ hk_le, ?_⟩
  rw [Real.dist_eq]
  exact (abs_sub_floor_div_pow_two_le t ht.1 n).trans_lt (by linarith [hpow ▸ hn])

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Sierpinski's theorem (set version)**: a closed subset of a real topological vector space
that is closed under midpoints is convex. The dyadic-rational density of `[0, 1]` plus
topological closedness upgrades pairwise-midpoint stability to full convex-combination
closedness. -/
theorem Convex.of_isClosed_of_midpoint_mem {s : Set E} (hs : IsClosed s)
    (h_mid : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → midpoint ℝ u v ∈ s) : Convex ℝ s := by
  intro x hx y hy a b ha hb hab
  have hb_in : (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E) b ∈ s := by
    refine Icc_zero_one_subset_of_isClosed_of_midpoint_mem
      (hs.preimage AffineMap.lineMap_continuous)
      (by simpa using hx) (by simpa using hy)
      (fun u hu v hv ↦ ?_) ⟨hb, by linarith⟩
    rw [Set.mem_preimage, AffineMap.map_midpoint]
    exact h_mid hu hv
  rwa [AffineMap.lineMap_apply_module, show 1 - b = a from by linarith] at hb_in
