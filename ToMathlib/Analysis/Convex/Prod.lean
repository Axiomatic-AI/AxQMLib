/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic

/-!
# Concavity on a product of convex sets, and its converse failure

A function `f : E × F → β` that is concave on a product set `s ×ˢ t` (i.e. *jointly*
concave in its two arguments) is concave in each argument separately, with the other held
fixed. This file records both slices, and the fact that the converse fails: separate
concavity in each argument does **not** imply joint concavity.

## Main results

* `ConcaveOn.slice_left` — if `f` is concave on `s ×ˢ t`, then for each fixed `b ∈ t` the
  map `a ↦ f (a, b)` is concave on `s`.
* `ConcaveOn.slice_right` — the symmetric statement fixing the first argument.
* `mulPair` — the product `(x, y) ↦ x * y` on `ℝ × ℝ`.
* `mulPair_concaveOn_left`, `mulPair_concaveOn_right` — `mulPair` is (affine, hence) concave
  in each argument separately.
* `mulPair_not_concaveOn` — `mulPair` is **not** jointly concave: it is the standard example
  of a function concave in each input yet not jointly concave.

## Implementation notes

The slices are stated for concavity on arbitrary convex subsets `s ×ˢ t` (not just the whole
space), so that they apply e.g. to functions concave only on a restricted domain such as the
positive matrices. Both proofs reduce to the observation that a convex combination of two
points sharing a fixed coordinate keeps that coordinate fixed
(`c • b + d • b = (c + d) • b = b` when `c + d = 1`).
-/

@[expose] public section

open Set

section Slice

variable {𝕜 E F β : Type*}
  [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid β] [PartialOrder β]
  [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]
  {s : Set E} {t : Set F} {f : E × F → β}

/-- **Joint concavity implies concavity in the first argument.** If `f` is concave on the
product `s ×ˢ t`, then for any fixed `b ∈ t`, the function `a ↦ f (a, b)` is concave on `s`. -/
theorem ConcaveOn.slice_left (hf : ConcaveOn 𝕜 (s ×ˢ t) f) {b : F} (hb : b ∈ t) :
    ConcaveOn 𝕜 s (fun a => f (a, b)) := by
  have pairEq : ∀ (x y : E) (c d : 𝕜), c + d = 1 →
      c • (x, b) + d • (y, b) = ((c • x + d • y : E), b) := by
    intro x y c d hcd
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hcd, one_smul]
  refine ⟨fun x hx y hy c d hc hd hcd => ?_, fun x hx y hy c d hc hd hcd => ?_⟩
  · have hmem := hf.1 (Set.mk_mem_prod hx hb) (Set.mk_mem_prod hy hb) hc hd hcd
    rw [pairEq x y c d hcd] at hmem
    exact hmem.1
  · have hineq := hf.2 (Set.mk_mem_prod hx hb) (Set.mk_mem_prod hy hb) hc hd hcd
    rw [pairEq x y c d hcd] at hineq
    exact hineq

/-- **Joint concavity implies concavity in the second argument.** If `f` is concave on the
product `s ×ˢ t`, then for any fixed `a ∈ s`, the function `b ↦ f (a, b)` is concave on `t`. -/
theorem ConcaveOn.slice_right (hf : ConcaveOn 𝕜 (s ×ˢ t) f) {a : E} (ha : a ∈ s) :
    ConcaveOn 𝕜 t (fun b => f (a, b)) := by
  have pairEq : ∀ (x y : F) (c d : 𝕜), c + d = 1 →
      c • (a, x) + d • (a, y) = ((a : E), (c • x + d • y : F)) := by
    intro x y c d hcd
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hcd, one_smul]
  refine ⟨fun x hx y hy c d hc hd hcd => ?_, fun x hx y hy c d hc hd hcd => ?_⟩
  · have hmem := hf.1 (Set.mk_mem_prod ha hx) (Set.mk_mem_prod ha hy) hc hd hcd
    rw [pairEq x y c d hcd] at hmem
    exact hmem.2
  · have hineq := hf.2 (Set.mk_mem_prod ha hx) (Set.mk_mem_prod ha hy) hc hd hcd
    rw [pairEq x y c d hcd] at hineq
    exact hineq

end Slice

section Counterexample

/-- The product function `(x, y) ↦ x * y` on `ℝ × ℝ`. It is the standard example of a
function that is concave (indeed affine) in each argument separately, yet not jointly
concave. -/
def mulPair (p : ℝ × ℝ) : ℝ := p.1 * p.2

/-- `mulPair` is concave in its first argument (with the second held fixed): for fixed `b`,
`a ↦ a * b` is affine, hence concave. -/
theorem mulPair_concaveOn_left (b : ℝ) : ConcaveOn ℝ Set.univ (fun a => mulPair (a, b)) :=
  (LinearMap.mulRight ℝ b).concaveOn convex_univ

/-- `mulPair` is concave in its second argument (with the first held fixed): for fixed `a`,
`b ↦ a * b` is affine, hence concave. -/
theorem mulPair_concaveOn_right (a : ℝ) : ConcaveOn ℝ Set.univ (fun b => mulPair (a, b)) :=
  (LinearMap.mulLeft ℝ a).concaveOn convex_univ

/-- `mulPair` is **not** jointly concave: at `(1, 1)` and `(-1, -1)` with weights `1/2, 1/2`,
the concavity inequality would read `1 ≤ mulPair (0, 0) = 0`, which is false. This exhibits a
function concave in each input separately but not jointly concave (N&C Exercise 11.23). -/
theorem mulPair_not_concaveOn : ¬ ConcaveOn ℝ (Set.univ : Set (ℝ × ℝ)) mulPair := by
  intro h
  have hle := h.2 (Set.mem_univ ((1, 1) : ℝ × ℝ)) (Set.mem_univ ((-1, -1) : ℝ × ℝ))
    (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ + 2⁻¹ = 1)
  simp only [mulPair, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk] at hle
  norm_num at hle

end Counterexample
