/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Convex.Function

/-!
# Finite sums of convex/concave functions are convex/concave
-/

@[expose] public section

variable {𝕜 E β ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [AddCommMonoid β] [PartialOrder β]
variable [SMul 𝕜 E] [Module 𝕜 β] {s : Set E}

theorem ConvexOn.sum [IsOrderedAddMonoid β] {t : Finset ι} {f : ι → E → β}
    (hs : Convex 𝕜 s) (h : ∀ i ∈ t, ConvexOn 𝕜 s (f i)) :
    ConvexOn 𝕜 s (fun x ↦ ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using convexOn_const 0 hs
  | @insert i t hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

theorem ConcaveOn.sum [IsOrderedAddMonoid β] {t : Finset ι} {f : ι → E → β}
    (hs : Convex 𝕜 s) (h : ∀ i ∈ t, ConcaveOn 𝕜 s (f i)) :
    ConcaveOn 𝕜 s (fun x ↦ ∑ i ∈ t, f i x) :=
  ConvexOn.sum (β := βᵒᵈ) hs h
