/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card

/-! # Counting the fixed-size subsets containing a given element

The number of `n`-element subsets of a finite set `t` that contain a fixed element `a ∈ t` is
`C(t.card − 1, n − 1)`: once `a` is placed, the remaining `n − 1` elements are chosen from the
other `t.card − 1` elements of `t`.

This is the single-element special case (`s = {a}`) of Mathlib's
`Finset.card_filter_powersetCard_subset` (which is not yet available in this snapshot); it is stated
for an arbitrary `Finset t` so it is reusable, not specialised to `t = univ`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- The number of `n`-element subsets of `t` containing a fixed `a ∈ t` is `C(t.card − 1, n − 1)`.
Bijection with the `(n − 1)`-element subsets of `t.erase a`, via `x ↦ x.erase a` and
`y ↦ insert a y`. -/
theorem card_filter_mem_powersetCard {a : α} {t : Finset α} (ha : a ∈ t) {n : ℕ} (hn : 1 ≤ n) :
    ((t.powersetCard n).filter (fun x => a ∈ x)).card = (t.card - 1).choose (n - 1) := by
  rw [← card_erase_of_mem ha, ← card_powersetCard (n - 1) (t.erase a)]
  refine card_bij' (fun x _ => x.erase a) (fun y _ => insert a y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_powersetCard] at hx ⊢
    obtain ⟨⟨hxt, hxc⟩, hax⟩ := hx
    exact ⟨erase_subset_erase a hxt, by rw [card_erase_of_mem hax, hxc]⟩
  · intro y hy
    simp only [mem_powersetCard, mem_filter, mem_powersetCard] at hy ⊢
    obtain ⟨hyt, hyc⟩ := hy
    have hay : a ∉ y := fun h => (mem_erase.mp (hyt h)).1 rfl
    refine ⟨⟨insert_subset ha (hyt.trans (erase_subset a t)), ?_⟩, mem_insert_self _ _⟩
    rw [card_insert_of_notMem hay, hyc, Nat.sub_add_cancel hn]
  · intro x hx
    simp only [mem_filter] at hx
    exact insert_erase hx.2
  · intro y hy
    simp only [mem_powersetCard] at hy
    have hay : a ∉ y := fun h => (mem_erase.mp (hy.1 h)).1 rfl
    exact erase_insert hay

end Finset
