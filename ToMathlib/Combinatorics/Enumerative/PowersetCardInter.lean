/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A hypergeometric left-tail count for subsets meeting a fixed set

Fix a finite ground set `S` and a distinguished subset `E ⊆ S` (think: `S` are `2 * n` bits and
`E` the erroneous ones). Sampling an `n`-element subset `C ⊆ S`, this file bounds the number of
samples that meet `E` in *few* elements — the left tail of the hypergeometric distribution.

The bound is elementary. The map `C ↦ (C ∩ E, C \ E)` injects the subsets `C` with
`(C ∩ E).card < s` into `{A ∈ E.powerset | A.card < s} ×ˢ (S \ E).powerset`, because
`C = (C \ E) ∪ (C ∩ E)` recovers `C` from the pair. Hence their count is at most
`(∑ j ∈ range s, (E.card).choose j) * 2 ^ (S \ E).card`. Dropping the cardinality constraint on
the second coordinate — bounding the subsets of `S \ E` by all `2 ^ (S \ E).card` of them, rather
than tracking `(C \ E).card = n - (C ∩ E).card` — trades the exact hypergeometric count for a
clean, side-condition-free inequality. That is all that is needed to turn the count into an
`exp[-Θ(ε² n)]` sampling-error bound.

## Main results

* `Finset.card_powersetCard_filter_inter_lt_le`: the tail-count inequality above.

This is the combinatorial core (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.27, step (1)) of the random-sampling test in the BB84 quantum key distribution security
analysis: a random sample of `n` of the `2 * n` bits meeting the error set in few places is
exponentially unlikely when the total error count is large.
-/

open Finset

namespace Finset

public section

variable {α : Type*} [DecidableEq α]

/-- The number of subsets of `E` with fewer than `s` elements is the partial sum of a row of
Pascal's triangle: `#{A ⊆ E | A.card < s} = ∑ j ∈ range s, (E.card).choose j`, obtained by
partitioning the small subsets of `E` by their cardinality. -/
theorem card_powerset_filter_card_lt {α : Type*} (E : Finset α) (s : ℕ) :
    (E.powerset.filter (fun A => A.card < s)).card = ∑ j ∈ Finset.range s, (E.card).choose j := by
  classical
  have hbi : E.powerset.filter (fun A => A.card < s)
      = (Finset.range s).biUnion (fun j => E.powersetCard j) := by
    ext A
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨hAE, hcard⟩; exact ⟨A.card, hcard, hAE, rfl⟩
    · rintro ⟨j, hj, hAE, hAcard⟩; exact ⟨hAE, hAcard ▸ hj⟩
  rw [hbi, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun j _ => Finset.card_powersetCard j E)
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun A hAx hAy => hxy ?_
    rw [mem_powersetCard] at hAx hAy
    exact hAx.2 ▸ hAy.2

/-- **Hypergeometric left-tail count.** For a finite ground set `S`, a subset `E`, and thresholds
`n`, `s`, the number of `n`-element subsets `C ⊆ S` meeting `E` in fewer than `s` elements is at
most `(∑ j ∈ range s, (E.card).choose j) * 2 ^ (S \ E).card`.

The count of `n`-subsets of `S` with exactly `j` elements in `E` is the hypergeometric term
`(E.card).choose j * (S \ E).card.choose (n - j)`; this inequality replaces the second binomial by
the trivial bound `2 ^ (S \ E).card`, which suffices for the entropy estimates that follow and
avoids any side condition relating `s`, `n` and the cardinalities. -/
theorem card_powersetCard_filter_inter_lt_le (S E : Finset α) (n s : ℕ) :
    ((S.powersetCard n).filter (fun C => (C ∩ E).card < s)).card
      ≤ (∑ j ∈ Finset.range s, (E.card).choose j) * 2 ^ (S \ E).card := by
  -- Inject `C ↦ (C ∩ E, C \ E)` into `{A ⊆ E | A.card < s} ×ˢ (S \ E).powerset`.
  calc ((S.powersetCard n).filter (fun C => (C ∩ E).card < s)).card
      ≤ ((E.powerset.filter (fun A => A.card < s)) ×ˢ (S \ E).powerset).card := by
        refine Finset.card_le_card_of_injOn (fun C => (C ∩ E, C \ E)) ?_ ?_
        · intro C hC
          simp only [Finset.mem_coe, mem_filter, mem_powersetCard] at hC
          obtain ⟨⟨hCS, _⟩, hlt⟩ := hC
          simp only [Finset.mem_coe, mem_product, mem_filter, mem_powerset]
          exact ⟨⟨inter_subset_right, hlt⟩, sdiff_subset_sdiff hCS Subset.rfl⟩
        · intro C₁ _ C₂ _ heq
          simp only [Prod.mk.injEq] at heq
          obtain ⟨he, hd⟩ := heq
          rw [← Finset.sdiff_union_inter C₁ E, ← Finset.sdiff_union_inter C₂ E, he, hd]
    _ = (E.powerset.filter (fun A => A.card < s)).card * (S \ E).powerset.card :=
        Finset.card_product _ _
    _ = (∑ j ∈ Finset.range s, (E.card).choose j) * 2 ^ (S \ E).card := by
        rw [card_powerset_filter_card_lt E s, Finset.card_powerset]

end

end Finset
