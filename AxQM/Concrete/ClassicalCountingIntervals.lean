/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Concrete: hard instances for the classical counting query lower bound

This is shared infrastructure for the classical query lower bound of Nielsen & Chuang §6.3
(Exercise 6.14): "any classical counting algorithm ... must make `Ω(N)` oracle calls". It supplies
the combinatorial core of the two-point family that separates "no solutions" from "some solutions"
against an adaptive query algorithm (the decision-tree model of
`AxQM/Concrete/ClassicalQueryModel.lean`).

The counting problem is over a Boolean oracle `f : Fin N → Bool`, whose **number of solutions** is
`numSolutions f`, the count of indices at which `f` is `true`. The hard family is the collection of
**length-`m` interval oracles** `intervalOracle m s` (`true` exactly on `[s, s + m)`): each has
exactly `m` solutions (`numSolutions_intervalOracle`), and there are `N - m + 1` of them.

The key combinatorial fact is the **union bound** `card_hitStarts_le`: a fixed query set `Q` of size
`|Q|` can meet ("hit") at most `m · |Q|` of the intervals, because a single queried index lies in at
most `m` of them. Consequently (`card_missStarts_ge`) at least `(N - m + 1) - m · |Q|` intervals
avoid `Q` entirely. Combined with the locality lemma of the query model — an algorithm cannot
distinguish two oracles agreeing on its query set — every avoided interval is indistinguishable from
the all-`false` oracle, which forces the `Ω(N)` bound in the final assembly.

All arithmetic is over `ℕ` via `Fin.val` comparisons (no `NatCast` on `Fin N`, no `Nat.choose`),
keeping the counting cast-free.
-/

namespace AxQM.Concrete

variable {N : ℕ}

/-- The **number of solutions** of a Boolean oracle `f : Fin N → Bool`: the number of indices at
which `f` is `true`. For the counting problem this is the quantity `M` an algorithm estimates. -/
def numSolutions (f : Fin N → Bool) : ℕ := (Finset.univ.filter fun x => f x = true).card

/-- The **length-`m` interval oracle** starting at position `s`: it is `true` exactly on the
indices `x` with `s ≤ x < s + m`, packing `m` solutions into one contiguous block. These are the
hard instances for the counting lower bound; taking `m = 0` gives the all-`false` oracle. -/
def intervalOracle (m s : ℕ) : Fin N → Bool := fun x => decide (s ≤ (x : ℕ) ∧ (x : ℕ) < s + m)

@[simp] lemma intervalOracle_eq_true_iff (m s : ℕ) (x : Fin N) :
    intervalOracle m s x = true ↔ s ≤ (x : ℕ) ∧ (x : ℕ) < s + m := by
  simp [intervalOracle]

lemma intervalOracle_eq_false_iff (m s : ℕ) (x : Fin N) :
    intervalOracle m s x = false ↔ ¬ (s ≤ (x : ℕ) ∧ (x : ℕ) < s + m) := by
  simp [intervalOracle]

/-- The length-`m` interval oracle has exactly `m` solutions, provided the interval fits in
`[0, N)`. -/
lemma numSolutions_intervalOracle {m s : ℕ} (h : s + m ≤ N) :
    numSolutions (intervalOracle (N := N) m s) = m := by
  unfold numSolutions
  have himg : ((Finset.univ.filter fun x : Fin N => intervalOracle m s x = true).image Fin.val)
      = Finset.Ico s (s + m) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      intervalOracle_eq_true_iff, Finset.mem_Ico]
    constructor
    · rintro ⟨x, ⟨hs, hlt⟩, rfl⟩; exact ⟨hs, hlt⟩
    · rintro ⟨hs, hlt⟩
      exact ⟨⟨v, by omega⟩, ⟨hs, hlt⟩, rfl⟩
  have hcard : (Finset.univ.filter fun x : Fin N => intervalOracle m s x = true).card
      = (Finset.Ico s (s + m)).card := by
    rw [← himg]
    exact (Finset.card_image_of_injective _ Fin.val_injective).symm
  rw [hcard, Nat.card_Ico]
  omega

/-- The interval start positions in `range (N - m + 1)` whose length-`m` interval is **hit** by the
query set `Q` — some queried index falls inside `[s, s + m)`. -/
def hitStarts (m : ℕ) (Q : Finset (Fin N)) : Finset ℕ :=
  (Finset.range (N - m + 1)).filter fun s => ∃ q ∈ Q, intervalOracle (N := N) m s q = true

/-- The interval start positions in `range (N - m + 1)` whose length-`m` interval **avoids** the
query set `Q` entirely — every queried index sees `false`, as under the all-`false` oracle. -/
def missStarts (m : ℕ) (Q : Finset (Fin N)) : Finset ℕ :=
  (Finset.range (N - m + 1)).filter fun s => ∀ q ∈ Q, intervalOracle (N := N) m s q = false

/-- **Union bound.** A query set of size `|Q|` hits at most `m · |Q|` of the length-`m` intervals:
each queried index lies in at most `m` of them. -/
lemma card_hitStarts_le (m : ℕ) (Q : Finset (Fin N)) :
    (hitStarts m Q).card ≤ m * Q.card := by
  have hsub : hitStarts m Q ⊆
      Q.biUnion fun q =>
        (Finset.range (N - m + 1)).filter fun s => s ≤ (q : ℕ) ∧ (q : ℕ) < s + m := by
    intro s hs
    rw [hitStarts, Finset.mem_filter] at hs
    obtain ⟨hrange, q, hq, hqtrue⟩ := hs
    rw [intervalOracle_eq_true_iff] at hqtrue
    rw [Finset.mem_biUnion]
    exact ⟨q, hq, Finset.mem_filter.2 ⟨hrange, hqtrue⟩⟩
  calc (hitStarts m Q).card
      ≤ (Q.biUnion fun q =>
          (Finset.range (N - m + 1)).filter fun s => s ≤ (q : ℕ) ∧ (q : ℕ) < s + m).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Q,
          ((Finset.range (N - m + 1)).filter fun s => s ≤ (q : ℕ) ∧ (q : ℕ) < s + m).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q, m := by
        apply Finset.sum_le_sum
        intro q _
        have hsubset :
            (Finset.range (N - m + 1)).filter (fun s => s ≤ (q : ℕ) ∧ (q : ℕ) < s + m)
              ⊆ Finset.Icc ((q : ℕ) + 1 - m) (q : ℕ) := by
          intro s hs
          rw [Finset.mem_filter] at hs
          rw [Finset.mem_Icc]
          omega
        calc ((Finset.range (N - m + 1)).filter fun s => s ≤ (q : ℕ) ∧ (q : ℕ) < s + m).card
            ≤ (Finset.Icc ((q : ℕ) + 1 - m) (q : ℕ)).card := Finset.card_le_card hsubset
          _ ≤ m := by rw [Nat.card_Icc]; omega
    _ = m * Q.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- At least `(N - m + 1) - m · |Q|` of the `N - m + 1` length-`m` intervals avoid the query set
`Q`. This is the union bound in the form the lower-bound argument consumes: many intervals are
indistinguishable from the all-`false` oracle to an algorithm querying only `Q`. -/
lemma card_missStarts_ge (m : ℕ) (Q : Finset (Fin N)) :
    (N - m + 1) - m * Q.card ≤ (missStarts m Q).card := by
  have hcongr : missStarts m Q
      = (Finset.range (N - m + 1)).filter
          fun s => ¬ ∃ q ∈ Q, intervalOracle (N := N) m s q = true := by
    unfold missStarts
    apply Finset.filter_congr
    intro s _
    simp only [not_exists, not_and, Bool.not_eq_true]
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.range (N - m + 1))
    (fun s => ∃ q ∈ Q, intervalOracle (N := N) m s q = true)
  rw [Finset.card_range] at hpart
  rw [hcongr]
  have hhit : (hitStarts m Q).card ≤ m * Q.card := card_hitStarts_le m Q
  rw [hitStarts] at hhit
  omega

end AxQM.Concrete
