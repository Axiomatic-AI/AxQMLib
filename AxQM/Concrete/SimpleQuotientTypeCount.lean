/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PairwiseSimpleQuotientCount

/-!
# Concrete: the number of distinct simple-quotient types of an *arbitrary* subgroup family

This file supplies the **arbitrary-family sharp type-count** for the *aggregation over quotient
types* behind the Ettinger–Høyer–Knill maximal-subgroup low-index sum `∑_{M ⋖ K} (|M|/|K|)^s`
for Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## Why the identification bound needs this

`Concrete/SubgroupFixedQuotientCount.lean` counts, *per fixed* simple quotient type `Q`, the normal
maximals `M ⋖ K` with `K/M ≅ Q` (`card_relIndex_kernel_surjective_hom_le`, `≤ |Q|^{log₂|K|}`). To
aggregate those per-type counts into a bound on the residual sum
`∑_{M ⋖ K,\ K/M\ \text{nonab.\ simple}} [K:M]^{-s}` one needs the **number of distinct simple
quotient types** to be `≤ log₂|K|` — the sharp count (a crude type-count by the number of subgroups
would reintroduce a `(log₂|K|)²` term and return to the quadratic sample regime).

`Concrete/PairwiseSimpleQuotientCount.lean` proved exactly `log₂|K|` — but only for a family whose
quotients are *already pairwise non-isomorphic* (`card_le_log_of_pairwise_noniso_simpleQuotient`,
via diagonal surjectivity `∏ᵢ [K:Nᵢ] ≤ |K|`). The **actual** residual maximals are *not*
pre-selected that way: many share a quotient type. This file closes that gap, reducing an
**arbitrary** family of normal subgroups with simple quotients to a pairwise-non-isomorphic
*covering* subfamily — one representative per realised quotient type — and thereby bounds the number
of distinct types of an arbitrary family by `log₂|H|`.

## What is proved

* `exists_subset_pairwise_noniso_cover` — for any indexed family `N : ι → Subgroup H` of **normal**
  subgroups and any finset `s` of indices, there is a subfinset `r ⊆ s` that is (i) **covering**:
  every `i ∈ s` has some `j ∈ r` with `H ⧸ N i ≃* H ⧸ N j`, and (ii) **pairwise
  non-isomorphic**: distinct `i, j ∈ r` have `H ⧸ N i ≇ H ⧸ N j`. So `r` picks out exactly one
  representative per quotient isomorphism type realised over `s`. It is proved by strong induction
  on `s`: pick any `m ∈ s`, recurse on the subfinset `s'` of indices whose quotient is *not*
  isomorphic to `H ⧸ N m`, and prepend `m`. (Only normality is needed — the quotients must be
  groups; neither finiteness nor simplicity enters.)
* `exists_subset_cover_card_le_log_of_simpleQuotient` — when in addition `H` is finite and each
  `H ⧸ N i` (over `s`) is **simple**, the covering subfamily `r` has `r.card ≤ log₂|H|`: it is
  pairwise non-isomorphic with simple quotients, so
  `card_le_log_of_pairwise_noniso_simpleQuotient` applies. This is the sharp type-count for an
  arbitrary family — the last combinatorial ingredient before the per-type counts of
  `SubgroupFixedQuotientCount.lean` can be aggregated into the residual maximal-subgroup sum bound
  (`∑_{M ⋖ K,\ K/M\ \text{nonab.\ simple}} [K:M]^{-s} ≤ c/|G|`, tracked as the next step).
-/

namespace AxQM.Concrete

variable {H : Type*} [Group H] {ι : Type*}

/-- **A pairwise non-isomorphic covering subfamily of representatives.** For any family
`N : ι → Subgroup H` of normal subgroups and any finset `s` of indices, there is `r ⊆ s` such that

* every `i ∈ s` is *covered* — `∃ j ∈ r, H ⧸ N i ≃* H ⧸ N j` (some representative shares its
  quotient type), and
* the representatives are *pairwise non-isomorphic* — distinct `i, j ∈ r` have `H ⧸ N i ≇ H ⧸ N j`.

Thus `r` selects exactly one index per quotient isomorphism type realised over `s`. Proof by strong
induction on `s`: for nonempty `s` pick some `m ∈ s`, let `s'` be the indices whose quotient is
*not* isomorphic to `H ⧸ N m` (a proper subfinset, as `m ∉ s'` via the identity isomorphism),
extract a covering subfamily `r'` of `s'` by the induction hypothesis, and return `insert m r'`: `m`
covers everything isomorphic to `H ⧸ N m`, `r'` covers the rest, and `m` is non-isomorphic to every
member of `r' ⊆ s'`. Only normality is used (so the quotients carry a group structure). -/
theorem exists_subset_pairwise_noniso_cover (N : ι → Subgroup H) [∀ i, (N i).Normal]
    (s : Finset ι) :
    ∃ r ⊆ s, (∀ i ∈ s, ∃ j ∈ r, Nonempty (H ⧸ N i ≃* H ⧸ N j)) ∧
      (∀ i ∈ r, ∀ j ∈ r, i ≠ j → IsEmpty (H ⧸ N i ≃* H ⧸ N j)) := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with hs | ⟨m, hm⟩
    · exact ⟨∅, by simp [hs], by simp [hs], by simp⟩
    · -- Recurse on the indices whose quotient is *not* isomorphic to `H ⧸ N m`.
      set s' := s.filter (fun i => IsEmpty (H ⧸ N i ≃* H ⧸ N m)) with hs'
      have hs'ss : s' ⊂ s := by
        refine Finset.filter_ssubset.mpr ⟨m, hm, ?_⟩
        simp only [not_isEmpty_iff]
        exact ⟨MulEquiv.refl _⟩
      obtain ⟨r', hr's', hcov', hpw'⟩ := ih s' hs'ss
      have hmemS' : ∀ i ∈ r', IsEmpty (H ⧸ N i ≃* H ⧸ N m) := fun i hi =>
        (Finset.mem_filter.mp (hr's' hi)).2
      refine ⟨insert m r', ?_, ?_, ?_⟩
      · -- `insert m r' ⊆ s`
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hm
        · exact (hr's'.trans (Finset.filter_subset _ _)) hi
      · -- covering
        intro i hi
        by_cases hiso : Nonempty (H ⧸ N i ≃* H ⧸ N m)
        · exact ⟨m, Finset.mem_insert_self _ _, hiso⟩
        · have hiS' : i ∈ s' := Finset.mem_filter.mpr ⟨hi, not_nonempty_iff.mp hiso⟩
          obtain ⟨j, hjr', hcov⟩ := hcov' i hiS'
          exact ⟨j, Finset.mem_insert_of_mem hjr', hcov⟩
      · -- pairwise non-isomorphic
        intro i hi j hj hne
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact absurd rfl hne
          · exact ⟨fun e => (hmemS' j hj').false e.symm⟩
        · rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact ⟨fun e => (hmemS' i hi').false e⟩
          · exact hpw' i hi' j hj' hne

/-- **The number of distinct simple-quotient types of a family is at most `log₂|H|`.** For a finite
group `H` and a family `N : ι → Subgroup H` of normal subgroups whose quotients `H ⧸ N i` (over `s`)
are **simple**, there is a covering subfinset `r ⊆ s` — one representative per realised quotient
type — with `r.card ≤ log₂|H|`. Indeed `r` is pairwise non-isomorphic with simple quotients
(`exists_subset_pairwise_noniso_cover`), so `card_le_log_of_pairwise_noniso_simpleQuotient` bounds
its size. This is the sharp type-count for an *arbitrary* family (dropping the
pairwise-non-isomorphic hypothesis of `card_le_log_of_pairwise_noniso_simpleQuotient`): the number
of distinct simple
quotient types realised over `s` is `≤ log₂|H|` — the aggregation ingredient the residual
maximal-subgroup low-index sum needs. -/
theorem exists_subset_cover_card_le_log_of_simpleQuotient [Finite H] (N : ι → Subgroup H)
    [∀ i, (N i).Normal] (s : Finset ι) (hsimple : ∀ i ∈ s, IsSimpleGroup (H ⧸ N i)) :
    ∃ r ⊆ s, (∀ i ∈ s, ∃ j ∈ r, Nonempty (H ⧸ N i ≃* H ⧸ N j)) ∧
      r.card ≤ Nat.log 2 (Nat.card H) := by
  obtain ⟨r, hrs, hcov, hpw⟩ := exists_subset_pairwise_noniso_cover N s
  exact ⟨r, hrs, hcov,
    card_le_log_of_pairwise_noniso_simpleQuotient N r (fun i hi => hsimple i (hrs hi)) hpw⟩

end AxQM.Concrete
