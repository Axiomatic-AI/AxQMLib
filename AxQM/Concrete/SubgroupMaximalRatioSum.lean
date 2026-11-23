/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupPrimeIndexNormalCount
import AxQM.Concrete.SubgroupSimpleQuotientTypeSum
import AxQM.Concrete.SubgroupNonNormalMaximalConjugacy

/-!
# The assembled maximal-subgroup ratio sum (Ettinger–Høyer–Knill piece ii)

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Problem 5.5.)* This file **assembles** the
four separately-proven bounds on the maximal-subgroup ratio sum `∑_{M ⋖ K} (|M|/|K|)^s` into a
single statement, isolating the entire remaining Ettinger–Høyer–Knill counting tail (piece ii) as
**one** clean group-theoretic hypothesis.

The collision-sum reduction `sum_cosetAffinity_pow_collision_maximal_le_of_sq`
(`SubgroupMaximalSum.lean`) pins the whole EHK counting tail on the maximal-subgroup sum
`∑_{M ⋖ K} (|M|/|K|)^s`. A maximal
`M ⋖ K` is either **normal** in `K` or **non-normal**, and a normal maximal has a **simple**
quotient `K/M` (the correspondence theorem: a coatom of the subgroup lattice yields a simple
quotient — `isSimpleGroup_quotient_of_covBy_of_normal`), which is either **cyclic of prime order**
(abelian simple) or **nonabelian simple** (order `≥ 60 ≥ 4`). So the maximals split into three
families, each already bounded at N&C's sample exponent `2·|G|² ≤ 2^s`:

* **prime-index normal** — `≤ 1/(2|G|)` (`sum_prime_index_normal_maximal_ratio_pow_le_of_sq`,
  complex characters `G →* ℂˣ`), which also subsumes the elementary index-`2` count;
* **nonabelian-simple normal** — `≤ 1/(2|G|)` (`sum_simple_quotient_ratio_pow_le_of_sq`, per-type
  hom-count `≤ |Q|^{log₂|K|}` aggregated over `≤ log₂|K|` quotient types);
* **non-normal** — `≤ 1/(2|G|)` **given** `3·#{K-conjugacy classes of non-normal maximals} ≤ |K|²`
  (`sum_nonnormal_maximal_ratio_pow_le_classCard_of_sq`, self-normalization + orbit–stabilizer).

## The two headline results

* `sum_normal_maximal_ratio_pow_le_of_sq` — the **normal** maximals contribute `≤ 1/|G|`,
  *unconditionally* (the first two families summed). Every remaining conditionality of piece (ii)
  is therefore confined to the non-normal maximals.
* `sum_maximal_ratio_pow_le_of_classCard_sq` — the **full** maximal-subgroup sum
  `∑_{M ⋖ K} (|M|/|K|)^s ≤ 3/(2|G|)`, *conditional only* on the single non-normal class count
  `3·#{K-conj classes of non-normal maximals} ≤ |K|²` (Liebeck–Pyber–Shalev-strength — the one
  genuinely deep-group-theory residual of piece ii, with no group quotient to count through). This
  collapses the ~eight-file maximal-subgroup development into one bound whose sole open input is
  that count.

Both are stated over the real-valued weight `(|M|/|K|)^s`.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

/-- **A subgroup covered by `K` and normal in it has a simple quotient.** If `M ⋖ K` (maximal in
`K`) and `M.subgroupOf K` is normal, then `↥K ⧸ M.subgroupOf K` is a simple group. This is the group
form of the correspondence (fourth isomorphism) theorem: a subgroup of the quotient pulls back to a
subgroup of `↥K` containing the coatom `M.subgroupOf K`, hence is `M.subgroupOf K` or `⊤` by
maximality, so the quotient has only the trivial and improper subgroups. (Normality of
`M.subgroupOf K` is only needed to form the quotient group; the argument controls *all* subgroups of
the quotient, not just the normal ones.) -/
theorem isSimpleGroup_quotient_of_covBy_of_normal {K M : Subgroup G} (h : M ⋖ K)
    (hN : (M.subgroupOf K).Normal) : IsSimpleGroup (↥K ⧸ M.subgroupOf K) := by
  have := hN
  have hMK : M ≤ K := h.1.le
  have hNtop : M.subgroupOf K ≠ ⊤ :=
    fun hEq => h.1.ne (le_antisymm hMK (Subgroup.subgroupOf_eq_top.mp hEq))
  have : Nontrivial (↥K ⧸ M.subgroupOf K) := QuotientGroup.nontrivial_iff.mpr hNtop
  refine ⟨fun H' _ => ?_⟩
  set B : Subgroup ↥K := Subgroup.comap (QuotientGroup.mk' (M.subgroupOf K)) H' with hBdef
  have hNB : M.subgroupOf K ≤ B := QuotientGroup.le_comap_mk' _ _
  set B' : Subgroup G := B.map K.subtype with hB'def
  have hMB' : M ≤ B' := by
    rw [hB'def]
    calc M = (M.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hMK).symm
      _ ≤ B.map K.subtype := Subgroup.map_mono hNB
  have hB'K : B' ≤ K := Subgroup.map_subtype_le B
  have hHeq : H' = Subgroup.map (QuotientGroup.mk' (M.subgroupOf K)) B := by
    rw [hBdef, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rcases eq_or_lt_of_le hMB' with hEq | hLt
  · left
    have hBN : B = M.subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      rw [← hB'def, ← hEq, Subgroup.map_subgroupOf_eq_of_le hMK]
    rw [hHeq, hBN, Subgroup.map_eq_bot_iff]
    exact (QuotientGroup.ker_mk' _).ge
  · right
    have hB'K' : B' = K := by
      by_contra hne
      exact (h.2 hLt) (lt_of_le_of_ne hB'K hne)
    have hBtop : B = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [← hB'def, hB'K', ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hHeq, hBtop]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- **A normal maximal subgroup has prime relative index or a simple quotient of order `≥ 4`.** For
`M ⋖ K` normal in `K`, the relative index `[K : M]` (`= Nat.card (↥K ⧸ M.subgroupOf K)`) is `≥ 2`;
if it is `< 4` it is `2` or `3`, hence prime, and if it is `≥ 4` the (simple) quotient has order
`≥ 4`. This is the case split feeding the two normal-maximal counting families. -/
private theorem covBy_normal_prime_relIndex_or_simpleQuot [Finite G] {K M : Subgroup G}
    (hcov : M ⋖ K) (hnorm : (M.subgroupOf K).Normal) :
    (M.relIndex K).Prime ∨
      (IsSimpleGroup (↥K ⧸ M.subgroupOf K) ∧ 4 ≤ Nat.card (↥K ⧸ M.subgroupOf K)) := by
  have := hnorm
  have hMK : M ≤ K := hcov.1.le
  have hNtop : M.subgroupOf K ≠ ⊤ :=
    fun hEq => hcov.1.ne (le_antisymm hMK (Subgroup.subgroupOf_eq_top.mp hEq))
  have hidx : (M.subgroupOf K).index = Nat.card (↥K ⧸ M.subgroupOf K) := Subgroup.index_eq_card _
  have hrel : M.relIndex K = Nat.card (↥K ⧸ M.subgroupOf K) := hidx
  have hn2 : 2 ≤ Nat.card (↥K ⧸ M.subgroupOf K) := by
    have := Subgroup.one_lt_index_of_ne_top (H := M.subgroupOf K) hNtop
    rw [hidx] at this; omega
  rcases lt_or_ge (Nat.card (↥K ⧸ M.subgroupOf K)) 4 with hlt | hge
  · left
    rw [hrel]
    rcases (show Nat.card (↥K ⧸ M.subgroupOf K) = 2 ∨ Nat.card (↥K ⧸ M.subgroupOf K) = 3 by omega)
      with h | h <;> rw [h] <;> norm_num
  · exact Or.inr ⟨isSimpleGroup_quotient_of_covBy_of_normal hcov hnorm, hge⟩

/-- **Union bound for a nonnegative real weight.** `∑_{s ∪ t} f ≤ ∑_s f + ∑_t f` when `f ≥ 0`, via
inclusion–exclusion `Finset.sum_union_inter` discarding the nonnegative intersection term. -/
private theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ i, 0 ≤ f i) : ∑ M ∈ s ∪ t, f M ≤ (∑ M ∈ s, f M) + ∑ M ∈ t, f M := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hi : 0 ≤ ∑ M ∈ s ∩ t, f M := Finset.sum_nonneg (fun i _ => hf i)
  linarith

open Classical in
/-- **The normal maximal subgroups contribute `≤ 1/|G|`** (Ettinger–Høyer–Knill piece ii,
unconditional). At N&C's sample exponent `2·|G|² ≤ 2^s`, the ratio sum over the maximal subgroups
`M ⋖ K` that are *normal* in `K` is `≤ 1/|G|`:

`∑_{M ⋖ K, M ◁ K} (|M|/|K|)^s ≤ 1/|G|`.

Every normal maximal has a simple quotient (`isSimpleGroup_quotient_of_covBy_of_normal`), hence lies
in the prime-index family (`sum_prime_index_normal_maximal_ratio_pow_le_of_sq`, `≤ 1/(2|G|)`) or the
order-`≥ 4` simple-quotient family (`sum_simple_quotient_ratio_pow_le_of_sq`, `≤ 1/(2|G|)`); their
sum bounds this. It is **unconditional**: the two normal families are counted through their quotient
characters/homomorphisms, so all remaining conditionality of piece (ii) is confined to the
non-normal maximals. -/
theorem sum_normal_maximal_ratio_pow_le_of_sq [Finite G] [Fintype (Subgroup G)] (K : Subgroup G)
    {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K ∧ (M.subgroupOf K).Normal),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (Nat.card G : ℝ)⁻¹ := by
  classical
  have hwnn : ∀ M : Subgroup G, 0 ≤ ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s := fun M => by positivity
  have hsub :
      Finset.univ.filter (fun M : Subgroup G => M ⋖ K ∧ (M.subgroupOf K).Normal)
        ⊆ Finset.univ.filter
            (fun M : Subgroup G => M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime)
          ∪ Finset.univ.filter
            (fun M : Subgroup G => M ≤ K ∧
              ∃ _ : (M.subgroupOf K).Normal,
                IsSimpleGroup (↥K ⧸ M.subgroupOf K) ∧ 4 ≤ Nat.card (↥K ⧸ M.subgroupOf K)) := by
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hM ⊢
    obtain ⟨hcov, hnorm⟩ := hM
    rcases covBy_normal_prime_relIndex_or_simpleQuot hcov hnorm with hp | hs4
    · exact Or.inl ⟨hcov.1.le, hnorm, hp⟩
    · exact Or.inr ⟨hcov.1.le, hnorm, hs4.1, hs4.2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hwnn i)).trans ?_
  refine (sum_union_le_of_nonneg _ _ _ hwnn).trans ?_
  have h2 := sum_prime_index_normal_maximal_ratio_pow_le_of_sq K hs
  have h3 := sum_simple_quotient_ratio_pow_le_of_sq K hs
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have heq : (2 * (Nat.card G : ℝ))⁻¹ + (2 * (Nat.card G : ℝ))⁻¹ = (Nat.card G : ℝ)⁻¹ := by
    have hG0 : (Nat.card G : ℝ) ≠ 0 := by exact_mod_cast hGpos.ne'
    field_simp; ring
  linarith

open Classical in
/-- **The full maximal-subgroup ratio sum is `≤ 3/(2|G|)`, conditional only on the non-normal class
count** (Ettinger–Høyer–Knill piece ii). At N&C's sample exponent `2·|G|² ≤ 2^s`, and
*given* the single group-theoretic count
`3·#{K-conjugacy classes of non-normal maximals} ≤ |K|²`, the whole maximal-subgroup ratio sum obeys

`∑_{M ⋖ K} (|M|/|K|)^s ≤ 3/(2|G|)`.

It splits the maximals into normal (`≤ 1/|G|`, `sum_normal_maximal_ratio_pow_le_of_sq`,
unconditional) and non-normal (`≤ 1/(2|G|)`, `sum_nonnormal_maximal_ratio_pow_le_classCard_of_sq`,
using the class count); `1/|G| + 1/(2|G|) = 3/(2|G|)`. This bound collapses the entire
Ettinger–Høyer–Knill counting tail (piece ii) into the *single* Liebeck–Pyber–Shalev-strength count
of the `K`-conjugacy classes of non-normal maximal subgroups — the one residual with no group
quotient to count through. Composing it with the collision reduction
`sum_cosetAffinity_pow_collision_maximal_le_of_sq` (which consumes the mild
`∀ J, ∑_{M ⋖ J} (|M|/|J|)^s ≤ 1/2` this bound supplies for `|G| ≥ 3`) would drive the coset
collision sum below `1/|G|` at N&C's linear sample count. -/
theorem sum_maximal_ratio_pow_le_of_classCard_sq [Finite G] [Fintype (Subgroup G)] (K : Subgroup G)
    {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : 3 * ((Finset.univ.filter
        (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).image
        (fun M => Quotient.mk (MulAction.orbitRel ↥K (Subgroup G)) M)).card
      ≤ (Nat.card ↥K) ^ 2) :
    ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ 3 / (2 * Nat.card G) := by
  classical
  have hwnn : ∀ M : Subgroup G, 0 ≤ ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s := fun M => by positivity
  have hsub :
      Finset.univ.filter (fun M : Subgroup G => M ⋖ K)
        ⊆ Finset.univ.filter (fun M : Subgroup G => M ⋖ K ∧ (M.subgroupOf K).Normal)
          ∪ Finset.univ.filter (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal) := by
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hM ⊢
    by_cases hnorm : (M.subgroupOf K).Normal
    · exact Or.inl ⟨hM, hnorm⟩
    · exact Or.inr ⟨hM, hnorm⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hwnn i)).trans ?_
  refine (sum_union_le_of_nonneg _ _ _ hwnn).trans ?_
  have hnorm := sum_normal_maximal_ratio_pow_le_of_sq K hs
  have hnn := sum_nonnormal_maximal_ratio_pow_le_classCard_of_sq K hs hcount
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have heq : (Nat.card G : ℝ)⁻¹ + (2 * Nat.card G : ℝ)⁻¹ = 3 / (2 * Nat.card G) := by
    have hG0 : (Nat.card G : ℝ) ≠ 0 := by exact_mod_cast hGpos.ne'
    field_simp; ring
  linarith

end AxQM.Concrete
