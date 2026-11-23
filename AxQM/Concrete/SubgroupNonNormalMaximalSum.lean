/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.IndexNormal
import AxQM.Concrete.SubgroupIndexTwoCount

/-!
# The non-normal maximal-subgroup low-index sum (Ettinger–Høyer–Knill piece (ii))

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Problem 5.5.)* This file discharges the
**reduction** of the last remaining part of the Ettinger–Høyer–Knill maximal-subgroup sum
`∑_{M ⋖ K} (|M|/|K|)^s` — the **non-normal** maximals — to a single clean subgroup **count**,
exactly parallel to the index-`2` (`SubgroupIndexTwoCount.lean`), prime-index-normal
(`SubgroupPrimeIndexNormalCount.lean`), and nonabelian-simple-normal
(`SubgroupSimpleQuotientTypeSum.lean`) parts.

A maximal subgroup `M ⋖ K` is either normal or not in `K`; the normal ones (simple quotient: prime
index, or order-`≥ 4` simple) are handled by the files above. The **non-normal** maximals are the
residual. The key elementary structural fact is that a **non-normal** maximal subgroup has relative
index at least `3`: relative index `2` forces normality (`Subgroup.normal_of_index_eq_two`), so a
non-normal maximal has relative index `≥ 3`, hence weight `(|M|/|K|)^s ≤ (1/3)^s`. Summing gives

`∑_{M ⋖ K, M ⋪ K} (|M|/|K|)^s ≤ #{non-normal maximals of K} · (1/3)^s`
(`sum_nonnormal_maximal_ratio_pow_le`),

so — at N&C's sample exponent `2·|G|² ≤ 2^s` (i.e. `s = 2 log₂|G| + 1`, `m = 2s = 4 log₂|G| + 2`) —
the count bound `#{non-normal maximals of K} ≤ |K|²` drives the non-normal part below `1/(2|G|)`
(`sum_nonnormal_maximal_ratio_pow_le_of_sq`). The **weight `(1/3)^s` (not `(1/2)^s`) is essential**:
with the `2^s ≥ 2|G|²` exponent one has `3^s ≥ 2·|G|³` (from `8^s ≤ 9^s`), so the polynomial count
`≤ |K|² ≤ |G|²` is swamped by the cubic-in-`|G|` decay `3^{-s}`, whereas the mere `(1/2)^s` decay
would only reach the constant `≤ 1/2` (the "mild generation" bound).

This **isolates** the one remaining pure counting ingredient of piece (ii): a **polynomial** bound
`#{non-normal maximals of K} ≤ |K|²` on the number of non-normal maximal subgroups of `K` (implied,
e.g., by the Liebeck–Pyber–Shalev bound `#{maximals of K} ≤ |K|^{3/2}`). Unlike the normal cases —
counted through their quotient homomorphisms (sign / complex characters, `G →* Q` hom-counts) — a
non-normal maximal has no group quotient, so its count is the genuinely Gaussian-binomial-strength
part; this file provides everything except that count.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

/-- **A non-normal maximal subgroup of `K` has relative index at least `3`.** If `M` is a proper
subgroup of `K` (`M < K`) whose image `M.subgroupOf K` is **not** normal in `K`, then
`3 ≤ M.relIndex K`. Indeed the relative index is positive (it divides `|K| > 0`) and cannot be `1`
(else `M.subgroupOf K = ⊤`, i.e. `K ≤ M`, contradicting `M < K`) nor `2` (relative index `2` forces
normality, `Subgroup.normal_of_index_eq_two`), so it is `≥ 3`. Index `2` is the only index that is
automatically normal here, so it is exactly the non-normal maximals pushed to index `≥ 3`. -/
theorem three_le_relIndex_of_lt_of_not_normal [Finite G] {K M : Subgroup G} (hlt : M < K)
    (hnn : ¬ (M.subgroupOf K).Normal) : 3 ≤ M.relIndex K := by
  have hdvd : M.relIndex K ∣ Nat.card ↥K := Subgroup.relIndex_dvd_card M K
  have hpos : 0 < M.relIndex K := Nat.pos_of_dvd_of_pos hdvd Nat.card_pos
  have hne1 : M.relIndex K ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact absurd (le_antisymm hlt.le h1) (ne_of_lt hlt)
  have hne2 : M.relIndex K ≠ 2 := by
    intro h2
    rw [Subgroup.relIndex] at h2
    exact hnn (Subgroup.normal_of_index_eq_two h2)
  omega

/-- A subgroup `M ≤ K` of relative index `≥ 3` has order-ratio `|M|/|K| = 1/[K:M] ≤ 1/3`
(`ratio_eq_one_div_relIndex` at `[K:M] ≥ 3`). -/
theorem ratio_le_of_three_le_relIndex [Finite G] {K M : Subgroup G} (hle : M ≤ K)
    (h3 : 3 ≤ M.relIndex K) : ((Nat.card ↥M : ℝ) / Nat.card ↥K) ≤ 1 / 3 := by
  rw [ratio_eq_one_div_relIndex hle]
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h3)

/-- Arithmetic bridge for the sample exponent: `2·n² ≤ 2^s ⟹ 2·n³ ≤ 3^s`. The point is that the
`2^s ≥ 2|G|²` exponent is strong enough to absorb an extra factor of `|G|` at base `3`: squaring,
`(2n³)² = 4n⁶ ≤ 8n⁶ = (2n²)³ ≤ (2^s)³ = 8^s ≤ 9^s = (3^s)²`, and taking square roots gives the
claim. This is what lets a *polynomial* count (`≤ |K|² ≤ |G|²`) against the `3^{-s}` weight reach
`≤ 1/(2|G|)`, where a `2^{-s}` weight would only reach the constant `1/2`. -/
theorem two_mul_cube_le_three_pow {a : ℝ} {s : ℕ} (ha : 0 ≤ a) (hs : 2 * a ^ 2 ≤ 2 ^ s) :
    2 * a ^ 3 ≤ 3 ^ s := by
  have e8 : ((2 : ℝ) ^ s) ^ 3 = (8 : ℝ) ^ s := by
    rw [← pow_mul, mul_comm s 3, pow_mul]; norm_num
  have e9 : ((3 : ℝ) ^ s) ^ 2 = (9 : ℝ) ^ s := by
    rw [← pow_mul, mul_comm s 2, pow_mul]; norm_num
  have h89 : (8 : ℝ) ^ s ≤ (9 : ℝ) ^ s := pow_le_pow_left₀ (by norm_num) (by norm_num) s
  have hcube : (2 * a ^ 2) ^ 3 ≤ ((2 : ℝ) ^ s) ^ 3 := pow_le_pow_left₀ (by positivity) hs 3
  have key : (2 * a ^ 3) ^ 2 ≤ ((3 : ℝ) ^ s) ^ 2 :=
    calc (2 * a ^ 3) ^ 2 = 4 * a ^ 6 := by ring
      _ ≤ 8 * a ^ 6 := by nlinarith [pow_nonneg ha 6]
      _ = (2 * a ^ 2) ^ 3 := by ring
      _ ≤ ((2 : ℝ) ^ s) ^ 3 := hcube
      _ = (8 : ℝ) ^ s := e8
      _ ≤ (9 : ℝ) ^ s := h89
      _ = ((3 : ℝ) ^ s) ^ 2 := e9.symm
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp key

open Classical in
/-- **The non-normal part of the maximal-subgroup low-index sum, bounded by a count.** For a
subgroup `K` and exponent `s`, the **non-normal** maximal subgroups `M ⋖ K` (`M.subgroupOf K` not
normal in
`K`) each contribute weight `(|M|/|K|)^s ≤ (1/3)^s` (relative index `≥ 3`,
`three_le_relIndex_of_lt_of_not_normal`), so

`∑_{M ⋖ K, M ⋪ K} (|M|/|K|)^s ≤ #{non-normal maximals of K} · (1/3)^s`.

This reduces the entire non-normal part to counting the non-normal maximal subgroups of `K`. -/
theorem sum_nonnormal_maximal_ratio_pow_le [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) (s : ℕ) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).card : ℝ) * (1 / 3) ^ s := by
  have hbound : ∀ M ∈ Finset.univ.filter
      (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal),
      ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s ≤ (1 / 3) ^ s := by
    intro M hM
    rw [Finset.mem_filter] at hM
    obtain ⟨_, hcov, hnn⟩ := hM
    have hlt : M < K := hcov.lt
    have h3 := three_le_relIndex_of_lt_of_not_normal hlt hnn
    exact pow_le_pow_left₀ (by positivity) (ratio_le_of_three_le_relIndex hlt.le h3) s
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans_eq ?_
  rw [nsmul_eq_mul]

open Classical in
/-- **The non-normal part is `≤ 1/(2|G|)` at N&C's sample exponent, given the count bound.** Once
`2·|G|² ≤ 2^s` (i.e. `s = 2 log₂|G| + 1`, N&C's exponent `m = 2s = 4 log₂|G| + 2`), a **polynomial**
bound `#{non-normal maximals of K} ≤ |K|²` on the non-normal maximals drives their contribution to
the maximal-subgroup sum below `1/(2|G|)`:

`∑_{M ⋖ K, M ⋪ K} (|M|/|K|)^s ≤ 1/(2|G|)`.

The count `≤ |K|² ≤ |G|²` times the weight `(1/3)^s = 3^{-s}` gives `≤ |G|²·3^{-s} ≤ 1/(2|G|)`
since `2·|G|³ ≤ 3^s` (`two_mul_cube_le_three_pow`, from `2·|G|² ≤ 2^s`). This isolates the **one**
remaining counting ingredient of Ettinger–Høyer–Knill piece (ii): the polynomial non-normal-maximal
count `#{M ⋖ K : M ⋪ K} ≤ |K|²` (implied by Liebeck–Pyber–Shalev `#{maximals} ≤ |K|^{3/2}`), the
residual that — unlike the normal cases — has no single-quotient character/hom-count witness. With
it, and the index-`2`, prime-index-normal, and nonabelian-simple-normal parts (all `≤ 1/(2|G|)`),
the whole maximal-subgroup sum is `≤ c/|G|`. -/
theorem sum_nonnormal_maximal_ratio_pow_le_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : (Finset.univ.filter
        (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).card ≤ (Nat.card ↥K) ^ 2) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (2 * Nat.card G : ℝ)⁻¹ := by
  refine (sum_nonnormal_maximal_ratio_pow_le K s).trans ?_
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hKle : (Nat.card ↥K : ℝ) ≤ Nat.card G := by
    have : Nat.card ↥K ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card K)
    exact_mod_cast this
  have hcountR : ((Finset.univ.filter
      (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).card : ℝ)
      ≤ (Nat.card ↥K : ℝ) ^ 2 := by exact_mod_cast hcount
  have hsR : (2 : ℝ) * (Nat.card G : ℝ) ^ 2 ≤ 2 ^ s := by exact_mod_cast hs
  have hcube : (2 : ℝ) * (Nat.card G : ℝ) ^ 3 ≤ 3 ^ s :=
    two_mul_cube_le_three_pow (by positivity) hsR
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
  calc ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).card : ℝ) * (1 / 3) ^ s
      ≤ (Nat.card ↥K : ℝ) ^ 2 * (1 / 3) ^ s :=
        mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ ≤ (Nat.card G : ℝ) ^ 2 * (1 / 3) ^ s :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hKle 2) (by positivity)
    _ ≤ (2 * Nat.card G : ℝ)⁻¹ := by
        rw [div_pow, one_pow, mul_one_div, inv_eq_one_div (2 * (Nat.card G : ℝ)),
          div_le_div_iff₀ h3pos (by positivity)]
        nlinarith [hcube]

end AxQM.Concrete
