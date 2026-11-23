/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import AxQM.Concrete.SubgroupFixedQuotientCount

/-!
# Concrete: the per-quotient-type contribution to the nonabelian-simple maximal sum

This file supplies the **per-quotient-type contribution** to the residual maximal-subgroup low-index
sum `∑_{M ⋖ K} (|M|/|K|)^s` behind the Ettinger–Høyer–Knill identification bound of Nielsen &
Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## The context

`Concrete/SubgroupMaximalSum.lean` reduced the Ettinger–Høyer–Knill collision tail to the
**maximal-subgroup low-index sum** `∑_{M ⋖ K} (|M|/|K|)^s`. A maximal subgroup `M ⋖ K` normal in `K`
has a *simple* quotient `K/M`; the **abelian** (prime-index) case was discharged in
`Concrete/SubgroupPrimeIndexNormalCount.lean` by a single character group, and the residual is the
**nonabelian simple** quotients (index `|Q| ≥ 60`), which must be counted **one quotient type `Q` at
a time** (`Concrete/SubgroupFixedQuotientCount.lean`: for a fixed finite `Q` there are at most
`|Q|^{log₂|K|}` subgroups `M ≤ K` with `K/M ≅ Q`). The remaining aggregation over the (at most
`log₂|K|`, `Concrete/SimpleQuotientTypeCount.lean`) realised types decomposes into

* this file — the **per-type** contribution: for each fixed quotient type `Q` (of order `≥ 4`),
  the contribution `∑_{M : K/M ≅ Q} (|M|/|K|)^s` of its whole fibre is `≤ 1/(2|G|²)`; and
* the outstanding **type-aggregation** — summing the per-type contribution over the
  `≤ log₂|K| ≤ |G|` realised types to reach `≤ 1/(2|G|)` (tracked as the next step).

## What is proved

* `sum_fixed_quotient_ratio_pow_le_of_sq` — for a subgroup `K ≤ G` of a finite group `G`, a
  **fixed** finite group `Q` with `4 ≤ |Q|`, and N&C's sample exponent `2·|G|² ≤ 2^s` (i.e.
  `s ≥ 2 log₂|G| + 1`, `m = 2s = 4 log₂|G| + 2`):

  `∑_{M ≤ K, K/M ≅ Q} (|M|/|K|)^s ≤ 1/(2|G|²)`,

  the sum running over the subgroups `M ≤ K` whose relative quotient is `Q` (phrased instance-free
  as `M.subgroupOf K` being the kernel of a surjection `↥K →* Q`). The whole fibre collapses to a
  single weight — each such `M` has `[K:M] = |Q|`, so `(|M|/|K|)^s = |Q|^{-s}` — times the fibre
  count `≤ |Q|^{log₂|K|}` (`card_relIndex_kernel_surjective_hom_le`), giving
  `|Q|^{log₂|K|}·|Q|^{-s} = |Q|^{log₂|K| - s}`. The order threshold `|Q| ≥ 4` and the sample
  exponent make this decay swamp the count: `|Q|^{s - log₂|K|} ≥ 4^{s - log₂|K|} ≥ (2|G|)² ≥ 2|G|²`,
  so the quotient is `≤ 1/(2|G|²)`. (The `≥ 4` threshold is exactly what beats the eventual
  `≤ log₂|K| ≤ |G|` type-count factor: `|G| · 1/(2|G|²) = 1/(2|G|)`. Nonabelian simple quotients
  have `|Q| ≥ 60 ≥ 4`.)
-/

namespace AxQM.Concrete

variable {G : Type*} [Group G]

open Classical in
/-- **The per-quotient-type contribution to the residual maximal-subgroup sum is `≤ 1/(2|G|²)`.**
For a subgroup `K ≤ G` of a finite group `G`, a fixed finite group `Q` with `4 ≤ |Q|`, and N&C's
sample exponent `2·|G|² ≤ 2^s` (`s ≥ 2 log₂|G| + 1`, `m = 2s = 4 log₂|G| + 2`), the total weight of
the subgroups `M ≤ K` whose relative quotient is `Q` — phrased instance-free as `M.subgroupOf K`
being the kernel of a surjective homomorphism `↥K →* Q` (equivalently `↥K ⧸ (M.subgroupOf K) ≃* Q`)
— is

`∑_{M ≤ K, K/M ≅ Q} (|M|/|K|)^s ≤ 1/(2|G|²)`.

Every such `M` has `[K:M] = |Q|` (`Subgroup.card_mul_index` +
`QuotientGroup.quotientKerEquivOfSurjective`),
so its weight `(|M|/|K|)^s = |Q|^{-s}` is the *same* for the whole fibre; the fibre count is
`≤ |Q|^{log₂|K|}` (`card_relIndex_kernel_surjective_hom_le`), so the contribution is
`≤ |Q|^{log₂|K|}·|Q|^{-s}`. Since `|Q| ≥ 4` and `2^s ≥ 2|G|²`, one has (with
`p = log₂|K| ≤ log₂|G|` and `2^p ≤ |K| ≤ |G|`) the natural-number bound `2·|G|²·|Q|^p ≤ |Q|^s`,
i.e. the contribution is `≤ 1/(2|G|²)`. Applied at a nonabelian simple `Q` (`|Q| ≥ 60 ≥ 4`) this
is the per-type ingredient of the nonabelian-simple maximal-subgroup sum; summing it over the
`≤ log₂|K| ≤ |G|` realised quotient types (the outstanding aggregation) yields the target
`≤ 1/(2|G|)`. -/
theorem sum_fixed_quotient_ratio_pow_le_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) (Q : Type*) [Group Q] [Finite Q] (hQ : 4 ≤ Nat.card Q)
    {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ≤ K ∧
          ∃ χ : ↥K →* Q, Function.Surjective χ ∧ χ.ker = M.subgroupOf K),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (2 * Nat.card G ^ 2 : ℝ)⁻¹ := by
  classical
  have hQposR : (0 : ℝ) < (Nat.card Q : ℝ) := by
    have : 0 < Nat.card Q := by omega
    exact_mod_cast this
  have hGposR : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos
  set P := (fun M : Subgroup G => M ≤ K ∧
      ∃ χ : ↥K →* Q, Function.Surjective χ ∧ χ.ker = M.subgroupOf K) with hP
  -- Every subgroup in a fixed-`Q` fibre carries the *same* weight `(1/|Q|)^s`, since `[K:M] = |Q|`.
  have hterm : ∀ M ∈ Finset.univ.filter P,
      ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s = ((Nat.card Q : ℝ)⁻¹) ^ s := by
    intro M hM
    rw [Finset.mem_filter] at hM
    obtain ⟨hle, χ, hsurj, hker⟩ := hM.2
    have hcard : Nat.card ↥M * Nat.card Q = Nat.card ↥K := by
      have e : (↥K ⧸ χ.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective χ hsurj
      have hidx : χ.ker.index = Nat.card Q := by
        rw [Subgroup.index]; exact Nat.card_congr e.toEquiv
      rw [hker] at hidx
      have hmul := Subgroup.card_mul_index (M.subgroupOf K)
      rw [hidx] at hmul
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hmul
    have hMpos : (0 : ℝ) < Nat.card ↥M := by exact_mod_cast Nat.card_pos
    have heq : (Nat.card ↥M : ℝ) / Nat.card ↥K = (Nat.card Q : ℝ)⁻¹ := by
      rw [← hcard]; push_cast; field_simp
    rw [heq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  -- The fibre count is `≤ |Q|^{log₂|K|}` (`card_relIndex_kernel_surjective_hom_le`).
  have hcardle : ((Finset.univ.filter P).card : ℝ)
      ≤ (Nat.card Q ^ Nat.log 2 (Nat.card ↥K) : ℝ) := by
    have h1 : (Finset.univ.filter P).card = Nat.card {M : Subgroup G // P M} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1]; exact_mod_cast card_relIndex_kernel_surjective_hom_le K Q
  -- The arithmetic heart: `2·|G|²·|Q|^{log₂|K|} ≤ |Q|^s` for `4 ≤ |Q|` at the sample exponent.
  have hkeyNat : 2 * Nat.card G ^ 2 * Nat.card Q ^ Nat.log 2 (Nat.card ↥K) ≤ Nat.card Q ^ s := by
    set g := Nat.card G; set q := Nat.card Q; set k := Nat.card ↥K
    set p := Nat.log 2 k with hp
    have hk0 : k ≠ 0 := Nat.card_pos.ne'
    have hkg : k ≤ g := Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card K)
    have hg : 1 ≤ g := Nat.card_pos
    have h2p_le_k : 2 ^ p ≤ k := Nat.pow_log_le_self 2 hk0
    have h2p_le_g : 2 ^ p ≤ g := le_trans h2p_le_k hkg
    -- `s ≥ p + 1`: `2^{p+1} ≤ 2·|G| ≤ 2·|G|² ≤ 2^s`.
    have hps1 : p + 1 ≤ s := by
      have h1 : 2 ^ (p + 1) ≤ 2 ^ s := by
        calc 2 ^ (p + 1) = 2 * 2 ^ p := by ring
          _ ≤ 2 * g := by nlinarith [h2p_le_g]
          _ ≤ 2 * g ^ 2 := by nlinarith [hg]
          _ ≤ 2 ^ s := hs
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    have hps : p ≤ s := le_trans (Nat.le_succ p) hps1
    -- `2^{s-p} ≥ 2|G|` (cancel `2^p` from `2^s ≥ 2|G|² ≥ 2|G|·2^p`).
    have h2sp : 2 * g ≤ 2 ^ (s - p) := by
      have hmul : 2 ^ (s - p) * 2 ^ p = 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hps]
      have hge : 2 * g * 2 ^ p ≤ 2 ^ (s - p) * 2 ^ p := by
        rw [hmul]
        calc 2 * g * 2 ^ p ≤ 2 * g * g := by nlinarith [h2p_le_g]
          _ = 2 * g ^ 2 := by ring
          _ ≤ 2 ^ s := hs
      exact Nat.le_of_mul_le_mul_right hge (pow_pos (by norm_num) p)
    -- `4^{s-p} = (2^{s-p})² ≥ (2|G|)² = 4|G|² ≥ 2|G|²`.
    have h4sp : 2 * g ^ 2 ≤ 4 ^ (s - p) := by
      have hsq : (2 ^ (s - p)) ^ 2 = 4 ^ (s - p) := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      calc 2 * g ^ 2 ≤ 4 * g ^ 2 := by nlinarith
        _ = (2 * g) ^ 2 := by ring
        _ ≤ (2 ^ (s - p)) ^ 2 := by nlinarith [h2sp]
        _ = 4 ^ (s - p) := hsq
    -- `|Q|^{s-p} ≥ 4^{s-p} ≥ 2|G|²`, then multiply by `|Q|^p`.
    have hqsp : 2 * g ^ 2 ≤ q ^ (s - p) := le_trans h4sp (Nat.pow_le_pow_left hQ _)
    calc 2 * g ^ 2 * q ^ p ≤ q ^ (s - p) * q ^ p := Nat.mul_le_mul_right _ hqsp
      _ = q ^ s := by rw [← pow_add, Nat.sub_add_cancel hps]
  have hkey : (2 * Nat.card G ^ 2 : ℝ) * Nat.card Q ^ Nat.log 2 (Nat.card ↥K)
      ≤ (Nat.card Q : ℝ) ^ s := by exact_mod_cast hkeyNat
  -- `|Q|^p · (1/|Q|)^s = |Q|^p / |Q|^s ≤ 1/(2|G|²)`.
  have hstep : ((Nat.card Q : ℝ) ^ Nat.log 2 (Nat.card ↥K)) * ((Nat.card Q : ℝ)⁻¹) ^ s
      ≤ (2 * Nat.card G ^ 2 : ℝ)⁻¹ := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hQposR s),
      inv_mul_eq_div, le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos hGposR 2))]
    linarith [hkey]
  calc ((Finset.univ.filter P).card : ℝ) * ((Nat.card Q : ℝ)⁻¹) ^ s
      ≤ ((Nat.card Q : ℝ) ^ Nat.log 2 (Nat.card ↥K)) * ((Nat.card Q : ℝ)⁻¹) ^ s :=
        mul_le_mul_of_nonneg_right hcardle (by positivity)
    _ ≤ (2 * Nat.card G ^ 2 : ℝ)⁻¹ := hstep

end AxQM.Concrete
