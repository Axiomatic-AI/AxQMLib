/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CosetOverlapSum
import AxQM.Concrete.SubgroupIndexCount
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concrete: the Ettinger–Høyer–Knill collision sum — its per-intersection geometric tail

This file supplies the **inner geometric sum** of the Ettinger–Høyer–Knill identification bound
behind Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem). Identifying the
hidden subgroup `K` from the `m`-copy coset reduced state `σ_K^{⊗m}` requires controlling the
collision sum over all candidate hidden subgroups `K'` of the pairwise affinity,

`∑_{K'≠K} A(K, K')^m`,   `A(K, K') = |K∩K'| / √(|K|·|K'|)`

(`AxQM.Concrete.cosetAffinity`, `AxQM.cosetDensityState_pi_affinity`). The
Ettinger–Høyer–Knill decomposition **reindexes this sum by the intersection** `H = K ∩ K'`:
candidates with a fixed intersection `H` all lie above `H`, and their contribution is a sum over the
overgroups of `H`, damped by the sample count. This file bounds that inner sum — **sharply**.

## What is proved

* `sum_overgroup_ratio_pow_le_one_add_pow` — the **binomial bound**, the shared kernel of the two
  order-sum estimates below. For *any* exponent `s` (no hypothesis),

  `∑_{K' ≥ H} (|H| / |K'|)^s ≤ (1 + 2^{-s})^{|G|}`,

  the raw output of the relative-generating-set injection into finsets of `G` plus the binomial
  identity `∑_{t⊆G} x^{|t|} = (1+x)^{|G|}`, before any bound on the right side.
* `sum_overgroup_ratio_pow_le` — the **overgroup order-sum bound**. For a fixed subgroup `H` of a
  finite group `G` and an exponent `s` with `2·|G| ≤ 2^s`,

  `∑_{K' ≥ H} (|H| / |K'|)^s ≤ 2`,

  i.e. summing the inverse relative index `(|H|/|K'|)^s = [K':H]^{-s}` over every overgroup `K'` of
  `H` converges to an **absolute constant** — no factor of `|G|`. This sharp bound is exactly what
  keeps the eventual sample count *linear*. It follows from the binomial bound via
  `(1+2^{-s})^{|G|} ≤ e^{|G|·2^{-s}} ≤ e^{½} ≤ 2`.
* `sum_proper_overgroup_ratio_pow_le` — the **proper-overgroup geometric tail**. The same sum with
  its diagonal `K' = H` term removed decays geometrically:

  `∑_{K' ⊋ H} (|H| / |K'|)^s ≤ 2·|G|·2^{-s}`   (again for `2·|G| ≤ 2^s`).

  The full sum's `K' = H` term alone contributes `1`; subtracting it from the binomial bound leaves
  `(1+2^{-s})^{|G|} - 1 ≤ e^{|G|·2^{-s}} - 1 ≤ 2·|G|·2^{-s}` (using `e^y - 1 ≤ 2y` on `[0, 1/2]`).
  This is the sharp form of the Ettinger–Høyer–Knill collision sum's `H = K` fibre (the candidates
  `K' ⊋ K`): at the sample exponent `s = 2 log₂|G| + 1` it is `≤ 1/|G|`, in place of the loose
  constant `1` the per-intersection bound leaves there.

  The proof is a **binomial / relative-generating-set** estimate — not a dyadic-shell count. Every
  `K' ≥ H` is generated over `H` by a finite set `t = t(K') ⊆ G` with `2^{|t|}·|H| ≤ |K'|`, hence
  `[K':H] ≥ 2^{|t|}` (`exists_finset_two_pow_mul_card_le`), and `K' = ⟨t⟩ ⊔ H` recovers `K'` from
  `t`, so `K' ↦ t(K')` is **injective**. Therefore

  `∑_{K'≥H} (|H|/|K'|)^s ≤ ∑_{K'≥H} (2^{-s})^{|t(K')|} ≤ ∑_{t ⊆ G} (2^{-s})^{|t|}
      = (1 + 2^{-s})^{|G|} ≤ e^{|G|·2^{-s}} ≤ e^{1/2} ≤ 2`,

  where the middle equality is the binomial identity `∑_{t⊆G} x^{|t|} = (1+x)^{|G|}`
  (`Finset.prod_add`) and the final step uses `|G|·2^{-s} ≤ 1/2` (the hypothesis `2·|G| ≤ 2^s`) with
  `1/2 < log 2`. The earlier dyadic-shell route through `card_subgroup_index_le` only reached
  `≤ 2·|G|²`, whose spurious
  `|G|²` (the shell-`0` count `|G|^{0+2}` charged to the single member `K' = H`) is fatal to the
  linear sample count; this binomial argument removes it.
* `sum_cosetAffinity_pow_inter_le` — the **per-intersection collision contribution**. For subgroups
  `K, H` of `G` and `2·|G| ≤ 2^s`, the affinity sum over the candidates whose intersection with `K`
  is exactly `H` obeys

  `∑_{K' : K∩K' = H} A(K, K')^{2s} ≤ (|H|/|K|)^s · 2`.

  Each such `K'` has `A(K, K') = |H|/√(|K|·|K'|)`, so `A^{2s} = (|H|/|K|)^s·(|H|/|K'|)^s`; factoring
  the `K`-only weight `(|H|/|K|)^s` out and bounding the residual `∑ (|H|/|K'|)^s` over `{K∩·=H} ⊆
  {·≥H}` by `sum_overgroup_ratio_pow_le` gives the stated bound. (The even exponent `2s` matches
  N&C's sample count `m = 4 log₂|G| + 2 = 2·(2 log₂|G| + 1)`, and keeps the arithmetic on integer
  powers of the squared affinity `A² = |K∩K'|²/(|K||K'|)`, free of `√`.)

## The role in the full bound — and what remains

Writing the full collision sum as `∑_{K'≠K} A(K, K')^{2s} = ∑_{H ≤ K} ∑_{K' : K∩K' = H} A^{2s}` and
applying `sum_cosetAffinity_pow_inter_le` per intersection turns it into

`∑_{K'≠K} A^{2s} ≤ 2 · ∑_{H ≤ K} (|H|/|K|)^s`

— the inner (overgroup) direction fully discharged here, and now with an **absolute** constant `2`
in place of the earlier `2·|G|²`. The **outer** sum `∑_{H ≤ K} (|H|/|K|)^s` runs over the
*sub*groups of `K` weighted by inverse index `[K:H]^{-s}`; bounding it is the dual, low-index
counting direction of the Ettinger–Høyer–Knill argument, and is the remaining ingredient. It is
**not** reachable by the binomial argument here: that argument bounds `∑_{K'≥H} (|H|/|K'|)^s`
because `K' ↦ (generating set of K' over H)` is injective (the closure recovers `K'` with `H`
fixed); for the outer sum `H` varies below the *fixed* `K`, and a generating set of `K` over `H`
does not recover `H`, so no such injection exists. The outer low-index sum therefore needs a
genuinely different combinatorial input (a bound on the number of *large* subgroups of `K`, i.e.
subgroups of small index). Everything here is stated for
group / `Real` data and the quantity `cosetAffinity`.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

/-- `(1 + x) ^ n ≤ e^{n·x}` for `0 ≤ x` — the elementary bound `1 + x ≤ eˣ` raised to the `n`-th
power. A pure `Real` inequality (no group data), shared verbatim by the two overgroup order-sum
estimates below (`sum_overgroup_ratio_pow_le` and `sum_proper_overgroup_ratio_pow_le`). -/
private lemma one_add_pow_le_exp_nmul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ Real.exp (n * x) := by
  calc (1 + x) ^ n ≤ (Real.exp x) ^ n :=
        pow_le_pow_left₀ (add_nonneg zero_le_one hx)
          (by rw [add_comm]; exact Real.add_one_le_exp x) n
    _ = Real.exp (n * x) := (Real.exp_natCast_mul n x).symm

/-- `(1 + x) ^ n - 1 ≤ 2·n·x` for `0 ≤ x` and `n·x ≤ 1/2` — the geometric-tail companion of
`one_add_pow_le_exp_nmul`, via `(1+x)^n ≤ e^{n·x}` and `e^y ≤ 1 + 2y` on `[0, 1/2]` (the latter from
`1 - y ≤ e^{-y}`). A pure `Real` inequality, consumed by `sum_proper_overgroup_ratio_pow_le`. -/
private lemma one_add_pow_sub_one_le_two_nmul {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hnx : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n - 1 ≤ 2 * n * x := by
  have hexp : (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := one_add_pow_le_exp_nmul hx n
  set t : ℝ := (n : ℝ) * x with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg (Nat.cast_nonneg n) hx
  have hey : Real.exp t ≤ 1 + 2 * t := by
    have hepos : (0 : ℝ) < Real.exp t := Real.exp_pos t
    have h1t : (0 : ℝ) < 1 - t := by linarith
    have hinv : 1 - t ≤ (Real.exp t)⁻¹ := by
      have h := Real.add_one_le_exp (-t)
      rw [Real.exp_neg] at h; linarith
    have hle : (1 - t) * Real.exp t ≤ 1 := by
      calc (1 - t) * Real.exp t ≤ (Real.exp t)⁻¹ * Real.exp t :=
            mul_le_mul_of_nonneg_right hinv (le_of_lt hepos)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hepos)
    nlinarith [hle, h1t, mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]
  calc (1 + x) ^ n - 1 ≤ Real.exp t - 1 := by linarith [hexp]
    _ ≤ 2 * t := by linarith [hey]
    _ = 2 * n * x := by rw [ht]; ring

open Classical in
/-- **The binomial bound on the overgroup order-sum** (Nielsen & Chuang, Problem 5.5). For a fixed
subgroup `H` of a finite group `G` and *any* exponent `s`,

`∑_{K' ≥ H} (|H| / |K'|)^s ≤ (1 + 2^{-s})^{|G|}`.

This is the raw output of the **binomial / relative-generating-set** estimate, *before* any bound on
its right side (and needing **no** hypothesis on `s`). Every `K' ≥ H` is generated over `H` by a
finite set `t = t(K') ⊆ G` with `2^{|t|}·|H| ≤ |K'|`, so `[K':H] ≥ 2^{|t|}` and
`(|H|/|K'|)^s ≤ (2^{-s})^{|t|}` (`exists_finset_two_pow_mul_card_le`); since `K' = ⟨t⟩ ⊔ H` recovers
`K'` from `t`, the map `K' ↦ t(K')` is injective, so the overgroup sum is dominated by the sum over
*all* finsets of `G`,

`∑_{K'≥H} (|H|/|K'|)^s ≤ ∑_{t ⊆ G} (2^{-s})^{|t|} = (1 + 2^{-s})^{|G|}`

(binomial identity `∑_{t⊆G} x^{|t|} = (1+x)^{|G|}`, `Finset.prod_add`). The two consumers convert
this further: `sum_overgroup_ratio_pow_le` bounds `(1+2^{-s})^{|G|} ≤ 2` (via `1+y ≤ e^y` and
`|G|·2^{-s} ≤ 1/2`), and `sum_proper_overgroup_ratio_pow_le` subtracts the `K' = H` term to obtain
the geometric tail `(1+2^{-s})^{|G|} - 1 ≤ 2·|G|·2^{-s}`. -/
theorem sum_overgroup_ratio_pow_le_one_add_pow [Finite G] [Fintype (Subgroup G)]
    (H : Subgroup G) (s : ℕ) :
    ∑ K' ∈ Finset.univ.filter (fun K' : Subgroup G => H ≤ K'),
        (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s
      ≤ (1 + ((2 : ℝ) ^ s)⁻¹) ^ Nat.card G := by
  have : Fintype G := Fintype.ofFinite G
  set x : ℝ := ((2 : ℝ) ^ s)⁻¹ with hx
  set S := Finset.univ.filter (fun K' : Subgroup G => H ≤ K') with hS
  -- **Relative generating set.** For each `K' ≥ H` choose `t = g K'` with `⟨t⟩ ⊔ H = K'` and
  -- `2^{|t|}·|H| ≤ |K'|` (`exists_finset_two_pow_mul_card_le`).
  have hg : ∀ K' : Subgroup G, H ≤ K' → ∃ t : Finset G,
      Subgroup.closure (↑t : Set G) ⊔ H = K' ∧ 2 ^ t.card * Nat.card ↥H ≤ Nat.card ↥K' := by
    intro K' hHK'
    obtain ⟨t, _, hcl, hb⟩ := exists_finset_two_pow_mul_card_le H K' hHK'
    exact ⟨t, hcl, hb⟩
  choose! g hgcl hgb using hg
  -- **Injectivity** of `K' ↦ g K'` on `S`: the closure `⟨g K'⟩ ⊔ H` recovers `K'`.
  have hinj : Set.InjOn g ↑S := by
    intro K'₁ h1 K'₂ h2 heq
    have hH1 : H ≤ K'₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hH2 : H ≤ K'₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    rw [← hgcl K'₁ hH1, ← hgcl K'₂ hH2, heq]
  -- **Termwise bound.** `(|H|/|K'|)^s ≤ x^{|g K'|}` with `x = 2^{-s}` (as `[K':H] ≥ 2^{|g K'|}`).
  have hstep : ∀ K' ∈ S, (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s ≤ x ^ (g K').card := by
    intro K' hK'
    have hHK' : H ≤ K' := (Finset.mem_filter.mp hK').2
    have hbnd : (2 : ℝ) ^ (g K').card * Nat.card ↥H ≤ Nat.card ↥K' := by exact_mod_cast hgb K' hHK'
    have hK'pos : (0 : ℝ) < Nat.card ↥K' := by exact_mod_cast Nat.card_pos
    have hbase : (Nat.card ↥H / Nat.card ↥K' : ℝ) ≤ ((2 : ℝ) ^ (g K').card)⁻¹ := by
      rw [div_le_iff₀ hK'pos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      calc (Nat.card ↥H : ℝ) * 2 ^ (g K').card = 2 ^ (g K').card * Nat.card ↥H := by ring
        _ ≤ Nat.card ↥K' := hbnd
    calc (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s
        ≤ (((2 : ℝ) ^ (g K').card)⁻¹) ^ s := pow_le_pow_left₀ (by positivity) hbase s
      _ = x ^ (g K').card := by
          rw [hx, inv_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (g K').card s]
  -- **Assemble** via the injection into finsets and the binomial identity.
  rw [Nat.card_eq_fintype_card (α := G)]
  calc ∑ K' ∈ S, (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s
      ≤ ∑ K' ∈ S, x ^ (g K').card := Finset.sum_le_sum hstep
    _ ≤ ∑ t ∈ (Finset.univ : Finset G).powerset, x ^ t.card := by
        rw [← Finset.sum_image (f := fun t => x ^ t.card) (fun a ha b hb => hinj ha hb)]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => by positivity)
        intro t ht
        simp only [Finset.mem_image] at ht
        obtain ⟨K', _, rfl⟩ := ht
        simp
    _ = (1 + x) ^ Fintype.card G := by
        have hp := Finset.prod_add (fun _ : G => x) (fun _ : G => (1 : ℝ)) Finset.univ
        simp only [Finset.prod_const, one_pow, mul_one, Finset.card_univ] at hp
        rw [add_comm 1 x]
        exact hp.symm

open Classical in
/-- **The overgroup order-sum bound** (Nielsen & Chuang, Problem 5.5, the Ettinger–Høyer–Knill inner
geometric sum). For a fixed subgroup `H` of a finite group `G` and an exponent `s` with
`2·|G| ≤ 2^s`,

`∑_{K' ≥ H} (|H| / |K'|)^s ≤ 2`.

The summand `(|H|/|K'|)^s = [K':H]^{-s}` is the inverse `s`-th power of the relative index; summed
over *every* overgroup `K'` of `H` it converges to an **absolute constant** (no factor of `|G|`)
once `s ≥ log₂|G| + 1`. This sharpness is what keeps the eventual Ettinger–Høyer–Knill sample count
`m = 4 log₂|G| + 2` **linear**.

The proof composes the binomial bound `sum_overgroup_ratio_pow_le_one_add_pow`
(`∑_{K'≥H}(|H|/|K'|)^s ≤ (1+2^{-s})^{|G|}`) with `(1+2^{-s})^{|G|} ≤ e^{|G|·2^{-s}} ≤ e^{½} ≤ 2`
(`1 + y ≤ e^y`, then `|G|·2^{-s} ≤ 1/2` from the hypothesis `2·|G| ≤ 2^s`, and `1/2 < log 2`). The
earlier dyadic-shell route through `card_subgroup_index_le` only reached `≤ 2·|G|²`, whose spurious
`|G|²` factor (the shell-`0` count charged to the single member `K' = H`) would force a *quadratic*
sample count; this argument removes it.

This is the inner sum of the Ettinger–Høyer–Knill collision bound: reindexing `∑_{K'≠K} A(K, K')^m`
by the intersection `H = K∩K'` leaves, per intersection, a geometric sum over the overgroups of `H`
(`sum_cosetAffinity_pow_inter_le`). -/
theorem sum_overgroup_ratio_pow_le [Finite G] [Fintype (Subgroup G)]
    (H : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ≤ 2 ^ s) :
    ∑ K' ∈ Finset.univ.filter (fun K' : Subgroup G => H ≤ K'),
        (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s
      ≤ 2 := by
  have : Fintype G := Fintype.ofFinite G
  refine (sum_overgroup_ratio_pow_le_one_add_pow H s).trans ?_
  rw [Nat.card_eq_fintype_card]
  set x : ℝ := ((2 : ℝ) ^ s)⁻¹ with hx
  have hcard : (Fintype.card G : ℝ) * x ≤ 1 / 2 := by
    rw [hx, mul_inv_le_iff₀ (by positivity)]
    have h2 : (2 : ℝ) * Nat.card G ≤ 2 ^ s := by exact_mod_cast hs
    rw [Nat.card_eq_fintype_card] at h2
    linarith
  calc (1 + x) ^ Fintype.card G
      ≤ Real.exp (Fintype.card G * x) := one_add_pow_le_exp_nmul (by positivity) _
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hcard
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by have := Real.log_two_gt_d9; linarith)
    _ = 2 := Real.exp_log (by norm_num)

open Classical in
/-- **The proper-overgroup geometric tail** (Nielsen & Chuang, Problem 5.5). For a fixed subgroup
`H` of a finite group `G` and an exponent `s` with `2·|G| ≤ 2^s`, the overgroup order-sum with its
diagonal `K' = H` term **removed** decays geometrically in `s`:

`∑_{K' ⊋ H} (|H| / |K'|)^s ≤ 2·|G|·2^{-s}`.

Where the full overgroup order-sum `sum_overgroup_ratio_pow_le` is an absolute constant `≤ 2` (the
`K' = H` term alone contributes `1`), dropping that term leaves the *proper* overgroups, whose
contribution is `O(|G|·2^{-s})` — small once `s ≳ log₂|G|`. At the Ettinger–Høyer–Knill sample
exponent `s = 2 log₂|G| + 1` (so `2^s = 2·|G|²`) this tail is `≤ 1/|G|`.

The proof subtracts the `K' = H` term (`(|H|/|H|)^s = 1`) from the binomial bound
`sum_overgroup_ratio_pow_le_one_add_pow` (`∑_{K'≥H} ≤ (1+2^{-s})^{|G|}`): since
`{K' : H < K'} = {K' : H ≤ K'} ∖ {H}`, the tail equals `∑_{K'≥H}(|H|/|K'|)^s - 1`, so it is at most
`(1+2^{-s})^{|G|} - 1 ≤ e^{|G|·2^{-s}} - 1 ≤ 2·(|G|·2^{-s})` — the last step `e^y - 1 ≤ 2y` for
`0 ≤ y ≤ 1/2` (here `y = |G|·2^{-s} ≤ 1/2` by the hypothesis `2·|G| ≤ 2^s`), from `1 - y ≤ e^{-y}`.

This sharpens the `H = K` fibre of the Ettinger–Høyer–Knill collision sum
(`sum_cosetAffinity_pow_collision_le`): the candidates `K' ⊋ K` are exactly the proper overgroups of
`K`, whose affinity contribution `∑_{K'⊋K}(|K|/|K'|)^s` is this tail at `H = K`, `≤ 2·|G|·2^{-s}` —
not the loose `2` the per-intersection bound leaves there. -/
theorem sum_proper_overgroup_ratio_pow_le [Finite G] [Fintype (Subgroup G)]
    (H : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ≤ 2 ^ s) :
    ∑ K' ∈ Finset.univ.filter (fun K' : Subgroup G => H < K'),
        (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s
      ≤ 2 * (Nat.card G : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
  have : Fintype G := Fintype.ofFinite G
  set x : ℝ := ((2 : ℝ) ^ s)⁻¹ with hx
  -- **The proper-overgroup filter is the overgroup filter with `H` removed.**
  have hHmem : H ∈ Finset.univ.filter (fun K' : Subgroup G => H ≤ K') :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl H⟩
  have hfilter : Finset.univ.filter (fun K' : Subgroup G => H < K')
      = (Finset.univ.filter (fun K' : Subgroup G => H ≤ K')).erase H := by
    ext K'
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
      lt_iff_le_and_ne]
    exact ⟨fun h => ⟨fun hc => h.2 hc.symm, h.1⟩, fun h => ⟨h.2, fun hc => h.1 hc.symm⟩⟩
  -- **Full overgroup sum = 1 (the `K' = H` term) + the proper tail.**
  have hHpos : (0 : ℝ) < Nat.card ↥H := by exact_mod_cast Nat.card_pos
  have hself : (Nat.card ↥H / Nat.card ↥H : ℝ) ^ s = 1 := by
    rw [div_self hHpos.ne', one_pow]
  have hsplit : (1 : ℝ) + ∑ K' ∈ Finset.univ.filter (fun K' : Subgroup G => H < K'),
        (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s
      = ∑ K' ∈ Finset.univ.filter (fun K' : Subgroup G => H ≤ K'),
        (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s := by
    rw [hfilter, ← hself]
    exact Finset.add_sum_erase _ (fun K' : Subgroup G => (Nat.card ↥H / Nat.card ↥K' : ℝ) ^ s) hHmem
  -- **Binomial bound on the full sum**, folded through `x = 2^{-s}`.
  have hbin := sum_overgroup_ratio_pow_le_one_add_pow (G := G) H s
  rw [← hx] at hbin
  -- **`|G|·x ≤ 1/2`** from the hypothesis `2·|G| ≤ 2^s`.
  have hNx : (Nat.card G : ℝ) * x ≤ 1 / 2 := by
    rw [hx, mul_inv_le_iff₀ (by positivity)]
    have h2 : (2 : ℝ) * Nat.card G ≤ 2 ^ s := by exact_mod_cast hs
    linarith
  -- **`(1+x)^{|G|} - 1 ≤ 2·|G|·x`** (`one_add_pow_sub_one_le_two_nmul`, from `1+x ≤ e^x` and
  -- `e^y ≤ 1 + 2y` on `[0, 1/2]`, with `y = |G|·x ≤ 1/2` — the hypothesis `2·|G| ≤ 2^s`).
  have hstep : (1 + x) ^ Nat.card G - 1 ≤ 2 * (Nat.card G : ℝ) * x :=
    one_add_pow_sub_one_le_two_nmul (by positivity) (Nat.card G) hNx
  -- **Assemble:** tail = full − 1 ≤ (1+x)^{|G|} − 1 ≤ 2·|G|·x.
  nlinarith [hsplit, hbin, hstep]

open Classical in
/-- **The per-intersection contribution to the Ettinger–Høyer–Knill collision sum** (Nielsen &
Chuang, Problem 5.5). For subgroups `K, H` of a finite group `G` and an exponent `s` with
`2·|G| ≤ 2^s`, the affinity sum over the candidate hidden subgroups `K'` whose intersection with `K`
is exactly `H` obeys

`∑_{K' : K∩K' = H} A(K, K')^{2s} ≤ (|H|/|K|)^s · 2`.

This reindexes the Ettinger–Høyer–Knill collision sum `∑_{K'≠K} A(K, K')^m` by the intersection
`H = K∩K'` (`A(K, K') = |K∩K'|/√(|K||K'|)`, `cosetAffinity`). For a candidate with `K∩K' = H` the
affinity is `A(K, K') = |H|/√(|K|·|K'|)`, so the even power `A^{2s} = (|H|/|K|)^s·(|H|/|K'|)^s`
splits into a `K`-only weight and a residual over `K'`; factoring the weight out and bounding the
residual `∑ (|H|/|K'|)^s` — taken over `{K∩·=H} ⊆ {·≥H}` — by the (sharp) overgroup order-sum bound
`sum_overgroup_ratio_pow_le` gives the result. The even exponent `2s` matches N&C's sample count
`m = 4 log₂|G| + 2 = 2·(2 log₂|G| + 1)` and keeps the algebra on the squared affinity
`A² = |K∩K'|²/(|K||K'|)`, free of `√`.

Summing this over `H ≤ K` reduces the full collision sum to `2·∑_{H ≤ K} (|H|/|K|)^s` — the inner
(overgroup) direction fully discharged, with an **absolute** constant. The outer factor
`∑_{H ≤ K} (|H|/|K|)^s` (a low-index count over the *sub*groups of `K`) is the remaining
Ettinger–Høyer–Knill ingredient (see the module docstring). -/
theorem sum_cosetAffinity_pow_inter_le [Finite G] [Fintype (Subgroup G)]
    (K H : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ≤ 2 ^ s) :
    ∑ K' ∈ Finset.univ.filter (fun K' : Subgroup G => K ⊓ K' = H),
        cosetAffinity K K' ^ (2 * s)
      ≤ ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s * 2 := by
  -- On the fiber `{K∩·=H}`, `A(K,K')^{2s} = (|H|/|K|)^s·(|H|/|K'|)^s`.
  have hterm : ∀ K' ∈ Finset.univ.filter (fun K' : Subgroup G => K ⊓ K' = H),
      cosetAffinity K K' ^ (2 * s)
        = ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s * ((Nat.card ↥H : ℝ) / Nat.card ↥K') ^ s := by
    intro K' hK'
    have hHeq : K ⊓ K' = H := (Finset.mem_filter.mp hK').2
    unfold cosetAffinity
    rw [hHeq, pow_mul, div_pow, Real.sq_sqrt (by positivity),
      show ((Nat.card ↥H : ℝ) ^ 2 / (Nat.card ↥K * Nat.card ↥K'))
          = ((Nat.card ↥H : ℝ) / Nat.card ↥K) * ((Nat.card ↥H : ℝ) / Nat.card ↥K') by
        rw [div_mul_div_comm]; ring_nf,
      mul_pow]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- `{K∩·=H} ⊆ {·≥H}` (an intersection with `K` equal to `H` forces `H ≤ K'`).
  have hHK'sub : Finset.univ.filter (fun K' : Subgroup G => K ⊓ K' = H)
      ⊆ Finset.univ.filter (fun K' : Subgroup G => H ≤ K') := by
    intro K' hK'
    rw [Finset.mem_filter] at hK' ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hK'.2]; exact inf_le_right
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hHK'sub (fun K' _ _ => by positivity)) ?_
  exact sum_overgroup_ratio_pow_le H hs

end AxQM.Concrete
