/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.IIDConcentration

/-!
# The theorem of typical sequences (classical asymptotic equipartition property)

For a finite alphabet `α`, a probability mass function `p : α → ℝ` (`0 ≤ p x`, `∑ x, p x = 1`) and a
tolerance `ε`, a length-`n` sequence `s : Fin n → α` is **`ε`-typical** when its `n`-fold i.i.d.
product probability `∏ i, p (s i)` is squeezed between `exp (-n (H + ε))` and `exp (-n (H - ε))`,
where `H = Real.entropy p` is the Shannon entropy (in nats). This is Nielsen & Chuang's primary
definition (their Eq. 12.26), the natural-logarithm form of `2^{-n(H+ε)} ≤ p ≤ 2^{-n(H-ε)}` (the
base-`2` version is the same statement rescaled). We record it as the `Finset`

`Real.typicalSeq p n ε : Finset (Fin n → α)`,

so that `(typicalSeq p n ε).card` is `|T(n, ε)|`. Because the lower bound is a strictly positive
exponential, zero-probability sequences are automatically excluded — which is exactly why the
multiplicative form (12.26), rather than the additive surprisal form (12.27), is the honest primary
definition: on the support the two coincide (`mem_typicalSeq_iff_abs_le`), but a letter of
probability `0` has surprisal `-log 0 = 0` and would spuriously satisfy the additive form.

Building on the finite i.i.d. Chebyshev concentration bound `Real.iid_average_deviation_le`
(`ToMathlib/InformationTheory/IIDConcentration.lean`), applied to the surprisal `g x = -log (p x)`
whose mean is `H`, this file proves **Nielsen & Chuang, Theorem 12.2**, parts (1) and (2).

## Main results

- `Real.typicalSeq`: the `ε`-typical set (Eq. 12.26).
- `Real.mem_typicalSeq`: its membership predicate.
- `Real.mem_typicalSeq_iff_abs_le`: on the support (`0 < ∏ i, p (s i)`), typicality is equivalent to
  the additive surprisal form `|(∑ i, -log (p (s i)))/n - H| ≤ ε` (Eq. 12.26 ↔ 12.27).
- `Real.sum_typicalSeq_ge`: **part (1), quantitative** — the probability that a sequence is typical
  is at least `1 - V/(n ε²)`, where `V = ∑ x, p x (-log (p x) - H)²` is the surprisal variance.
- `Real.exists_le_sum_typicalSeq`: **part (1), Nielsen–Chuang form** — for any `δ > 0`, for all
  sufficiently large `n`, that probability is at least `1 - δ`.
- `Real.card_typicalSeq_le`: **part (2), upper bound** — `|T(n, ε)| ≤ exp (n (H + ε))`, for every
  `n` (Eq. 12.28, right).
- `Real.card_typicalSeq_ge_of_le_sum`: **part (2), lower bound** — whenever the typicality
  probability is at least `1 - δ`, `(1 - δ) exp (n (H - ε)) ≤ |T(n, ε)|` (Eq. 12.28, left).
- `Real.exists_card_typicalSeq_bounds`: **part (2), Nielsen–Chuang form** — for any `δ > 0`, for all
  sufficiently large `n`, both cardinality bounds of Eq. 12.28 hold.
- `Real.exists_sum_weighted_prod_le_of_sum_le_exp`: **part (3), the small-set bound, weighted form**
  — for a rate `R < H` and any `δ > 0`, for all sufficiently large `n` *every* family of weights
  `w : (Fin n → α) → ℝ` with `0 ≤ w s ≤ 1` and `∑ s, w s ≤ exp (n R)` has `∑ s, w s · ∏ p ≤ δ`. The
  proof splits at the `ε`-typical set (`ε = (H - R)/2`): the atypical part is small by part (1)
  (weights `≤ 1`), and the typical part has total weight `≤ exp (n R)` with each factor `≤ exp
  (-n (H - ε))`. The fractional weights are what the quantum typical subspace theorem (Thm 12.5 (3))
  needs.
- `Real.exists_sum_prod_le_of_card_le_exp`: **part (3), the small-set bound** (Eq. 12.29) — the
  `0/1`-indicator special case: for `R < H`, `δ > 0`, large `n`, *every* collection `S` with
  `|S| ≤ exp (n R)` carries total probability `∑ s ∈ S, ∏ p ≤ δ`.
-/

@[expose] public section

open Finset

namespace Real

variable {α : Type*} [Fintype α]

open Classical in
/-- The set `T(n, ε)` of **`ε`-typical** length-`n` sequences for the i.i.d. source `p`
(Nielsen & Chuang, Eq. 12.26): those `s : Fin n → α` whose product probability `∏ i, p (s i)` lies
between `exp (-n (H + ε))` and `exp (-n (H - ε))`, with `H = entropy p`. The lower bound being a
positive exponential, this automatically excludes zero-probability sequences. -/
noncomputable def typicalSeq (p : α → ℝ) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) :=
  univ.filter fun s => Real.exp (-(n : ℝ) * (entropy p + ε)) ≤ ∏ i, p (s i) ∧
    ∏ i, p (s i) ≤ Real.exp (-(n : ℝ) * (entropy p - ε))

/-- Membership in the `ε`-typical set: `s` is typical iff its product probability is squeezed
between `exp (-n (H + ε))` and `exp (-n (H - ε))`. -/
theorem mem_typicalSeq {p : α → ℝ} {n : ℕ} {ε : ℝ} {s : Fin n → α} :
    s ∈ typicalSeq p n ε ↔
      Real.exp (-(n : ℝ) * (entropy p + ε)) ≤ ∏ i, p (s i) ∧
      ∏ i, p (s i) ≤ Real.exp (-(n : ℝ) * (entropy p - ε)) := by
  simp only [typicalSeq, mem_filter, mem_univ, true_and]

/-- **Eq. 12.26 ↔ Eq. 12.27.** On the support of the product distribution (`0 < ∏ i, p (s i)`, i.e.
`p (s i) > 0` for all `i`), `s` is `ε`-typical iff its per-symbol empirical surprisal
`(∑ i, -log (p (s i)))/n` is within `ε` of the entropy `H = entropy p`. This is the equivalence
between the multiplicative definition and the additive reformulation, valid precisely on the
support (where `log (∏ i, p (s i)) = ∑ i, log (p (s i))`). -/
theorem mem_typicalSeq_iff_abs_le {p : α → ℝ} {n : ℕ} (hn : 0 < n) {ε : ℝ}
    {s : Fin n → α} (hpos : 0 < ∏ i, p (s i)) :
    s ∈ typicalSeq p n ε ↔
      |(∑ i, -Real.log (p (s i))) / (n : ℝ) - entropy p| ≤ ε := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  have hne : ∀ i, p (s i) ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp hpos.ne') i (mem_univ i)
  have hsum : (∑ i, -Real.log (p (s i))) = -Real.log (∏ i, p (s i)) := by
    rw [Real.log_prod (fun x _ => hne x)]
    exact Finset.sum_neg_distrib _
  rw [mem_typicalSeq, ← Real.le_log_iff_exp_le hpos, ← Real.log_le_iff_le_exp hpos]
  set L := Real.log (∏ i, p (s i))
  rw [hsum]
  have hfrac : (-L) / (n : ℝ) - entropy p = (-L - entropy p * n) / n := by field_simp
  rw [hfrac, abs_div, abs_of_pos hn0, div_le_iff₀ hn0, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- **Nielsen & Chuang, Theorem 12.2 (1), quantitative form.** The probability that a length-`n`
sequence is `ε`-typical is at least `1 - V/(n ε²)`, where `V = ∑ x, p x (-log (p x) - H)²` is the
per-symbol surprisal variance. As `n → ∞` this tends to `1` (see `exists_le_sum_typicalSeq`).

The proof bounds the complement mass: the atypical set is pulled back, via
`mem_typicalSeq_iff_abs_le`, into the empirical-surprisal large-deviation set, whose mass the
Chebyshev engine `iid_average_deviation_le` bounds by `V/(n ε²)`; the total mass is `1`. -/
theorem sum_typicalSeq_ge {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    1 - (∑ x, p x * (-Real.log (p x) - entropy p) ^ 2) / (n * ε ^ 2)
      ≤ ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) := by
  classical
  have hcompl : ∑ s ∈ univ \ typicalSeq p n ε, ∏ i, p (s i)
      ≤ (∑ x, p x * (-Real.log (p x) - entropy p) ^ 2) / (n * ε ^ 2) := by
    set g : α → ℝ := fun x => -Real.log (p x) with hg
    have hm : entropy p = ∑ x, p x * g x := by
      simp only [hg]
      rw [entropy_eq_neg_sum_mul_log, ← Finset.sum_neg_distrib]
      simp only [mul_neg]
    have hdev := iid_average_deviation_le p g hp0 hp1 hm hn hε
    refine le_trans ?_ hdev
    rw [Finset.sdiff_eq_filter, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun s _ => ?_
    have hnn : (0 : ℝ) ≤ ∏ i, p (s i) := Finset.prod_nonneg fun i _ => hp0 _
    have hRHSnn : (0 : ℝ) ≤
        (if ε < |(∑ i, g (s i)) / (n : ℝ) - entropy p| then ∏ i, p (s i) else 0) := by
      split_ifs <;> first | exact hnn | exact le_refl 0
    by_cases hT : s ∈ typicalSeq p n ε
    · rw [ite_eq_right (not_not.mpr hT)]; exact hRHSnn
    · rw [ite_eq_left hT]
      rcases hnn.eq_or_lt with hz | hpos
      · exact hz.symm.le.trans hRHSnn
      · have hnotle : ¬ |(∑ i, -Real.log (p (s i))) / (n : ℝ) - entropy p| ≤ ε := fun hle =>
          hT ((mem_typicalSeq_iff_abs_le hn hpos).mpr hle)
        have hB : ε < |(∑ i, g (s i)) / (n : ℝ) - entropy p| :=
          not_le.mp (by simpa only [hg] using hnotle)
        exact (ite_eq_left hB).ge
  have htotal : ∑ s : Fin n → α, ∏ i, p (s i) = 1 := by rw [iid_total_mass, hp1, one_pow]
  have hsplit : ∑ s ∈ univ \ typicalSeq p n ε, ∏ i, p (s i)
      + ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) = 1 := by
    rw [Finset.sum_sdiff (Finset.subset_univ _)]; exact htotal
  linarith

/-- **Nielsen & Chuang, Theorem 12.2 (2), upper bound** (Eq. 12.28, right). For every `n`, the
number of `ε`-typical sequences satisfies `|T(n, ε)| ≤ exp (n (H + ε))`. Each typical sequence has
probability at least `exp (-n (H + ε))`, and the typical sequences carry total probability at most
`1`, so `|T(n, ε)| · exp (-n (H + ε)) ≤ 1`. -/
theorem card_typicalSeq_le {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {n : ℕ} {ε : ℝ} :
    ((typicalSeq p n ε).card : ℝ) ≤ Real.exp (n * (entropy p + ε)) := by
  have hnn : ∀ s : Fin n → α, (0 : ℝ) ≤ ∏ i, p (s i) := fun s => Finset.prod_nonneg fun i _ => hp0 _
  have htotal : ∑ s : Fin n → α, ∏ i, p (s i) = 1 := by rw [iid_total_mass, hp1, one_pow]
  have hsum_le_one : ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) ≤ 1 := by
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun s _ _ => hnn s
  have hlb : ((typicalSeq p n ε).card : ℝ) * Real.exp (-(n : ℝ) * (entropy p + ε))
      ≤ ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun s hs => (mem_typicalSeq.mp hs).1
  have hexp : Real.exp (-(n : ℝ) * (entropy p + ε)) = (Real.exp (n * (entropy p + ε)))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hexp] at hlb
  have hcard : ((typicalSeq p n ε).card : ℝ) / Real.exp (n * (entropy p + ε)) ≤ 1 := by
    rw [div_eq_mul_inv]; exact hlb.trans hsum_le_one
  rw [div_le_iff₀ (Real.exp_pos _)] at hcard
  simpa using hcard

/-- **Nielsen & Chuang, Theorem 12.2 (2), lower bound** (Eq. 12.28, left). Whenever the typicality
probability is at least `1 - δ`, the number of `ε`-typical sequences satisfies
`(1 - δ) exp (n (H - ε)) ≤ |T(n, ε)|`. Each typical sequence has probability at most
`exp (-n (H - ε))`, so `1 - δ ≤ |T(n, ε)| · exp (-n (H - ε))`. Fed the large-`n` typicality
probability of `exists_le_sum_typicalSeq`, this yields the Eq. 12.28 lower bound. -/
theorem card_typicalSeq_ge_of_le_sum {p : α → ℝ} {n : ℕ} {ε : ℝ} {δ : ℝ}
    (h : 1 - δ ≤ ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i)) :
    (1 - δ) * Real.exp (n * (entropy p - ε)) ≤ ((typicalSeq p n ε).card : ℝ) := by
  have hub : ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i)
      ≤ ((typicalSeq p n ε).card : ℝ) * Real.exp (-(n : ℝ) * (entropy p - ε)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun s hs => (mem_typicalSeq.mp hs).2
  have h1 : 1 - δ ≤ ((typicalSeq p n ε).card : ℝ) * Real.exp (-(n : ℝ) * (entropy p - ε)) :=
    h.trans hub
  have hb := mul_le_mul_of_nonneg_right h1 (Real.exp_pos ((n : ℝ) * (entropy p - ε))).le
  have hexp0 : Real.exp (-(n : ℝ) * (entropy p - ε)) * Real.exp ((n : ℝ) * (entropy p - ε)) = 1 :=
    by rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  rw [mul_assoc, hexp0, mul_one] at hb
  exact hb

/-- **Nielsen & Chuang, Theorem 12.2 (1), Nielsen–Chuang form.** Fix `ε > 0`. For any `δ > 0`, for
all sufficiently large `n`, the probability that a sequence is `ε`-typical is at least `1 - δ`.
This packages the quantitative bound `sum_typicalSeq_ge` with the Archimedean fact that
`V/(n ε²) → 0`. -/
theorem exists_le_sum_typicalSeq {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, 1 - δ ≤ ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) := by
  set V := ∑ x, p x * (-Real.log (p x) - entropy p) ^ 2
  have hVnn : 0 ≤ V := Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (sq_nonneg _)
  have hden : (0 : ℝ) < δ * ε ^ 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (V / (δ * ε ^ 2))
  refine ⟨max 1 N₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_left 1 N₀) hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hquant := sum_typicalSeq_ge hp0 hp1 hnpos hε
  have hle : V / (n * ε ^ 2) ≤ δ := by
    have hthis : V / (δ * ε ^ 2) ≤ n :=
      le_trans hN₀ (by exact_mod_cast le_trans (le_max_right 1 N₀) hn)
    have hVn : V ≤ (n : ℝ) * (δ * ε ^ 2) :=
      calc V = V / (δ * ε ^ 2) * (δ * ε ^ 2) := (div_mul_cancel₀ V hden.ne').symm
        _ ≤ (n : ℝ) * (δ * ε ^ 2) := mul_le_mul_of_nonneg_right hthis hden.le
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * ε ^ 2)]
    nlinarith [hVn]
  linarith

/-- **Nielsen & Chuang, Theorem 12.2 (2), Nielsen–Chuang form** (Eq. 12.28). Fix `ε > 0`. For any
`δ > 0`, for all sufficiently large `n`, the number of `ε`-typical sequences satisfies
`(1 - δ) exp (n (H - ε)) ≤ |T(n, ε)| ≤ exp (n (H + ε))`. The upper bound holds for every `n`
(`card_typicalSeq_le`); the lower bound uses the large-`n` typicality probability
(`exists_le_sum_typicalSeq` feeding `card_typicalSeq_ge_of_le_sum`). -/
theorem exists_card_typicalSeq_bounds {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      (1 - δ) * Real.exp (n * (entropy p - ε)) ≤ ((typicalSeq p n ε).card : ℝ) ∧
        ((typicalSeq p n ε).card : ℝ) ≤ Real.exp (n * (entropy p + ε)) := by
  obtain ⟨N, hNpos, hN⟩ := exists_le_sum_typicalSeq hp0 hp1 hε hδ
  exact ⟨N, hNpos, fun n hn => ⟨card_typicalSeq_ge_of_le_sum (hN n hn),
    card_typicalSeq_le hp0 hp1⟩⟩

/-- **Weighted small-set bound** — the fractional-weight generalisation of the small-set bound
`exists_sum_prod_le_of_card_le_exp` (which is recovered from it below, at `0/1` indicator weights).
Fix a rate `R < entropy p`. For any `δ > 0`, for all sufficiently large `n`, *every* family of
weights `w : (Fin n → α) → ℝ` with `0 ≤ w s ≤ 1` and total weight `∑ s, w s ≤ exp (n R)` carries
weighted probability at most `δ`: `∑ s, w s * ∏ i, p (s i) ≤ δ`.

The fractional generality is what the *quantum* typical subspace theorem (Nielsen & Chuang, Theorem
12.5 (3)) needs: there the weights are the eigenbasis-diagonal matrix elements
`w κ = ⟨e_κ, S(n) e_κ⟩ ∈ [0, 1]` of an arbitrary projector `S(n)` of rank
`∑ κ, w κ = tr S(n) ≤ exp (n R)`, and `∑ κ, w κ · ∏ᵢ λ(κᵢ) = tr(S(n) ρ^⊗n)` is exactly its overlap
with the source `ρ^⊗n`.

The proof follows Nielsen & Chuang (`ε = (H - R)/2`), splitting the sum at the `ε`-typical set `T`:
the atypical part `∑_{s ∉ T} w s · ∏ p ≤ ∑_{s ∉ T} ∏ p ≤ δ/2` (weights `≤ 1`; part (1)); the typical
part `∑_{s ∈ T} w s · ∏ p ≤ (∑_{s ∈ T} w s) · exp(-n(H-ε)) ≤ exp(nR)·exp(-n(H-ε)) = exp(-nε) ≤ δ/2`
(each typical `∏ p ≤ exp(-n(H-ε))`; total weight `≤ exp(nR)`). -/
theorem exists_sum_weighted_prod_le_of_sum_le_exp {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) {R : ℝ} (hR : R < entropy p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ w : (Fin n → α) → ℝ, (∀ s, 0 ≤ w s) → (∀ s, w s ≤ 1) →
      ∑ s, w s ≤ Real.exp (n * R) → ∑ s, w s * ∏ i, p (s i) ≤ δ := by
  classical
  set H := entropy p with hH
  set ε := (H - R) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨N₁, hN₁pos, hN₁⟩ := exists_le_sum_typicalSeq hp0 hp1 hεpos hδ2
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (-Real.log (δ / 2) / ε)
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁pos (le_max_left _ _), fun n hn w hw0 hw1 hwsum => ?_⟩
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hnn : ∀ s : Fin n → α, (0 : ℝ) ≤ ∏ i, p (s i) := fun s => Finset.prod_nonneg fun i _ => hp0 _
  -- split the full sum at the `ε`-typical set `T`.
  have hsplit : ∑ s, w s * ∏ i, p (s i)
      = (∑ s ∈ typicalSeq p n ε, w s * ∏ i, p (s i))
        + ∑ s ∈ univ \ typicalSeq p n ε, w s * ∏ i, p (s i) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ (typicalSeq p n ε))]; ring
  -- atypical part: weights `≤ 1`, so bounded by the atypical mass `1 - ∑_T ≤ δ/2` (part (1)).
  have hatyp : ∑ s ∈ univ \ typicalSeq p n ε, w s * ∏ i, p (s i) ≤ δ / 2 := by
    have hsub : ∑ s ∈ univ \ typicalSeq p n ε, w s * ∏ i, p (s i)
        ≤ ∑ s ∈ univ \ typicalSeq p n ε, ∏ i, p (s i) := by
      exact Finset.sum_le_sum fun s _ => mul_le_of_le_one_left (hnn s) (hw1 s)
    have htotal : ∑ s : Fin n → α, ∏ i, p (s i) = 1 := by rw [iid_total_mass, hp1, one_pow]
    have hcompl : ∑ s ∈ univ \ typicalSeq p n ε, ∏ i, p (s i)
        + ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) = 1 := by
      rw [Finset.sum_sdiff (Finset.subset_univ _)]; exact htotal
    have hprob := hN₁ n hnN₁
    linarith
  -- typical part: each `∏ p ≤ exp(-n(H-ε))` and the total weight `≤ exp(nR)`.
  have htyp : ∑ s ∈ typicalSeq p n ε, w s * ∏ i, p (s i) ≤ δ / 2 := by
    have hmem : ∑ s ∈ typicalSeq p n ε, w s * ∏ i, p (s i)
        ≤ (∑ s ∈ typicalSeq p n ε, w s) * Real.exp (-(n : ℝ) * (H - ε)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun s hs => ?_
      exact mul_le_mul_of_nonneg_left (mem_typicalSeq.mp hs).2 (hw0 s)
    have hwt : (∑ s ∈ typicalSeq p n ε, w s) ≤ Real.exp (n * R) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun s _ _ => hw0 s)) hwsum
    have hcombine : Real.exp (n * R) * Real.exp (-(n : ℝ) * (H - ε))
        = Real.exp (-((n : ℝ) * ε)) := by
      rw [← Real.exp_add]; congr 1; rw [hε]; ring
    have hle : Real.exp (-((n : ℝ) * ε)) ≤ δ / 2 :=
      calc Real.exp (-((n : ℝ) * ε))
          ≤ Real.exp (Real.log (δ / 2)) := by
            refine Real.exp_le_exp.mpr ?_
            have h1 : -Real.log (δ / 2) / ε ≤ (n : ℝ) := le_trans hN₂ (by exact_mod_cast hnN₂)
            rw [div_le_iff₀ hεpos] at h1
            linarith
        _ = δ / 2 := Real.exp_log hδ2
    calc ∑ s ∈ typicalSeq p n ε, w s * ∏ i, p (s i)
        ≤ (∑ s ∈ typicalSeq p n ε, w s) * Real.exp (-(n : ℝ) * (H - ε)) := hmem
      _ ≤ Real.exp (n * R) * Real.exp (-(n : ℝ) * (H - ε)) :=
          mul_le_mul_of_nonneg_right hwt (Real.exp_pos _).le
      _ = Real.exp (-((n : ℝ) * ε)) := hcombine
      _ ≤ δ / 2 := hle
  rw [hsplit]; linarith

/-- **Nielsen & Chuang, Theorem 12.2 (3)** (Eq. 12.29, the small-set bound). Fix a rate `R` strictly
below the entropy (`R < entropy p`). For any `δ > 0`, for all sufficiently large `n`, *every*
collection `S` of length-`n` sequences with at most `exp (n R)` members carries total probability at
most `δ`: `∑ s ∈ S, ∏ i, p (s i) ≤ δ`. (In Nielsen & Chuang's base-`2` normalisation the size bound
reads `|S(n)| ≤ 2^{n R}`; here the entropy and the exponentials are in nats, the same statement
rescaled by `log 2`.)

The special case of the weighted bound `exists_sum_weighted_prod_le_of_sum_le_exp` at the `0/1`
indicator weight `w s = if s ∈ S then 1 else 0`, for which `∑ s, w s = |S| ≤ exp (n R)` and
`∑ s, w s · ∏ p = ∑_{s ∈ S} ∏ p`. -/
theorem exists_sum_prod_le_of_card_le_exp {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR : R < entropy p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ S : Finset (Fin n → α),
      (S.card : ℝ) ≤ Real.exp (n * R) → ∑ s ∈ S, ∏ i, p (s i) ≤ δ := by
  classical
  obtain ⟨N, hNpos, hN⟩ := exists_sum_weighted_prod_le_of_sum_le_exp hp0 hp1 hR hδ
  refine ⟨N, hNpos, fun n hn S hScard => ?_⟩
  -- `∑ s, (if s ∈ S then 1 else 0) = |S|`.
  have hcard : ∑ s, (if s ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Apply the weighted bound at the `0/1` indicator of `S`.
  have key := hN n hn (fun s => if s ∈ S then (1 : ℝ) else 0) (fun s => by positivity)
    (fun s => by split <;> norm_num) (by rw [hcard]; exact hScard)
  -- The weighted mass over the indicator is the plain mass over `S`.
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] using key

end Real
