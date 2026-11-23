/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Combinatorics.Enumerative.PowersetCardInter
public import ToMathlib.InformationTheory.Coding.BinomialEntropyBound
public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropyQuadraticBound
public import Mathlib.Data.Nat.Choose.Central

/-!
# An exponential tail bound for the random-sampling error test

Fix a ground set `S` of `2 * n` bits and an error set `E ⊆ S` (`|E| = M` errors). A random
`n`-element subset `C ⊆ S` is used as *check bits*; the *uniform-sampling probability* that fewer
than `s` of the errors land on the check bits is

`p := #{C ∈ S.powersetCard n | (C ∩ E).card < s} / (2 * n).choose n`,

the left tail of the hypergeometric distribution `Hypergeometric (2 * n) M n`. This file bounds `p`
and shows it decays exponentially once the threshold `s` sits below the mode `M / 2`.

## Main results

* `Finset.card_powersetCard_filter_inter_lt_div_choose_le`: the *entropy form*,
  `p ≤ (2 * n + 1) * 2 ^ (-M * (1 - H₂ ((s - 1) / M)))`, where `H₂ = Real.binEntropyBit`. This is
  the assembly of the counting inequality `Finset.card_powersetCard_filter_inter_lt_le` with the
  Hamming-ball entropy bound `sum_range_choose_le_rpow_mul_binEntropyBit` and the central-binomial
  lower bound `Nat.four_pow_le_two_mul_add_one_mul_central_binom`.
* `Finset.card_powersetCard_filter_inter_lt_div_choose_le_two_pow`: the *Gaussian tail form*,
  `p ≤ (2 * n + 1) * 2 ^ (-ε² * n / 4)`, valid whenever the deficit `M - 2 (s - 1)` of the
  threshold below the mode is at least `ε * n`. Obtained from the entropy form by the quadratic
  entropy bound `Real.binEntropyBit_le_one_sub_two_mul_sq`, `1 - H₂ x ≥ 2 (x - ½) ^ 2`.
* `Finset.card_powersetCard_filter_inter_lt_and_lt_div_choose_le_two_pow`: the same exponential
  bound for the full event `{(C ∩ E).card < s ∧ t < (E \ C).card}` — few errors on the check bits
  *and* many on the untested rest — obtained by discarding the (implied) second conjunct.

This is the analytic heart of Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.27 (random sampling tests) in the BB84 quantum key distribution security analysis: with
`M = μ n` errors and check-threshold `s = δ n`, the deficit `M - 2 (s - 1) = ε n + 2 ≥ ε n`
(N&C's `δ = (μ - ε) / 2`), so the probability of seeing `< δ n` errors on the checks yet
`> (δ + ε) n` on the rest is `≤ (2 n + 1) * 2 ^ (-ε² n / 4) = exp[-O(ε² n)]`.
-/

open Finset

namespace Finset

public section

variable {α : Type*} [DecidableEq α]

/-- **Entropy form of the random-sampling tail bound.** For a ground set `S` of `2 * n` bits, an
error set `E ⊆ S` with `M := E.card`, and a check-threshold `s ≥ 1` sitting at or below the mode
(`2 (s - 1) ≤ M`), the fraction of `n`-subsets `C ⊆ S` meeting `E` in fewer than `s` elements is
bounded by `(2 n + 1) * 2 ^ (-M * (1 - H₂ ((s - 1) / M)))`, where `H₂ = Real.binEntropyBit`.

Assembled from the counting inequality `card_powersetCard_filter_inter_lt_le`
(`badCount ≤ (∑_{j < s} C(M, j)) * 2 ^ (2 n - M)`), the Hamming-ball entropy bound
`sum_range_choose_le_rpow_mul_binEntropyBit` (`∑_{j < s} C(M, j) ≤ 2 ^ (M * H₂ ((s - 1) / M))`),
and the central-binomial lower bound `four_pow_le_two_mul_add_one_mul_central_binom`
(`(2 n).choose n ≥ 2 ^ (2 n) / (2 n + 1)`). This is Nielsen & Chuang, Exercise 12.27, steps
(1)–(2) (eqs 12.186–12.187). -/
theorem card_powersetCard_filter_inter_lt_div_choose_le {n : ℕ} (S E : Finset α) (s : ℕ)
    (hS : S.card = 2 * n) (hE : E ⊆ S) (hs : 1 ≤ s) (hs2 : 2 * (s - 1) ≤ E.card) :
    (((S.powersetCard n).filter (fun C => (C ∩ E).card < s)).card : ℝ) / ((2 * n).choose n)
      ≤ (2 * n + 1) *
        (2 : ℝ) ^ (-(E.card : ℝ) * (1 - Real.binEntropyBit (((s - 1 : ℕ) : ℝ) / E.card))) := by
  have hM2n : E.card ≤ 2 * n := hS ▸ Finset.card_le_card hE
  have hCpos : (0 : ℝ) < ((2 * n).choose n) := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)
  set bad := ((S.powersetCard n).filter (fun C => (C ∩ E).card < s)).card with hbad
  set H : ℝ := Real.binEntropyBit (((s - 1 : ℕ) : ℝ) / E.card) with hH
  -- Step A + B: the numerator (as a real) is bounded by `2 ^ (M * H + (2 n - M))`.
  have hbadR : (bad : ℝ) ≤ (2 : ℝ) ^ ((E.card : ℝ) * H + ((2 * n : ℝ) - E.card)) := by
    have hcount : bad ≤ (∑ j ∈ Finset.range s, (E.card).choose j) * 2 ^ (S \ E).card :=
      Finset.card_powersetCard_filter_inter_lt_le S E n s
    have hsdiff : (S \ E).card = 2 * n - E.card := by rw [Finset.card_sdiff_of_subset hE, hS]
    rw [hsdiff] at hcount
    have hcountR : (bad : ℝ)
        ≤ (∑ j ∈ Finset.range s, ((E.card).choose j : ℝ)) * (2 : ℝ) ^ (2 * n - E.card) := by
      exact_mod_cast hcount
    have hsum : (∑ j ∈ Finset.range s, ((E.card).choose j : ℝ))
        ≤ (2 : ℝ) ^ ((E.card : ℝ) * H) := by
      rw [show s = (s - 1) + 1 by omega]
      exact sum_range_choose_le_rpow_mul_binEntropyBit hs2
    calc (bad : ℝ)
        ≤ (∑ j ∈ Finset.range s, ((E.card).choose j : ℝ)) * (2 : ℝ) ^ (2 * n - E.card) := hcountR
      _ ≤ (2 : ℝ) ^ ((E.card : ℝ) * H) * (2 : ℝ) ^ (2 * n - E.card) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = (2 : ℝ) ^ ((E.card : ℝ) * H) * (2 : ℝ) ^ (((2 * n - E.card : ℕ) : ℝ)) := by
          rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((E.card : ℝ) * H + ((2 * n : ℝ) - E.card)) := by
          rw [← Real.rpow_add (by norm_num), Nat.cast_sub hM2n]; push_cast; ring_nf
  -- Central-binomial lower bound: `2 ^ (2 n) ≤ (2 n + 1) * (2 n).choose n`.
  have hCbound : (2 : ℝ) ^ ((2 * n : ℝ)) ≤ (2 * n + 1) * ((2 * n).choose n) := by
    have h : 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n := by
      simpa [Nat.centralBinom_eq_two_mul_choose] using
        Nat.four_pow_le_two_mul_add_one_mul_centralBinom n
    have hR : (4 : ℝ) ^ n ≤ (2 * n + 1) * ((2 * n).choose n) := by exact_mod_cast h
    calc (2 : ℝ) ^ ((2 * n : ℝ))
        = (4 : ℝ) ^ n := by
          rw [show ((2 * n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
      _ ≤ (2 * n + 1) * ((2 * n).choose n) := hR
  -- Combine.
  rw [div_le_iff₀ hCpos]
  calc (bad : ℝ)
      ≤ (2 : ℝ) ^ ((E.card : ℝ) * H + ((2 * n : ℝ) - E.card)) := hbadR
    _ = (2 : ℝ) ^ (-(E.card : ℝ) * (1 - H)) * (2 : ℝ) ^ ((2 * n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    _ ≤ (2 : ℝ) ^ (-(E.card : ℝ) * (1 - H)) * ((2 * n + 1) * ((2 * n).choose n)) :=
        mul_le_mul_of_nonneg_left hCbound (Real.rpow_nonneg (by norm_num) _)
    _ = (2 * n + 1) * (2 : ℝ) ^ (-(E.card : ℝ) * (1 - H)) * ((2 * n).choose n) := by ring

/-- **Gaussian tail form of the random-sampling error bound** (Nielsen & Chuang, Exercise 12.27,
final result). With the hypotheses of `card_powersetCard_filter_inter_lt_div_choose_le`, if the
threshold `s` sits below the mode `M / 2` by a deficit of at least `ε n`
(`ε * n ≤ M - 2 (s - 1)`, with `ε ≥ 0`), then the sampling probability decays like a Gaussian tail,
`p ≤ (2 n + 1) * 2 ^ (-ε² n / 4)`, the explicit form of `exp[-O(ε² n)]`.

Obtained from the entropy form via the quadratic entropy bound
`Real.binEntropyBit_le_one_sub_two_mul_sq`: `1 - H₂ x ≥ 2 (x - ½) ^ 2` with `x = (s - 1) / M` gives
`M (1 - H₂ x) ≥ (M - 2 (s - 1)) ^ 2 / (2 M) ≥ (ε n) ^ 2 / (4 n) = ε² n / 4`, using `M ≤ 2 n`. -/
theorem card_powersetCard_filter_inter_lt_div_choose_le_two_pow {n : ℕ} (S E : Finset α) (s : ℕ)
    (ε : ℝ) (hS : S.card = 2 * n) (hE : E ⊆ S) (hs : 1 ≤ s) (hε : 0 ≤ ε)
    (hgap : ε * n ≤ (E.card : ℝ) - 2 * ((s - 1 : ℕ) : ℝ)) :
    (((S.powersetCard n).filter (fun C => (C ∩ E).card < s)).card : ℝ) / ((2 * n).choose n)
      ≤ (2 * n + 1) * (2 : ℝ) ^ (-(ε ^ 2 * n) / 4) := by
  have hM2n : E.card ≤ 2 * n := hS ▸ Finset.card_le_card hE
  have hMn : (E.card : ℝ) ≤ 2 * n := by exact_mod_cast hM2n
  have hεn : (0 : ℝ) ≤ ε * n := by positivity
  have hdef : (0 : ℝ) ≤ (E.card : ℝ) - 2 * ((s - 1 : ℕ) : ℝ) := le_trans hεn hgap
  have hs2 : 2 * (s - 1) ≤ E.card := by
    have h : (2 * ((s - 1 : ℕ) : ℝ)) ≤ (E.card : ℝ) := by linarith
    exact_mod_cast h
  -- The key exponent inequality `ε² n / 4 ≤ M (1 - H₂ ((s - 1) / M))`.
  have hexp : ε ^ 2 * n / 4
      ≤ (E.card : ℝ) * (1 - Real.binEntropyBit (((s - 1 : ℕ) : ℝ) / E.card)) := by
    rcases Nat.eq_zero_or_pos E.card with hM0 | hMpos
    · -- No errors: `s = 1`, the deficit is `0`, forcing `ε n = 0` and hence `ε² n = 0`.
      have hs10 : s - 1 = 0 := by omega
      have hupper : ε * n ≤ 0 := by
        have hz : (E.card : ℝ) - 2 * ((s - 1 : ℕ) : ℝ) = 0 := by rw [hM0, hs10]; norm_num
        exact hgap.trans_eq hz
      have hεn0 : ε * n = 0 := le_antisymm hupper hεn
      have hε2n : ε ^ 2 * n = 0 := by rw [pow_two, mul_assoc, hεn0, mul_zero]
      rw [hM0]; simp only [Nat.cast_zero, zero_mul]; linarith [hε2n]
    · have hMR : (0 : ℝ) < E.card := by exact_mod_cast hMpos
      have hMne : (E.card : ℝ) ≠ 0 := hMR.ne'
      set x : ℝ := ((s - 1 : ℕ) : ℝ) / E.card with hx
      have hx0 : 0 ≤ x := by rw [hx]; positivity
      have hx1 : x ≤ 1 := by
        rw [hx, div_le_one hMR]
        have : (2 * ((s - 1 : ℕ) : ℝ)) ≤ (E.card : ℝ) := by exact_mod_cast hs2
        linarith
      have hHle : Real.binEntropyBit x ≤ 1 - 2 * (x - 2⁻¹) ^ 2 :=
        Real.binEntropyBit_le_one_sub_two_mul_sq hx0 hx1
      -- `M x = s - 1`, so `M (x - ½) = (s - 1) - M / 2` and `2 M (x - ½)² = (2(s-1) - M)² / (2M)`.
      have hMx0 : (E.card : ℝ) * x = ((s - 1 : ℕ) : ℝ) := by rw [hx]; field_simp
      have hMxh : (E.card : ℝ) * (x - 2⁻¹) = ((s - 1 : ℕ) : ℝ) - (E.card : ℝ) * 2⁻¹ := by
        rw [mul_sub, hMx0]
      have hval : 2 * (E.card : ℝ) * (x - 2⁻¹) ^ 2
          = 2 * (((s - 1 : ℕ) : ℝ) - (E.card : ℝ) * 2⁻¹) ^ 2 / E.card := by
        rw [eq_div_iff hMne, ← hMxh]; ring
      -- `ε² n / 4 ≤ 2 M (x - ½)²`, after clearing the `x` denominator.
      have hlow : ε ^ 2 * n / 4 ≤ 2 * (E.card : ℝ) * (x - 2⁻¹) ^ 2 := by
        rw [hval, le_div_iff₀ hMR]
        nlinarith [hgap, hεn, hMn,
          mul_nonneg (show (0 : ℝ) ≤ (E.card : ℝ) - 2 * ((s - 1 : ℕ) : ℝ) - ε * n by linarith)
            (show (0 : ℝ) ≤ (E.card : ℝ) - 2 * ((s - 1 : ℕ) : ℝ) + ε * n by linarith),
          mul_nonneg (show (0 : ℝ) ≤ ε ^ 2 * n by positivity)
            (show (0 : ℝ) ≤ 2 * n - (E.card : ℝ) by linarith)]
      -- `2 M (x - ½)² ≤ M (1 - H₂ x)`.
      have hquad : 2 * (E.card : ℝ) * (x - 2⁻¹) ^ 2
          ≤ (E.card : ℝ) * (1 - Real.binEntropyBit x) := by
        nlinarith [mul_nonneg hMR.le
          (show (0 : ℝ) ≤ (1 - Real.binEntropyBit x) - 2 * (x - 2⁻¹) ^ 2 by linarith)]
      calc ε ^ 2 * n / 4 ≤ 2 * (E.card : ℝ) * (x - 2⁻¹) ^ 2 := hlow
        _ ≤ (E.card : ℝ) * (1 - Real.binEntropyBit x) := hquad
  -- Assemble: entropy form, then monotonicity of `2 ^ ·`.
  refine le_trans (card_powersetCard_filter_inter_lt_div_choose_le S E s hS hE hs hs2) ?_
  have hmono : (2 : ℝ) ^ (-(E.card : ℝ) * (1 - Real.binEntropyBit (((s - 1 : ℕ) : ℝ) / E.card)))
      ≤ (2 : ℝ) ^ (-(ε ^ 2 * n) / 4) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [hexp]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **Random-sampling error bound for the full BB84 test event** (Nielsen & Chuang, Exercise
12.27). The exponential bound `p ≤ (2 n + 1) * 2 ^ (-ε² n / 4)` holds for the full event of the
exercise — *fewer than `s` errors on the check bits `C`* **and** *more than `t` errors on the
untested rest `S \ C`* — since that event is contained in `{(C ∩ E).card < s}` (the second conjunct
is discarded).

Here `(E \ C).card` counts errors on the untested bits `S \ C` (as `E ⊆ S`), matching N&C's
"`> (δ + ε) n` errors on the remaining `n` bits". -/
theorem card_powersetCard_filter_inter_lt_and_lt_div_choose_le_two_pow {n : ℕ} (S E : Finset α)
    (s t : ℕ) (ε : ℝ) (hS : S.card = 2 * n) (hE : E ⊆ S) (hs : 1 ≤ s) (hε : 0 ≤ ε)
    (hgap : ε * n ≤ (E.card : ℝ) - 2 * ((s - 1 : ℕ) : ℝ)) :
    (((S.powersetCard n).filter
        (fun C => (C ∩ E).card < s ∧ t < (E \ C).card)).card : ℝ) / ((2 * n).choose n)
      ≤ (2 * n + 1) * (2 : ℝ) ^ (-(ε ^ 2 * n) / 4) := by
  refine le_trans ?_
    (card_powersetCard_filter_inter_lt_div_choose_le_two_pow S E s ε hS hE hs hε hgap)
  have hsub : (S.powersetCard n).filter (fun C => (C ∩ E).card < s ∧ t < (E \ C).card)
      ⊆ (S.powersetCard n).filter (fun C => (C ∩ E).card < s) := by
    intro C hC
    rw [Finset.mem_filter] at hC ⊢
    exact ⟨hC.1, hC.2.1⟩
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast Finset.card_le_card hsub

end

end Finset
