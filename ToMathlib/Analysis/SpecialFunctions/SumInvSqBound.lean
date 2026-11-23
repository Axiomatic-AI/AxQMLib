/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Data.Nat.Prime.Defs

/-! # An integral bound on `∑ 1/q²` over the integers `≥ 2` and over the primes

This file records an elementary integral-comparison bound on the tail of the series `∑ 1/q²`.
The key inequality is that, for `x ≥ 2`,
`2 / (3 x²) ≤ ∫_x^{x+1} 1/y² dy`,
which, summed against the telescoping value `∫_2^∞ 1/y² dy = 1/2`, yields
`∑_{q ≥ 2} 1/q² ≤ (3/2) ∫_2^∞ 1/y² dy = 3/4`,
and hence the same bound for the sub-sum over the primes.

This is Exercise 5.16 of Nielsen & Chuang, *Quantum Computation and Quantum Information* (p. 231),
where the prime version is used to show that the order-finding "third method" succeeds with
probability at least `1/4` (their eq. (5.58)): with `p(q ∣ s) ≤ 1/q` one has
`1 - ∑_q p(q ∣ s'₁) p(q ∣ s'₂) ≥ 1 - ∑_q 1/q² ≥ 1 - 3/4 = 1/4`, the sum ranging over primes `q`.
The content here is the purely analytic bound `∑_q 1/q² ≤ 3/4`; the probabilistic step
`p(q ∣ s) ≤ 1/q` belongs to the surrounding text, not to this exercise.

## Main statements

* `integral_one_div_sq`: `∫_a^b 1/y² dy = 1/a - 1/b` for `0 < a`, `0 < b`.
* `two_div_three_mul_sq_le_integral_one_div_sq`: for `x ≥ 2`, `2/(3 x²) ≤ ∫_x^{x+1} 1/y² dy`
  (the exercise's first claim; equality holds at `x = 2`).
* `integral_Ioi_one_div_sq_two`: `∫_2^∞ 1/y² dy = 1/2`.
* `sum_one_div_sq_le_of_two_le`: any finite set of integers `≥ 2` has `∑ 1/n² ≤ 3/4`.
* `tsum_one_div_sq_two_le`: `∑_{n ≥ 2} 1/n² ≤ 3/4`.
* `Nat.Primes.tsum_one_div_sq_le`: `∑_{p prime} 1/p² ≤ 3/4` (the version used for N&C eq. (5.58)).

## Implementation notes

The finite integral `∫_a^b 1/y²` is computed by rewriting the integrand `1/y²` as the integer
power `y^(-2 : ℤ)` (they agree pointwise, even at `y = 0`) and applying `integral_zpow`. The
improper integral `∫_2^∞ 1/y²` instead rewrites `1/y²` as the real power `y^(-2 : ℝ)` on `Ioi 2`
(where `y > 0`) and applies `integral_Ioi_rpow_of_lt`. The tail bound is obtained without any
improper integral: the per-integer bound is summed over `Finset.Ico 2 N` via
`intervalIntegral.sum_integral_adjacent_intervals_Ico`, giving `∑_{Ico 2 N} 1/n² ≤ (3/2)(1/2 - 1/N)
≤ 3/4` uniformly in `N`; the two infinite-sum statements then follow from `Real.tsum_le_of_sum_le`
applied to the subtype of integers `≥ 2` and to `Nat.Primes` respectively (every prime is `≥ 2`).
-/

open scoped MeasureTheory
open intervalIntegral

@[expose] public section

/-- The definite integral of `1/y²` over `[a, b]`, for `0 < a` and `0 < b`, is `1/a - 1/b`. -/
theorem integral_one_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ y in a..b, 1 / y ^ 2 = 1 / a - 1 / b := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  have hfun : (fun y : ℝ => 1 / y ^ 2) = (fun y => y ^ (-2 : ℤ)) := by
    funext y; rw [zpow_neg, one_div, zpow_two, sq]
  rw [hfun, integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num; field_simp; ring

/-- The interval integrand `1/y²` is interval integrable on `[a, b]` whenever `0 ∉ [a, b]`
(so the integrand is continuous there). -/
theorem intervalIntegrable_one_div_sq {a b : ℝ} (h : (0 : ℝ) ∉ Set.uIcc a b) :
    IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const ((continuous_pow 2).continuousOn)
  intro y hy
  exact pow_ne_zero 2 (fun hy0 => h (hy0 ▸ hy))

/-- **Nielsen & Chuang, Exercise 5.16 (first claim).** For every `x ≥ 2`,
`2 / (3 x²) ≤ ∫_x^{x+1} 1/y² dy`. The left-hand side is a lower bound for the exact value
`1/x - 1/(x+1) = 1/(x(x+1))` of the integral, with equality at `x = 2`. -/
theorem two_div_three_mul_sq_le_integral_one_div_sq {x : ℝ} (hx : 2 ≤ x) :
    2 / (3 * x ^ 2) ≤ ∫ y in x..(x + 1), 1 / y ^ 2 := by
  have hx0 : 0 < x := by linarith
  rw [integral_one_div_sq hx0 (by linarith)]
  have key : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by field_simp; ring
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (le_of_lt hx0) (by linarith : (0 : ℝ) ≤ x - 2)]

/-- The improper integral `∫_2^∞ 1/y² dy = 1/2`. Multiplying by `3/2` gives the value `3/4`
appearing in Nielsen & Chuang's Exercise 5.16. -/
theorem integral_Ioi_one_div_sq_two : ∫ y in Set.Ioi (2 : ℝ), 1 / y ^ 2 = 1 / 2 := by
  have hcong : ∫ y in Set.Ioi (2 : ℝ), 1 / y ^ 2 = ∫ y in Set.Ioi (2 : ℝ), y ^ (-2 : ℝ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : (0 : ℝ) < y := by simp only [Set.mem_Ioi] at hy; linarith
    simp only [Real.rpow_neg hy0.le, Real.rpow_two, one_div, sq]
  rw [hcong, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The partial sum `∑_{n = 2}^{N-1} 1/n²` is bounded by `3/4`, uniformly in `N`. This is the
integral-comparison heart of Nielsen & Chuang's Exercise 5.16: each term satisfies
`1/n² ≤ (3/2) ∫_n^{n+1} 1/y² dy`, and the interval integrals telescope to
`∫_2^N 1/y² dy = 1/2 - 1/N ≤ 1/2`. -/
theorem sum_Ico_one_div_sq_le (N : ℕ) : ∑ n ∈ Finset.Ico 2 N, 1 / (n : ℝ) ^ 2 ≤ 3 / 4 := by
  rcases lt_or_ge N 2 with hN | hN
  · rw [Finset.Ico_eq_empty (by omega)]; norm_num
  have hterm : ∀ n ∈ Finset.Ico 2 N,
      (1 : ℝ) / (n : ℝ) ^ 2 ≤ (3 / 2) * ∫ y in (n : ℝ)..((n : ℝ) + 1), 1 / y ^ 2 := by
    intro n hn
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hn).1
    have hb := two_div_three_mul_sq_le_integral_one_div_sq h2
    have heq : (3 : ℝ) / 2 * (2 / (3 * (n : ℝ) ^ 2)) = 1 / (n : ℝ) ^ 2 := by
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      field_simp
    calc (1 : ℝ) / (n : ℝ) ^ 2 = (3 / 2) * (2 / (3 * (n : ℝ) ^ 2)) := heq.symm
      _ ≤ (3 / 2) * ∫ y in (n : ℝ)..((n : ℝ) + 1), 1 / y ^ 2 :=
          mul_le_mul_of_nonneg_left hb (by norm_num)
  have hint : ∀ k ∈ Set.Ico 2 N, IntervalIntegrable (fun y : ℝ => 1 / y ^ 2)
      MeasureTheory.volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    refine intervalIntegrable_one_div_sq (Set.notMem_uIcc_of_lt ?_ ?_)
    · linarith
    · push_cast; linarith
  calc ∑ n ∈ Finset.Ico 2 N, (1 : ℝ) / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Ico 2 N, (3 / 2) * ∫ y in (n : ℝ)..((n : ℝ) + 1), 1 / y ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (3 / 2) * ∑ n ∈ Finset.Ico 2 N, ∫ y in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), 1 / y ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; push_cast; ring_nf
    _ = (3 / 2) * ∫ y in ((2 : ℕ) : ℝ)..((N : ℕ) : ℝ), 1 / y ^ 2 := by
        rw [sum_integral_adjacent_intervals_Ico hN hint]
    _ = (3 / 2) * (1 / 2 - 1 / (N : ℝ)) := by
        have hNpos : (0 : ℝ) < (N : ℝ) := by
          have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        rw [Nat.cast_ofNat, integral_one_div_sq (by norm_num) hNpos]
    _ ≤ 3 / 4 := by
        have h1 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        nlinarith

/-- Any finite set `s` of natural numbers all `≥ 2` satisfies `∑_{n ∈ s} 1/n² ≤ 3/4`.
Every such `s` is contained in some `Finset.Ico 2 N`, so this follows from
`sum_Ico_one_div_sq_le` by monotonicity of the sum over supersets of nonnegative terms. -/
theorem sum_one_div_sq_le_of_two_le (s : Finset ℕ) (hs : ∀ n ∈ s, 2 ≤ n) :
    ∑ n ∈ s, 1 / (n : ℝ) ^ 2 ≤ 3 / 4 := by
  have hsub : s ⊆ Finset.Ico 2 (s.sup id + 1) := by
    intro n hn
    rw [Finset.mem_Ico]
    exact ⟨hs n hn, Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  calc ∑ n ∈ s, 1 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Ico 2 (s.sup id + 1), 1 / (n : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ 3 / 4 := sum_Ico_one_div_sq_le _

/-- If `f : ι → ℕ` is injective with every value `≥ 2`, then `∑_i 1/(f i)² ≤ 3/4`.
This packages the passage from the finite-set bound `sum_one_div_sq_le_of_two_le` to an infinite
sum via `Real.tsum_le_of_sum_le`: on each finite `u`, the sum is `∑_{m ∈ u.image f} 1/m²`, which is
`≤ 3/4` because `u.image f` is a finite set of integers `≥ 2`. -/
theorem tsum_one_div_sq_le_of_two_le {ι : Type*} (f : ι → ℕ) (hf : Function.Injective f)
    (h2 : ∀ i, 2 ≤ f i) : ∑' i, 1 / ((f i : ℕ) : ℝ) ^ 2 ≤ 3 / 4 := by
  refine Real.tsum_le_of_sum_le (fun i => by positivity) (fun u => ?_)
  have h := sum_one_div_sq_le_of_two_le (u.image f)
    (by intro m hm; rw [Finset.mem_image] at hm; obtain ⟨i, _, rfl⟩ := hm; exact h2 i)
  rwa [Finset.sum_image (fun x _ y _ hxy => hf hxy)] at h

/-- **Nielsen & Chuang, Exercise 5.16 (second claim, integer form).**
`∑_{n ≥ 2} 1/n² ≤ 3/4`, the sum ranging over all integers `≥ 2`. -/
theorem tsum_one_div_sq_two_le : ∑' n : {n : ℕ // 2 ≤ n}, 1 / ((n : ℕ) : ℝ) ^ 2 ≤ 3 / 4 :=
  tsum_one_div_sq_le_of_two_le Subtype.val Subtype.val_injective (fun n => n.2)

/-- **Nielsen & Chuang, Exercise 5.16 (second claim, prime form).**
`∑_{p prime} 1/p² ≤ 3/4`. This is the version used in N&C to bound the failure probability in
eq. (5.58): every prime is `≥ 2`, so the sum over the primes is dominated by the sum over the
integers `≥ 2`. -/
theorem Nat.Primes.tsum_one_div_sq_le : ∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ 2 ≤ 3 / 4 :=
  tsum_one_div_sq_le_of_two_le Subtype.val Subtype.val_injective (fun p => p.2.two_le)

end
