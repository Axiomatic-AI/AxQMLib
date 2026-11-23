/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.NumberTheory.PerfectPower
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Concrete: factoring `91` by reduction to order-finding (`x = 4`)

Nielsen & Chuang, Exercise 5.18 (§5.3.2, p. 234): *"Factoring 91."* This works the reduction of
factoring to order-finding (the algorithm on p. 233–234, built on Theorems 5.2 and 5.3) on the
concrete input `N = 91`, with the random element `x = 4`. Each step of the algorithm is confirmed:

* **Step 1** ("if `N` is even return the factor `2`") is *passed*: `91` is odd.
* **Step 2** ("determine whether `N = aᵇ` for `a ≥ 1`, `b ≥ 2` and if so return `a`") is *passed*:
  `91` is not a perfect power. The predicate is `Nat.IsPerfectPower` — the decidable predicate of
  Exercise 5.17 — so this is exactly the check Step 2 performs.
* **Step 3** ("randomly choose `x`; if `gcd(x, N) > 1` return that factor") *produces* `x = 4`,
  since `gcd(4, 91) = 1`: `4` is co-prime to `91`, so Step 3 returns no factor and hands `x = 4` to
  the order-finding subroutine.
* **Step 4** (order-finding) computes the order `r = 6` of `4` modulo `91`. The order of `x`
  modulo `N` is the least positive `r` with `xʳ ≡ 1 (mod N)`, i.e. `orderOf (x : ZMod N)`.
  The residues run `4¹=4, 4²=16, 4³=64, 4⁴=74, 4⁵=23, 4⁶=1 (mod 91)`, so `r = 6`.
* **Step 5** succeeds because `r = 6` is *even* and `x^{r/2} = 4³ = 64 ≢ -1 (mod 91)`. Moreover
  `64² ≡ 1 (mod 91)` while `64 ≢ ±1 (mod 91)`, so `64` is a *non-trivial square root of `1`* — the
  situation Theorem 5.2 turns into a factor. Indeed `gcd(x^{r/2} - 1, N) = gcd(63, 91) = 7` and
  `gcd(x^{r/2} + 1, N) = gcd(65, 91) = 13` are the two prime factors, and `7 · 13 = 91`.

(The book prints `x^{r/2} mod 91 = 64 = -1 (mod 91)` and `gcd(64 - 1, 19) = 7`; both are typos — the
success condition is `64 ≠ -1 (mod 91)`, and the modulus is `91`, giving `gcd(64 - 1, 91) = 7`.
Because `64 < 91`, the natural-number value `4³ = 64` *is* the residue `x^{r/2} mod 91`, so the two
readings of `x^{r/2}` agree and the gcd is taken of the natural numbers `63` and `65` with `91`.)

These are explicit numerical facts about the specific input `N = 91`, `x = 4`. (Chapter 5's
quantum order-finding subroutine is what computes such an `r` efficiently; the arithmetic
verification here is pure number theory. This mirrors `AxQM.Concrete.orderOf_five_zmod_twentyOne`,
Exercise 5.10.)
-/

namespace AxQM.Concrete

/-- **Step 1 of the factoring algorithm passes for `N = 91`.** `91` is odd, so the "if `N` is even,
return the factor `2`" step returns no factor. -/
theorem ninetyOne_odd : Odd (91 : ℕ) := by decide

/-- **Step 2 of the factoring algorithm passes for `N = 91`.** `91` is not a perfect power `aᵇ`
(`a ≥ 1`, `b ≥ 2`), so the "if `N = aᵇ` return the base `a`" step returns no factor. The predicate
`Nat.IsPerfectPower` is precisely the property Step 2 decides (Exercise 5.17). -/
theorem ninetyOne_not_isPerfectPower : ¬ Nat.IsPerfectPower 91 := by decide

/-- **Step 3 of the factoring algorithm produces `x = 4` for `N = 91`.** `4` is co-prime to `91`
(`gcd(4, 91) = 1`), so the "if `gcd(x, N) > 1` return that factor" step returns no factor and hands
`x = 4` to the order-finding subroutine. -/
theorem four_coprime_ninetyOne : Nat.Coprime 4 91 := by decide

/-- **The order `r` of `4` modulo `91` is `6`** (Step 4, order-finding): `6` is the least positive
integer with `4⁶ ≡ 1 (mod 91)`, i.e. the multiplicative order of the residue `4` in `ZMod 91`.

Proved with `orderOf_eq_of_pow_and_pow_div_prime`: `4⁶ = 1 (mod 91)`, while for each prime `p ∣ 6`
(namely `p = 2, 3`) the proper power `4^(6/p)` is `4³ = 64` resp. `4² = 16`, neither of which is
`1`; hence no proper divisor of `6` is a period and the order is exactly `6`. -/
theorem orderOf_four_zmod_ninetyOne : orderOf (4 : ZMod 91) = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime
  · decide
  · intro p hp hpd
    have h2 := hp.two_le
    have h6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpd
    interval_cases p <;> revert hpd <;> decide

/-- The order `r = 6` of `4` modulo `91` is **even**, so `r / 2` is an integer — the first half of
the Step 5 success condition (`r` even and `x^{r/2} ≢ -1`). -/
theorem orderOf_four_zmod_ninetyOne_even : Even (orderOf (4 : ZMod 91)) := by
  rw [orderOf_four_zmod_ninetyOne]; decide

/-- **`x^{r/2} = 4³ = 64 (mod 91)`.** With `r = 6` the algorithm forms `x^{r/2}`; here it is the
residue `64`. -/
theorem four_pow_half_order_zmod_ninetyOne :
    (4 : ZMod 91) ^ (orderOf (4 : ZMod 91) / 2) = 64 := by
  rw [orderOf_four_zmod_ninetyOne]; decide

/-- **`x^{r/2}` is a square root of `1` modulo `91`:** `(4^{r/2})² = 4ʳ = 1 (mod 91)`. Together with
`four_pow_half_order_ne_one_zmod_ninetyOne` and `four_pow_half_order_ne_neg_one_zmod_ninetyOne` this
makes `64` a *non-trivial* square root of `1` — the input Theorem 5.2 needs to extract a factor. -/
theorem four_pow_half_order_sq_zmod_ninetyOne :
    ((4 : ZMod 91) ^ (orderOf (4 : ZMod 91) / 2)) ^ 2 = 1 := by
  rw [orderOf_four_zmod_ninetyOne]; decide

/-- `x^{r/2} = 64 ≢ 1 (mod 91)`: the square root of `1` found is not the trivial root `+1`. -/
theorem four_pow_half_order_ne_one_zmod_ninetyOne :
    (4 : ZMod 91) ^ (orderOf (4 : ZMod 91) / 2) ≠ 1 := by
  rw [orderOf_four_zmod_ninetyOne]; decide

/-- **Step 5 success condition:** `x^{r/2} = 64 ≢ -1 (mod 91)`. Since `r` is even
(`orderOf_four_zmod_ninetyOne_even`) and `x^{r/2} ≠ -1`, the algorithm succeeds rather than failing.
It is also `≠ 1`, so `64` is the promised non-trivial square root of `1`. -/
theorem four_pow_half_order_ne_neg_one_zmod_ninetyOne :
    (4 : ZMod 91) ^ (orderOf (4 : ZMod 91) / 2) ≠ -1 := by
  rw [orderOf_four_zmod_ninetyOne]; decide

/-- **The factor from `gcd(x^{r/2} - 1, N)`.** `gcd(4³ - 1, 91) = gcd(63, 91) = 7`, a non-trivial
factor of `91` (Theorem 5.2 applied to the non-trivial square root `64`). -/
theorem gcd_four_pow_half_order_pred_ninetyOne :
    Nat.gcd (4 ^ (orderOf (4 : ZMod 91) / 2) - 1) 91 = 7 := by
  rw [orderOf_four_zmod_ninetyOne]; decide

/-- **The factor from `gcd(x^{r/2} + 1, N)`.** `gcd(4³ + 1, 91) = gcd(65, 91) = 13`, the
complementary non-trivial factor of `91`. -/
theorem gcd_four_pow_half_order_succ_ninetyOne :
    Nat.gcd (4 ^ (orderOf (4 : ZMod 91) / 2) + 1) 91 = 13 := by
  rw [orderOf_four_zmod_ninetyOne]; decide

/-- The two factors the algorithm recovers multiply back to `N`: `7 · 13 = 91`. Hence both `7` and
`13` are genuine non-trivial factors (each strictly between `1` and `91` and dividing `91`), i.e.
the reduction of factoring to order-finding has recovered the complete prime factorization of
`91`. -/
theorem seven_mul_thirteen_eq_ninetyOne : (7 : ℕ) * 13 = 91 := by decide

end AxQM.Concrete
