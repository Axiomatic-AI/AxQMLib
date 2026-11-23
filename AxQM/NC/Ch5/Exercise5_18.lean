/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Factoring91

/-!
# Nielsen & Chuang, Exercise 5.18 (Factoring 91)

Factoring 91: with x=4, compute order r, show x^{r/2} mod 91 != -1, gcd(64-1,91)=7.

*(N&C p. 234, §5.3.2 — the reduction of factoring to order-finding
worked on the concrete input `N = 91`, `x = 4`.)*

This is an explicit numerical trace of the classical factoring algorithm
(p. 233–234, based on Theorems 5.2 and 5.3) on a specific composite: the parity, perfect-power,
coprimality, multiplicative-order and gcd computations for `N = 91`, `x = 4`. Compare the
numerical Exercise 5.10 (`orderOf_five_zmod_twentyOne`).

## What is formalised, and where

The formalisation is in `AxQM/Concrete/Factoring91.lean` (namespace
`AxQM.Concrete`), one declaration per step of the algorithm:

* `ninetyOne_odd` — **Step 1** passes: `91` is odd (not even), so it does not return the factor `2`.
* `ninetyOne_not_isPerfectPower` — **Step 2** passes: `¬ Nat.IsPerfectPower 91`, so `91` is not
  `aᵇ` (`a ≥ 1`, `b ≥ 2`) and no base is returned. (`Nat.IsPerfectPower` is the decidable predicate
  of Exercise 5.17 — exactly the property Step 2 tests.)
* `four_coprime_ninetyOne` — **Step 3** produces `x = 4`: `Nat.Coprime 4 91`, so `gcd(4, 91) = 1`
  and Step 3 returns no factor.
* `orderOf_four_zmod_ninetyOne` — **Step 4**: `orderOf (4 : ZMod 91) = 6`, i.e. the order of `4`
  modulo `91` is `r = 6`.
* `orderOf_four_zmod_ninetyOne_even` — `r = 6` is even, the first half of the Step 5 success gate.
* `four_pow_half_order_zmod_ninetyOne` — `x^{r/2} = 4³ = 64 (mod 91)`.
* `four_pow_half_order_sq_zmod_ninetyOne`, `four_pow_half_order_ne_one_zmod_ninetyOne`,
  `four_pow_half_order_ne_neg_one_zmod_ninetyOne` — `64` is a *non-trivial square root of `1`*:
  `64² ≡ 1` while `64 ≢ 1` and `64 ≢ -1 (mod 91)`. The last is the **Step 5 success condition**
  `x^{r/2} ≢ -1`, and the trio is exactly the hypothesis of Theorem 5.2.
* `gcd_four_pow_half_order_pred_ninetyOne` — `gcd(x^{r/2} - 1, N) = gcd(63, 91) = 7`, the
  non-trivial factor the exercise asks for.
* `gcd_four_pow_half_order_succ_ninetyOne` — `gcd(x^{r/2} + 1, N) = gcd(65, 91) = 13`, the
  complementary factor.
* `seven_mul_thirteen_eq_ninetyOne` — `7 · 13 = 91`, confirming both gcd outputs are genuine
  non-trivial factors whose product is `N`.

## Two fidelity points

* **Book typos.** N&C prints the success line as `x^{r/2} mod 91 = 64 = -1 (mod 91)` and the factor
  as `gcd(64 - 1, 19) = 7`. Both are typos: the *success* condition is `64 ≠ -1 (mod 91)` (captured
  by `four_pow_half_order_ne_neg_one_zmod_ninetyOne`), and the modulus is `91`, giving
  `gcd(64 - 1, 91) = 7`. The formalisation states the corrected claims.
* **`x^{r/2}` representative.** Because `4³ = 64 < 91`, the natural-number value `4^{r/2}` already
  equals the residue `x^{r/2} mod 91`, so the gcd is taken of the naturals `63`, `65` against `91`,
  matching the book verbatim.
-/
