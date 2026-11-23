/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.NumberTheory.NontrivialSqrtOne

/-!
# Nielsen & Chuang, Theorem 5.2 (a factor from a nontrivial square root of one)

For nontrivial x with x^2=1 mod N, at least one of gcd(x-1,N), gcd(x+1,N) is a nontrivial factor of
N.

This is the *first step* of N&C's reduction of factoring to order-finding (§5.3.2): a nontrivial
square root of one modulo `N` hands over a nontrivial factor of `N`. (The companion probabilistic
step — that a random `y` coprime to `N` likely has even order `r` with `y^{r/2} ≢ ±1` — is
Theorem 5.3.)

## What is formalised, and where

The formalisation is in `ToMathlib/NumberTheory/NontrivialSqrtOne.lean`:

* `Nat.IsNontrivialFactor` — `d` is a nontrivial factor of `n` (`d ∣ n` with `1 < d < n`).
* `Nat.isNontrivialFactor_iff_mem_properDivisors` — the `Nat.properDivisors` spelling: `d` is a
  nontrivial factor of `n` iff it is a proper divisor of `n` greater than `1`.
* `Nat.isNontrivialFactor_gcd_of_dvd_mul` — the reusable core: if `n ∣ a * b` yet `n` divides
  neither `a` nor `b`, then `gcd(a, n)` is a nontrivial factor of `n`.
* `Nat.isNontrivialFactor_gcd_sub_one_of_dvd_sq_sub_one` and
  `Nat.isNontrivialFactor_gcd_add_one_of_dvd_sq_sub_one` — *both* `gcd(x − 1, N)` and
  `gcd(x + 1, N)` are nontrivial factors of `N` for a nontrivial square root of one.
* `Nat.isNontrivialFactor_gcd_sub_one_or_gcd_add_one_of_sq_modEq_one` — **Theorem 5.2 verbatim**
  (equivalently Theorem A4.11): with the hypotheses in `Nat.ModEq` form (`x + 1 ≡ 0 [MOD N]` being
  the spelling of `x ≡ −1`), at least one of `gcd(x − 1, N)`, `gcd(x + 1, N)` is a nontrivial
  factor of `N`.

## Two fidelity points

* **The `L`-bit / `O(L³)` clauses are not formalised.** They are complexity statements about
  Euclid's algorithm; the library has no cost model in which to state them, so they are deliberately
  out of scope (as with Theorem 5.1). The formal content captured is the arithmetic claim.
* **The "`N` composite" hypothesis is dropped as unnecessary.** A nontrivial square root of one
  cannot exist modulo a prime or modulo `1`, so compositeness is automatic; the theorem is proved
  for every `0 < N`, which is strictly more general and hence faithful to the stated content.
-/
