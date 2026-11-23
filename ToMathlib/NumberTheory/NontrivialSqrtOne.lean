/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Divisors

/-!
# Nontrivial square roots of one reveal a factor

A *nontrivial square root of one* modulo `N` is a residue `x` with `x² ≡ 1 (mod N)` that is
neither `1` nor `-1`.  This file proves the elementary number-theoretic fact — the mathematical
heart of the reduction of factoring to order-finding (Shor's algorithm) — that from such an `x`
one immediately reads off a *nontrivial factor* of `N`, namely `gcd(x - 1, N)` (and, in fact,
`gcd(x + 1, N)` as well).

## Main definitions

* `Nat.IsNontrivialFactor d n` : `d` is a divisor of `n` strictly between `1` and `n` (equivalently,
  `d ∈ n.properDivisors` with `1 < d`).

## Main results

* `Nat.isNontrivialFactor_iff_mem_properDivisors` : `d` is a nontrivial factor of `n` iff it is a
  proper divisor of `n` greater than `1` — the `Nat.properDivisors` spelling of the definition.
* `Nat.isNontrivialFactor_gcd_of_dvd_mul` : if `n ∣ a * b` but `n` divides neither `a` nor `b`,
  then `gcd(a, n)` is a nontrivial factor of `n`.  This is the reusable core.
* `Nat.isNontrivialFactor_gcd_sub_one_of_dvd_sq_sub_one` and
  `Nat.isNontrivialFactor_gcd_add_one_of_dvd_sq_sub_one` : for a nontrivial square root of one,
  *both* `gcd(x - 1, N)` and `gcd(x + 1, N)` are nontrivial factors of `N`.
* `Nat.isNontrivialFactor_gcd_sub_one_or_gcd_add_one_of_sq_modEq_one` : the statement exactly
  as it appears as Nielsen & Chuang, *Theorem 5.2* (and Theorem A4.11): at least one of
  `gcd(x - 1, N)`, `gcd(x + 1, N)` is a nontrivial factor of `N`.

## Implementation notes

Nielsen & Chuang phrase the hypotheses as the congruences `x² = 1 (mod N)`, `x ≠ 1 (mod N)`,
`x ≠ N - 1 = -1 (mod N)`, with `1 ≤ x ≤ N`; here `x + 1 ≡ 0 [MOD N]` is the (equivalent)
spelling of `x ≡ -1 (mod N)`.  The book's own proof (Theorem A4.11) shows only that *at least
one* gcd is a nontrivial factor, but in fact both are, so the two per-side lemmas above are
proved and the book's disjunction is derived from them.

Two fidelity points about the exact hypotheses:

* **The `L`-bit / `O(L³)` claims are not formalised.** "`N` is an `L` bit number" and the gcds "can
  be computed using `O(L³)` operations" are complexity statements about Euclid's algorithm; the
  library has no cost model in which to state them, so they are deliberately out of scope.  The
  formal content captured here is the purely arithmetic claim.
* **The "`N` composite" hypothesis is unnecessary.** N&C assume `N` composite, but this is
  automatic: a nontrivial square root of one *cannot* exist modulo a prime (or `1`), so the
  theorems are proved for every `0 < N` — strictly more general, hence faithful to the content.
-/

@[expose] public section

namespace Nat

/-- `d` is a *nontrivial factor* of `n`: a divisor of `n` strictly between `1` and `n`.
Equivalently, `d ∈ n.properDivisors` together with `1 < d`. -/
def IsNontrivialFactor (d n : ℕ) : Prop := d ∣ n ∧ 1 < d ∧ d < n

/-- `d` is a nontrivial factor of `n` iff it is a proper divisor of `n` greater than `1`.  This is
the `Nat.properDivisors` spelling of `Nat.IsNontrivialFactor`. -/
theorem isNontrivialFactor_iff_mem_properDivisors {d n : ℕ} :
    IsNontrivialFactor d n ↔ d ∈ n.properDivisors ∧ 1 < d := by
  constructor
  · rintro ⟨hdvd, h1, h2⟩
    exact ⟨Nat.mem_properDivisors.mpr ⟨hdvd, h2⟩, h1⟩
  · rintro ⟨hmem, h1⟩
    obtain ⟨hdvd, h2⟩ := Nat.mem_properDivisors.mp hmem
    exact ⟨hdvd, h1, h2⟩

/-- If `n` divides a product `a * b` but divides neither factor, then `gcd(a, n)` is a nontrivial
factor of `n`: it is `> 1` (else `a` would be coprime to `n`, forcing `n ∣ b`) and `< n` (else
`n ∣ a`). -/
theorem isNontrivialFactor_gcd_of_dvd_mul {a b n : ℕ} (hn : 0 < n)
    (hab : n ∣ a * b) (ha : ¬ n ∣ a) (hb : ¬ n ∣ b) :
    IsNontrivialFactor (Nat.gcd a n) n := by
  refine ⟨Nat.gcd_dvd_right a n, ?_, ?_⟩
  · -- `1 < gcd a n`
    have hpos : 0 < Nat.gcd a n := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right a n) hn
    have hne1 : Nat.gcd a n ≠ 1 := by
      intro hcop
      have hco : Nat.Coprime a n := hcop
      exact hb (hco.symm.dvd_of_dvd_mul_left hab)
    omega
  · -- `gcd a n < n`
    have hle : Nat.gcd a n ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_right a n)
    have hne : Nat.gcd a n ≠ n := fun heq => ha (heq ▸ Nat.gcd_dvd_left a n)
    omega

/-- First half of Nielsen & Chuang, Theorem 5.2: if `N ∣ x² - 1` but `N` divides neither `x - 1`
nor `x + 1` (i.e. `x` is a nontrivial square root of one modulo `N`), then `gcd(x - 1, N)` is a
nontrivial factor of `N`. -/
theorem isNontrivialFactor_gcd_sub_one_of_dvd_sq_sub_one {N x : ℕ} (hN : 0 < N)
    (hsq : N ∣ x ^ 2 - 1) (h1 : ¬ N ∣ x - 1) (h2 : ¬ N ∣ x + 1) :
    IsNontrivialFactor (Nat.gcd (x - 1) N) N := by
  have hmul : N ∣ (x - 1) * (x + 1) := by
    rw [Nat.mul_comm, ← Nat.sq_sub_sq, Nat.one_pow]; exact hsq
  exact isNontrivialFactor_gcd_of_dvd_mul hN hmul h1 h2

/-- Second half of Nielsen & Chuang, Theorem 5.2: under the same hypotheses, `gcd(x + 1, N)` is
also a nontrivial factor of `N`. -/
theorem isNontrivialFactor_gcd_add_one_of_dvd_sq_sub_one {N x : ℕ} (hN : 0 < N)
    (hsq : N ∣ x ^ 2 - 1) (h1 : ¬ N ∣ x - 1) (h2 : ¬ N ∣ x + 1) :
    IsNontrivialFactor (Nat.gcd (x + 1) N) N := by
  have hmul : N ∣ (x + 1) * (x - 1) := by rw [← Nat.sq_sub_sq, Nat.one_pow]; exact hsq
  exact isNontrivialFactor_gcd_of_dvd_mul hN hmul h2 h1

/-- **Nielsen & Chuang, Theorem 5.2** (equivalently Theorem A4.11 in Appendix 4).  Let `x` be a
nontrivial square root of one modulo `N`, i.e. `x² ≡ 1 (mod N)` with `x ≢ 1` and `x + 1 ≡ 0`
(the spelling of `x ≡ -1`) *both failing*.  Then at least one of `gcd(x - 1, N)` and
`gcd(x + 1, N)` is a nontrivial factor of `N`.

(In fact both are — see `Nat.isNontrivialFactor_gcd_sub_one_of_dvd_sq_sub_one` and
`Nat.isNontrivialFactor_gcd_add_one_of_dvd_sq_sub_one` — but the disjunction is stated to
match the textbook verbatim.) -/
theorem isNontrivialFactor_gcd_sub_one_or_gcd_add_one_of_sq_modEq_one {N x : ℕ} (hN : 0 < N)
    (hx : 1 ≤ x) (hsq : x ^ 2 ≡ 1 [MOD N]) (h1 : ¬ x ≡ 1 [MOD N])
    (h2 : ¬ x + 1 ≡ 0 [MOD N]) :
    IsNontrivialFactor (Nat.gcd (x - 1) N) N ∨ IsNontrivialFactor (Nat.gcd (x + 1) N) N := by
  have hxsq : 1 ≤ x ^ 2 := by simpa using Nat.pow_le_pow_left hx 2
  have hdvd_sq : N ∣ x ^ 2 - 1 := (Nat.modEq_iff_dvd' hxsq).mp hsq.symm
  have ha : ¬ N ∣ x - 1 := fun hd => h1 ((Nat.modEq_iff_dvd' hx).mpr hd).symm
  have hb : ¬ N ∣ x + 1 := fun hd => h2 (Nat.modEq_zero_iff_dvd.mpr hd)
  exact Or.inl (isNontrivialFactor_gcd_sub_one_of_dvd_sq_sub_one hN hdvd_sq ha hb)

end Nat
