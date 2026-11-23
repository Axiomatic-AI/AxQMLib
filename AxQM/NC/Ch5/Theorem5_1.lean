/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.NumberTheory.DiophantineApproximation.LegendreSharp

/-!
# Nielsen & Chuang, Theorem 5.1 (Continued fractions and rational approximation)

If |s/r - phi| <= 1/(2r^2) then s/r is a convergent of phi's continued fraction, computable in
O(L^3).

## What is formalised, and two fidelity points

The mathematical content is *Legendre's Theorem* of Diophantine approximation. It is formalised in
`ToMathlib/NumberTheory/DiophantineApproximation/LegendreSharp.lean`, where the declarations below
are. Mathlib already carries Legendre's Theorem in reduced-rational form
as `Real.exists_convs_eq_rat` (`|ξ - q| < 1 / (2 * q.den ^ 2)` ⟹ `q` is a convergent of `ξ`) and,
via the elementary recursion, `Real.exists_rat_eq_convergent`; the two declarations here supply what
Theorem 5.1 additionally needs.

**The correct theorem (strict form), in N&C's `s/r` phrasing.**

* `Real.exists_convs_eq_of_abs_sub_lt` — **Theorem 5.1 (corrected, strict).** For `k : ℤ`, `r : ℕ`,
  `0 < r`, if `|φ − k/r| < 1/(2r²)` then `k/r` is a convergent of the continued fraction of `φ`.
  This is N&C (5.48) with `s = k` and denominator `r` (not required to be in lowest terms), proved
  from `Real.exists_convs_eq_rat` via the bridge `q.den ∣ r ⇒ q.den ≤ r`, so the `1/(2r²)` accuracy
  implies the `1/(2·den²)` accuracy Legendre requires. This is the form the order-finding
  post-processing consumes; the sibling discrete-logarithm development
  (`.../DiscreteLogRecovery.lean`, Exercise 5.24) reuses it.

**Fidelity point 1 — `≤` is an overstatement.** N&C writes the hypothesis with a *non-strict* `≤`
(5.48), whereas the standard theorem — and the provable one — requires the *strict* `<`. The
non-strict version is genuinely **false** at the boundary: with `φ = 1/2` and `s/r = 1/1` one has
`|1/2 − 1| = 1/2 = 1/(2·1²)`, so `≤` holds with equality, yet the convergents of `1/2` are exactly
`{0, 1/2}` and none equals `1`. Rather than silently proving the strict version under the textbook's
name, the boundary counterexample is formalised and the literal `≤`-statement is refuted:

* `Real.convs_one_half_ne_one` — no continued-fraction convergent of `1/2` equals `1`.
* `Real.not_forall_exists_convs_eq_of_abs_sub_le` — the refutation: it is *not* true that
  `|ξ - q| ≤ 1 / (2 * q.den ^ 2)` forces `q` to be a convergent of `ξ`. This is precisely
  `Real.exists_convs_eq_rat` with `<` weakened to `≤`, shown false.

**Fidelity point 2 — `O(L³)` is not formalised.** The "computable in `O(L³)` operations" clause is a
complexity claim about the continued-fractions algorithm; the library has no cost model in which to
state it, so it is deliberately out of scope. The formal content captured here is the mathematical
approximation theorem (5.48) and its sharpness, which is what the order-finding argument relies on.
-/
