/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.RingTheory.ZMod.OrderFinding

/-!
# Nielsen & Chuang, Theorem 5.3 (most units are good for the order-finding reduction)

For odd composite N, random x coprime to N has order r even and x^{r/2}!=-1 mod N with prob >=
1-1/2^m.

This is the *second step* of N&C's reduction of factoring to order-finding (§5.3.2, proved in
§A4.3): a random `x` coprime to `N` is likely to have even order `r` with `x^{r/2} ≢ −1 (mod N)`,
so that `x^{r/2}` is a *nontrivial square root of `1`* modulo `N` — which the *first step*
(Theorem 5.2) then turns into a nontrivial factor of `N`. (The companion clause `x^{r/2} ≢ +1` is
automatic once `r` is even, since `r` is the least positive exponent with `x^r = 1`; the substance,
bounded below here, is `x^{r/2} ≢ −1`.)

## The erratum, and what is formalised

**Read critically (obligation 1), the printed bound `1 − 1/2^m` is FALSE.** A brute-force count over
`(ZMod N)ˣ` gives a good fraction of exactly `1/2` already at `N = 21` (`= 3 · 7`, `m = 2`): six of
the twelve units are bad, so `1/2 < 3/4 = 1 − 1/2²`. The same happens for every product of two
primes `≡ 3 (mod 4)` (`N = 21, 33, 57, 63, …`). N&C's own proof establishes only that a *bad* unit
forces the per-prime `2`-adic order valuations `d_j` to all coincide — an event of probability
`≤ 1/2^{m-1}` (each of the `m` factors contributes a maximal-`2`-power atom of mass `≤ 1/2`, and
pulling `m − 1` of them out gives `1/2^{m-1}`, not `1/2^m`). The **corrected and tight** bound is

`p(r even and x^{r/2} ≠ −1) ≥ 1 − 1/2^{m-1}`,   attained (with equality) at `N = 21`.

Following the Theorem 5.1 precedent ("read literally, the book is false"), the formalisation both
**proves the corrected theorem outright** and **formally refutes the printed bound**. The uniform
random choice of a coprime residue is modelled — with no probability measure — as an exact
cardinality bound over the finite unit group `(ZMod N)ˣ`, with `r = orderOf x` and `m =
N.primeFactors.card`. The development lives in `ToMathlib/RingTheory/ZMod/OrderFinding.lean`:

* `ZMod.orderFinding_good_units_card_ge` — **the corrected Theorem 5.3 (= A4.13)**:
  for odd `N > 1`, `(2^{m-1} − 1) · φ(N) ≤ 2^{m-1} · #{x : (ZMod N)ˣ | Even (orderOf x) ∧
  x^(orderOf x / 2) ≠ −1}`, i.e. at least a `1 − 1/2^{m-1}` fraction of units are good.
* `ZMod.card_good_units_twentyOne` — exactly `6` of the `12` units of `ZMod 21` are good; the
  witness that the corrected bound is **tight** (`6/12 = 1/2 = 1 − 1/2^{m-1}`).
* `ZMod.not_orderFinding_good_units_printed_bound` — **the refutation**: the printed universal bound
  `(2^m − 1) · φ(N) ≤ 2^m · #{good units}` is false (it would demand ≥ 9 good units at `N = 21`).

## Supporting development (the proof of Theorem A4.13 / §A4.3)

N&C defer the proof to Appendix A4.3, which itself rests on Lemma A4.12 (`2`-adic order counting
in a cyclic group) and Theorem A4.10 (`(ZMod p^α)ˣ` is cyclic for odd `p` — a fact the book cites
Knuth for). These are formalised in `ToMathlib/` as a small reusable tower, imported by the file
above:

* `ToMathlib/GroupTheory/SpecificGroups/Cyclic/OrderValuation.lean` — Lemma A4.12: in a finite
  cyclic
  group of even order, *exactly half* the elements have order divisible by the top power of `2`
  (`IsCyclic.two_mul_card_two_pow_dvd_orderOf`; the single-value `≤ ½` corollary used in the count
  is `IsCyclic.two_mul_card_padicValNat_orderOf_le`).
* `ToMathlib/GroupTheory/SpecificGroups/Cyclic/OrderValuationPi.lean` — the max-atom product bound
  over a finite family of such groups
  (`IsCyclic.two_pow_mul_card_forall_padicValNat_orderOf_eq_le`); this is N&C's own counting
  argument done with the correct `1/2^{m-1}` factor.
* `ToMathlib/GroupTheory/SpecificGroups/Cyclic/OrderValuationPiInvolution.lean` — the bad-tuple
  characterisation: a product tuple is bad iff its components share one `2`-adic order valuation
  (`IsCyclic.not_even_orderOf_or_pow_orderOf_div_two_eq_iff`).

(`(ZMod p^α)ˣ` cyclic is already in Mathlib as `ZMod.isCyclic_units_of_prime_pow`.)

## Deliberately out of scope

The order of `x` and the two `gcd`s are computed by an *order-finding subroutine* and Euclid's
algorithm; the surrounding `O(L³)` runtime and "reduction of factoring to order-finding" are
complexity statements the library has no cost model to express (as with Theorems 5.1, 5.2 and their
`O(L³)` clauses). The formal content captured is the number-theoretic probability bound itself.
-/
