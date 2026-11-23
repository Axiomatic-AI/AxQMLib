/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.RingTheory.Fintype

/-!
# Nielsen & Chuang, Exercise 5.11

Show that the order r of x satisfies r <= N.

*(N&C p. 226, §5.3.1.)*

For positive coprime integers `x < N`, N&C define the *order of `x` modulo `N`* as the least
positive integer `r` with `x ^ r ≡ 1 (mod N)` — precisely the multiplicative order
`orderOf (x : ZMod N)`, the residue `(x : ZMod N)` being a unit exactly because `gcd(x, N) = 1`.
Exercise 5.11 asks to show `r ≤ N`.

## The formalisation

The exercise's content is **already in stock Mathlib**:

* `ZMod.orderOf_lt` (`Mathlib/RingTheory/Fintype.lean`) —
  `∀ {n : ℕ}, 1 < n → ∀ (a : ZMod n), orderOf a < n`.

N&C's `r ≤ N` is the immediate `le_of_lt` weakening of this sharper bound `r < N`. Concretely, for
`1 < N` and any residue `x : ZMod N`, `(ZMod.orderOf_lt hN x).le : orderOf x ≤ N`.

## Fidelity

* **The hypothesis.** N&C take `x`, `N` positive with `x < N`; a positive `x < N` forces `N ≥ 2`,
  so the lemma's hypothesis `1 < N` is exactly the exercise's setting.
* **The order.** N&C's "order `r` of `x`" is `orderOf (x : ZMod N)`. Under the exercise's
  coprimality hypothesis `(x : ZMod N)` is a unit, so `orderOf (x : ZMod N)` is the genuine positive
  order `r` (the least `r > 0` with `x ^ r ≡ 1 (mod N)`). `ZMod.orderOf_lt` bounds it for *every*
  residue — including the non-coprime case, where `orderOf = 0 ≤ N` holds trivially — so it proves
  at least the exercise's `r ≤ N` under strictly weaker hypotheses.
* **No weakening.** Proving the sharper `r < N` (and hence `r ≤ N`) for an arbitrary residue is a
  faithful — indeed strictly stronger — discharge of the stated `r ≤ N`. A separate `orderOf x ≤ N`
  restatement would merely duplicate `ZMod.orderOf_lt`, so none is added.
-/
