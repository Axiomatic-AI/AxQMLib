/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Combinatorics.KeyDistribution

/-!
# Nielsen & Chuang, Exercise 12.25 (key counts for public- vs private-key cryptography)

*(N&C p. 584.)*

Count keys needed for n users under public vs private key cryptography.

**The answers.** With `n` users, each pair of which wishes to communicate:

* **Public key** — each user publishes one public key (anyone may encrypt to it; the matching
  private key never leaves its owner). One key per user, so `n` keys — a count *linear* in `n`.
* **Private key** — every pair of users must share its own distinct secret key (a key shared
  by two users cannot be reused with a third without leaking it). One key per unordered pair
  of distinct users, so `n choose 2 = n(n-1)/2` keys — a count *quadratic* in `n`. This is
  the whole point: as N&C stress just before the exercise, "the major difficulty of private
  key cryptosystems is secure distribution of key bits", and that burden grows quadratically.

This is a pure counting statement — the number of published public keys is the number of
users, and the number of shared private keys is the number of *edges of the complete graph*
on the users (each pair of distinct users is an edge).

## The formalisation

The formalisation is in
`ToMathlib/Combinatorics/KeyDistribution.lean`, in the `Cryptography.KeyDistribution` namespace.
The users are a finite type `V` (so "`n` users" is `Fintype.card V = n`) and the model records
what "a key" is in each scheme:

* `Cryptography.KeyDistribution.publicKeys` — the published public keys, one per user
  (`Finset.univ : Finset V`); `card_publicKeys : (publicKeys V).card = Fintype.card V`.
* `Cryptography.KeyDistribution.privateKeys` — the shared secret keys, one per communicating
  pair (`(⊤ : SimpleGraph V).edgeFinset`, the edges of the complete graph);
  `card_privateKeys_choose : (privateKeys V).card = (Fintype.card V).choose 2` and the closed
  form `card_privateKeys : … = Fintype.card V * (Fintype.card V - 1) / 2`.
* `card_publicKeys_le_card_privateKeys` — the scaling contrast: for `3 ≤ Fintype.card V` the
  quadratic private-key count dominates the linear public-key count.
* `card_publicKeys_fin` / `card_privateKeys_fin` — the `V = Fin n` specialisations, giving the
  literal answers `n` and `n * (n - 1) / 2`.

The substantive combinatorics (`SimpleGraph.card_edgeFinset_top_eq_card_choose_two`,
`Nat.choose_two_right`) is already in Mathlib; the file supplies the cryptographic model and
reads the counts off it.
-/
