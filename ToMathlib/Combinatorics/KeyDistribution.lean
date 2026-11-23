/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Key counts for public-key versus private-key cryptography

Consider a system of `n` users, *any* pair of which wishes to be able to communicate
privately.  This file counts the cryptographic keys that must be distributed under the two
classical paradigms, formalising Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Exercise 12.25 (p. 584).

The users form a finite type `V` (so "`n` users" is `Fintype.card V = n`), and the
"communication demand" — every pair wishes to talk — is the **complete graph** `⊤` on `V`.

* Under **public-key** cryptography each user publishes a single public key (anyone may
  encrypt to it; the matching private key never leaves its owner).  The distributed keys are
  therefore indexed one-per-user, so their number is `Fintype.card V` (`publicKeys`,
  `card_publicKeys`).
* Under **private-key** cryptography every communicating pair must *share* a distinct secret
  key (a key shared by users `a` and `b` cannot be reused with a third user without leaking
  it).  The distributed keys are therefore in bijection with the unordered pairs of distinct
  users — the **edges** of the complete graph on `V` — so their number is
  `(Fintype.card V).choose 2 = Fintype.card V * (Fintype.card V - 1) / 2` (`privateKeys`,
  `card_privateKeys_choose`, `card_privateKeys`).

The point of the exercise is the contrast in scaling: the public-key count grows *linearly*
in the number of users while the private-key count grows *quadratically*.  In particular the
private-key scheme requires at least as many keys as the public-key scheme once there are at
least three users (`card_publicKeys_le_card_privateKeys`) — an instance of the "secure
distribution of key bits is the major difficulty of private-key cryptosystems" remark
preceding the exercise in Nielsen & Chuang.

Because the underlying combinatorics is exactly the edge count of a complete graph, the
substantive facts (`SimpleGraph.card_edgeFinset_top_eq_card_choose_two`, `Nat.choose_two_right`)
already live in Mathlib; this file records the cryptographic *model* — what "a key" is in each
scheme — and reads the counts off it.
-/

@[expose] public section

namespace Cryptography.KeyDistribution

variable (V : Type*) [Fintype V]

/-- The public keys distributed among a set `V` of users under **public-key** cryptography:
one published public key per user.  (The private half of each key pair never leaves its
owner and so is not distributed.) -/
def publicKeys : Finset V := Finset.univ

/-- **Public-key count.** A public-key system for `n` users distributes `n` keys, one per
user. -/
theorem card_publicKeys : (publicKeys V).card = Fintype.card V :=
  Finset.card_univ

variable [DecidableEq V]

/-- The secret keys distributed among a set `V` of users under **private-key** cryptography:
one shared key per unordered pair of *distinct* users that wishes to communicate, i.e. one
per edge of the complete graph `⊤` on `V`. -/
noncomputable def privateKeys : Finset (Sym2 V) := (⊤ : SimpleGraph V).edgeFinset

/-- **Private-key count** (binomial form).  A private-key system for `n` users distributes
`n.choose 2` keys, one per pair of users. -/
theorem card_privateKeys_choose : (privateKeys V).card = (Fintype.card V).choose 2 := by
  rw [privateKeys, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-- **Private-key count** (closed form).  A private-key system for `n` users distributes
`n * (n - 1) / 2` keys, one per pair of users. -/
theorem card_privateKeys : (privateKeys V).card = Fintype.card V * (Fintype.card V - 1) / 2 := by
  rw [card_privateKeys_choose, Nat.choose_two_right]

/-- **The scaling contrast.**  Once there are at least three users, the private-key scheme
requires at least as many distributed keys as the public-key scheme: the linear count
`Fintype.card V` is bounded by the quadratic count `(Fintype.card V).choose 2`.  (For two
users the counts are `2` and `1`; the crossover is at three users, where both equal `3`.) -/
theorem card_publicKeys_le_card_privateKeys (h : 3 ≤ Fintype.card V) :
    (publicKeys V).card ≤ (privateKeys V).card := by
  rw [card_publicKeys, card_privateKeys_choose, Nat.choose_two_right,
    Nat.le_div_iff_mul_le (k := 2) (by omega)]
  exact Nat.mul_le_mul (le_refl _) (by omega)

/-- **Public-key count for `n` users** (`V = Fin n`): a public-key system for `n` users
distributes exactly `n` keys. -/
theorem card_publicKeys_fin (n : ℕ) : (publicKeys (Fin n)).card = n := by
  rw [card_publicKeys, Fintype.card_fin]

/-- **Private-key count for `n` users** (`V = Fin n`): a private-key system for `n` users
distributes exactly `n * (n - 1) / 2` keys. -/
theorem card_privateKeys_fin (n : ℕ) : (privateKeys (Fin n)).card = n * (n - 1) / 2 := by
  rw [card_privateKeys, Fintype.card_fin]

end Cryptography.KeyDistribution
