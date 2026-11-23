/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.NoiselessCoding

/-!
# Nielsen & Chuang, Theorem 12.4 (Shannon's noiseless channel coding theorem)

*(N&C p. 540.)*

Shannon's noiseless channel coding theorem: reliable compression iff R > H(X).

Theorem 12.4 is a purely information-theoretic statement about compressing an i.i.d. source
over a finite alphabet: a rate-`R` scheme maps length-`n` source sequences to `⌊n R⌋`-bit strings
and back, and is *reliable* when the exact-recovery probability tends to `1`. It is the
*classical* prerequisite for Schumacher's quantum noiseless coding theorem, Theorem 12.6.

## The formalisation

The formalisation is in `ToMathlib/InformationTheory/NoiselessCoding.lean`, built on the theorem of
typical sequences (`ToMathlib/InformationTheory/TypicalSequence.lean`, N&C Theorem 12.2). A rate-`R`
scheme at block length `n` is the structure `Real.CompressionScheme α n numBits` bundling
`encode : (Fin n → α) → (Fin numBits → Bool)` (N&C's `Cₙ`) and `decode` (their `Dₙ`), with the
intended `numBits = ⌊n R⌋`; `Real.CompressionScheme.successProb p sch` is the exact-recovery
probability `p(Dₙ(Cₙ(x)) = x)`, and reliability of a family is
`Tendsto (fun n => (sch n).successProb p) atTop (𝓝 1)` — exactly N&C's "approaches one". Because
`Real.entropy` is in nats while N&C's rate is in bits, the threshold `H(X) < R` (bits) is written
`entropy p < R * Real.log 2` (nats); see the module docstring for the unit convention.

**Direct part (achievability):**

* `Real.CompressionScheme` — the encode/decode model of a rate-`R` scheme (N&C `Cₙ`, `Dₙ`).
* `Real.CompressionScheme.successProb` — the exact-recovery probability, with `successProb_nonneg`
  and `successProb_le_one` (it is a probability).
* `Real.exists_compressionScheme_sum_typicalSeq_le` — the achievability construction: when
  `|T(n, ε)| ≤ 2 ^ numBits` there is a scheme recovering at least the typical mass.
* `Real.exists_card_typicalSeq_le_two_pow` — for `H + ε < R log 2` the typical set fits in the
  compressed space for large `n`.
* `Real.exists_reliable_compressionScheme` — **Theorem 12.4, direct part**:
  `entropy p < R * log 2` gives a reliable rate-`R` scheme family (success probability → `1`).

**Converse (`R < H(X)` ⟹ not reliable):**

* `Real.CompressionScheme.card_correctlyDecoded_le` — the counting core: a scheme's
  exactly-recovered set `{x : Dₙ(Cₙ(x)) = x}` has at most `2 ^ numBits` members, because `Cₙ` is
  injective on it.
* `Real.CompressionScheme.successProb_tendsto_zero_of_lt` — **Theorem 12.4, converse
  (quantitative):** for a nonnegative bit-rate below the entropy (`0 ≤ R`, `entropy p > R * log 2`)
  the success probability of *every* rate-`R` scheme family tends to `0`. A scheme's success set
  has at most `2 ^ ⌊n R⌋ ≤ exp (n (R log 2))` sequences, whose total probability tends to `0` when
  `R log 2 < H` by the small-set bound `Real.exists_sum_prod_le_of_card_le_exp` (N&C Thm 12.2 (3)).
* `Real.not_reliable_compressionScheme` — **Theorem 12.4, converse:** under the same hypotheses no
  rate-`R` scheme family is reliable (its success probability does not tend to `1`), exactly N&C's
  "any compression scheme will not be reliable".

The nonnegativity hypothesis `0 ≤ R` is faithful, not a weakening: a rate is a number of bits per
symbol, and it is genuinely needed (a deterministic source with a negative "rate" would otherwise be
a spurious counterexample). Both directions together are Shannon's noiseless channel coding theorem.
-/
