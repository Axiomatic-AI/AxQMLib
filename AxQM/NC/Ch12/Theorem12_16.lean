/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.UniversalHashRefutation

/-!
# Nielsen & Chuang, Theorem 12.16 (universal hashing / privacy amplification)

*(N&C p. 584.)*

Universal hash: H(G(X)|G) >= Hc(G(X)|G) >= m - 2^{m-Hc(X)}.

Here `Hc(X) = −log₂ ∑ₓ p(x)²` is the **collision entropy** (Rényi entropy of order 2, N&C
eq. 12.171), and a family `G` of hash functions `𝒳 → {0, 1}ᵐ` is **(2-)universal** when for every
pair of distinct inputs `a₁ ≠ a₂` the probability that a uniformly chosen `g ∈ G` collides them,
`g(a₁) = g(a₂)`, is at most `1/|B| = 2⁻ᵐ`. Writing `B = {0, 1}ᵐ`, `m = log₂|B|` is the number of
output bits, and `2^{m − Hc(X)} = |B|·Pc(X)` where `Pc(X) = ∑ₓ p(x)²` is the collision probability.

Theorem 12.16 is a statement in classical probability / information theory about the output
of a randomly chosen universal hash function. Compare the neighbouring collision-entropy result
Theorem 12.17 (`Theorem12_17`).

## The literal bound is FALSE — what is formalised

Read critically, **Nielsen & Chuang's second inequality is false as literally stated.** The first
inequality `H(G(X)|G) ≥ Hc(G(X)|G)` is correct. But the constant `2^{m − Hc(X)}` in the second
inequality over-states the true bound: the leftover-hash argument only gives an average collision
probability `E_G[Pc(g(X))] ≤ 1/|B| + Pc(X)`, so the honest lower bound is

`Hc(G(X)|G) ≥ m − log₂(1 + 2^{m − Hc(X)})`,

and `log₂(1 + z) > z` for `0 < z < 1` (equivalently `2^z < 1 + z`, the strict convexity of `2^·`
below its chord) — N&C drop the `1/ln 2` in `log₂(1 + z) ≤ z / ln 2`. In the regime of interest for
key extraction, `m < Hc(X)` so `z = 2^{m − Hc(X)} ∈ (0, 1)`, and the textbook constant strictly
exceeds the achievable bound. The faithful formalisation is
therefore **the corrected positive chain plus a formal refutation of the literal constant**, not a
silently strengthened restatement.

## The formalisation

The formalisation is a collision-entropy / universal-hashing API in
`ToMathlib/InformationTheory/`.

### Core collision-entropy API — `ToMathlib/InformationTheory/CollisionEntropy.lean`

* `Real.collisionProb p = ∑ᵢ p i ^ 2` — the collision probability `Pc(X) = ∑ₓ p(x)²`.
* `Real.collisionEntropy p = −Real.logb 2 (Real.collisionProb p)` — `Hc(X) = −log₂ ∑ₓ p(x)²`
  (N&C eq. 12.171).
* `Real.collisionEntropy_le_entropy_div_log_two` — **the first inequality, unconditional form**
  `Hc(X) ≤ H(X)`: `collisionEntropy p ≤ entropy p / Real.log 2` (Shannon entropy in bits), via
  `Real.log_collisionProb_inv_le_entropy` (Gibbs against the tilted reference `qᵢ = pᵢ²/Pc`).

### Universal hashing, leftover-hash bound — `ToMathlib/InformationTheory/UniversalHashing.lean`

(building on the push-forward identity `Real.collisionProb_law_eq_sum_pairs` of
`ToMathlib/InformationTheory/CollisionEntropyLaw.lean`)

* `Real.IsUniversalFamily h` — `h : γ → α → β` is `2`-universal: for `x ≠ x'`,
  `#{g | h g x = h g x'} / |γ| ≤ |β|⁻¹`.
* `Real.avgCollisionProb h p = (∑_g Real.collisionProb (Real.law p (h g))) / |γ|` — the average
  collision probability `E_G[Pc(g(X))]` of the hashed output.
* `Real.avgCollisionProb_le` — **the leftover-hash collision bound** (the combinatorial core of
  Theorem 12.16): for a universal `h`, `avgCollisionProb h p ≤ |β|⁻¹ + collisionProb p`,
  i.e. `E_G[Pc(g(X))] ≤ 1/|B| + Pc(X)`.

### Output entropies and the entropy chain — `ToMathlib/InformationTheory/UniversalHashEntropy.lean`

* `Real.avgCollisionEntropy h p = −Real.logb 2 (Real.avgCollisionProb h p)` — the conditional
  collision entropy `Hc(G(X) | G)` (convention A: `−log₂` of the *average* collision probability,
  the definition used in privacy amplification).
* `Real.avgShannonEntropy h p` — the conditional Shannon entropy `H(G(X) | G)` in bits.
* `Real.avgCollisionEntropy_le_avgShannonEntropy` — **the first inequality of Theorem 12.16**
  `H(G(X)|G) ≥ Hc(G(X)|G)`: averaging the per-`g` bound `Hc(g(X)) ≤ H(g(X))` and applying Jensen to
  the concave `log`.
* `Real.avgCollisionEntropy_ge` — **the corrected (honest) second inequality**
  `Hc(G(X)|G) ≥ log₂|β| − log₂(1 + |β|·Pc(X))`, i.e. `m − log₂(1 + 2^{m − Hc(X)})`, from
  `avgCollisionProb_le`, monotonicity of `log₂`, and the factorisation
  `|β|⁻¹ + Pc = |β|⁻¹·(1 + |β|·Pc)`.

### Refutation of the literal constant — `ToMathlib/InformationTheory/UniversalHashRefutation.lean`

* `Real.card_filter_apply_eq_pow` — for `x ≠ x'`, exactly `|β|^{|α|−1}` of the `|β|^{|α|}` functions
  `g : α → β` satisfy `g x = g x'` (a restriction-to-complement equivalence).
* `Real.id_isUniversalFamily` — the **all-functions family** `id : (α → β) → α → β` (index set
  `γ = α → β`, uniform `G` = a uniformly random function) is *exactly* `2`-universal.
* `Real.avgCollisionProb_id` — its closed form `avgCollisionProb id p = |β|⁻¹ + (1 − |β|⁻¹)·Pc(X)`,
  so the leftover-hash bound `≤ |β|⁻¹ + Pc(X)` is essentially tight.
* `Real.avgCollisionEntropy_id_uniform_lt_literalBound` — the concrete counterexample on
  `α = Fin 16`, `β = Fin 8` with `X` uniform: `m = 3`, `Pc(X) = 1/16` (`Hc(X) = 4`),
  `avgCollisionProb = 1/8 + (7/8)·(1/16) = 23/128`, so
  `Hc(G(X)|G) = −log₂(23/128) = 2.4757… < 5/2 = 3 − 2^{3−4} = m − 2^{m − Hc(X)}`. The strict
  inequality reduces to `23/128 > 2^{−5/2}`, i.e. `529 > 512` after squaring.
* `Real.exists_lt_universalHash_literalBound` — **the refutation**: there is a genuinely
  `2`-universal family `h` and input distribution `p` with
  `Hc(G(X)|G) < log₂|β| − |β|·Pc(X)` (`= m − 2^{m − Hc(X)}`), so Nielsen & Chuang's literal second
  inequality is false as stated.

## Faithfulness

* **First inequality.** `Real.avgCollisionEntropy_le_avgShannonEntropy` is verbatim N&C's
  `H(G(X)|G) ≥ Hc(G(X)|G)`, for an arbitrary `2`-universal family over finite alphabets and any
  input distribution.
* **Second inequality.** N&C's literal `Hc(G(X)|G) ≥ m − 2^{m − Hc(X)}` does **not** hold; the
  formalisation records the strongest true statement (`Real.avgCollisionEntropy_ge`, the
  `log₂(1 + ·)` bound) *and* a proof that the textbook constant fails
  (`Real.exists_lt_universalHash_literalBound`). No hypothesis was added and no dimension
  specialised to make the literal bound provable — it is genuinely false, and the counterexample is
  a *perfectly* `2`-universal family, so the refutation cannot be dismissed as an artefact of a
  degenerate hash family. The corrected bound `m − log₂(1 + 2^{m − Hc(X)})` is the honest content of
  N&C's second inequality: it is what the leftover-hash argument delivers, it agrees with the
  textbook constant to first order (`log₂(1 + z) ≈ z` as `z → 0`, the regime `m ≪ Hc(X)` where
  privacy amplification is applied), and it dominates it everywhere, so it is a faithful correction,
  not a different theorem wearing the same name.

## Summary

The two-inequality positive chain and the refutation of the literal constant are in
`ToMathlib/InformationTheory/{CollisionEntropy, CollisionEntropyLaw, UniversalHashing,
UniversalHashEntropy, UniversalHashRefutation}.lean`, with the main results
`Real.avgCollisionEntropy_le_avgShannonEntropy` (first inequality), `Real.avgCollisionEntropy_ge`
(corrected second inequality) and `Real.exists_lt_universalHash_literalBound` (refutation).
-/
