/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.GilbertVarshamov

/-!
# Nielsen & Chuang, Exercise 10.23 — the Gilbert–Varshamov bound

*(N&C §10.4.1, p. 449.)*

Prove the Gilbert-Varshamov bound k/n >= 1 - H(2t/n).

The Gilbert–Varshamov bound is stated by N&C as eq. (10.63): for large `n` there exists an `[n, k]`
error-correcting code protecting against errors on up to `t` bits for some `k` such that
> `k / n ≥ 1 − H(2t/n)`,
where `H(x) = −x log x − (1 − x) log(1 − x)` is the binary Shannon entropy (base `2`; N&C Ch. 11).

## What the exercise asks, and what is proved

The bound is an **existence** (achievability) statement: it guarantees that a good linear code
exists whenever one does not try to pack too much rate into too few bits. Its formalisation is two
theorems in `ToMathlib/`, namespace `LinearCode`
(`ToMathlib/InformationTheory/Coding/GilbertVarshamov.lean`):

* the **counting form** — the combinatorial heart — says a binary linear code of dimension `≥ k`
  and minimum distance `≥ d` exists whenever the Hamming-ball volume `∑_{i < d} C(n, i)` fits below
  `2 ^ (n − k)`;
* the **entropy (rate) form** — eq. (10.63) itself — turns that into `k / n ≥ 1 − H₂(2t/n)` by
  setting `d = 2t + 1` and bounding the ball volume by `2 ^ (n · H₂(2t/n))`.

The formalisation is in `ToMathlib/InformationTheory/Coding/GilbertVarshamov.lean`, alongside the
classical-coding development (`LinearCode`, `minDist`, `BinomialEntropyBound`, `SingletonBound`).
Every statement is about classical objects: binary linear codes `LinearCode (ZMod 2) (Fin n)`, their
minimum distance, Hamming-ball volumes `∑ C(n, i)`, and the binary entropy
`H₂ = Real.binEntropyBit`.

The *quantum* Gilbert–Varshamov bound `k / n ≥ 1 − 2 H₂(2t/n)` for CSS codes (N&C eq. (10.122),
Problem 10.2) is a separate item, `Problem10_2_GilbertVarshamov`; it uses the same
classical averaging argument on a *nested pair* of codes (whence the factor of `2`) and is in
`ToMathlib/InformationTheory/Coding/CSSGilbertVarshamov.lean`.

## Declarations

All in `ToMathlib/InformationTheory/Coding/GilbertVarshamov.lean`, binary case over `K = ZMod 2`:

* `LinearCode.exists_correctsErrors_of_rate_le` — **the exercise itself** (eq. (10.63)). In the
  regime `4 * t ≤ n` (so the entropy argument `2t/n` lies in `[0, 1/2]`), if
  `(k : ℝ) ≤ n · (1 − H₂(2t/n))` — i.e. `k / n ≥ 1 − H₂(2t/n)` — then there is a binary linear
  code `C ⊆ (Fin n → ZMod 2)` with `k ≤ Module.finrank (ZMod 2) C` and `C.CorrectsErrors t`
  (`LinearCode.CorrectsErrors C t := (2 * t + 1 : ℕ∞) ≤ C.minDist`, N&C p. 448).
* `LinearCode.exists_finrank_ge_minDist_ge` — **the counting form**: if
  `(∑ i ∈ Finset.range d, n.choose i) ≤ 2 ^ (n − k)` with `k ≤ n`, then a binary linear code of
  dimension `≥ k` and minimum distance `≥ d` exists. Taking `d = 2t + 1` yields a
  `t`-error-correcting code; this is the theorem the rate form specialises.
* `card_filter_hammingNorm_lt_le` — the **ball-volume bound**: the number of binary words of length
  `n` and Hamming weight `< d` is at most `∑_{i < d} C(n, i)` (a word injects into its support).
* `card_parityChecks_mulVec_eq_zero` — the **matrix count** behind the averaging argument (stated
  over any finite field): for a nonzero word `w`, exactly `(#K) ^ (m·n − m)` of the matrices
  `H : Matrix (Fin m) (Fin n) K` satisfy `H *ᵥ w = 0`, by rank-nullity for the surjective map
  `H ↦ H *ᵥ w`.

The entropy step `∑_{i ≤ 2t} C(n, i) ≤ 2 ^ (n · H₂(2t/n))` is
`sum_range_choose_le_rpow_mul_binEntropyBit` in
`ToMathlib/InformationTheory/Coding/BinomialEntropyBound.lean`.

## Faithfulness

* **Statement.** N&C's eq. (10.63) — "there exists an `[n, k]` code protecting against `t` errors
  for *some* `k` with `k / n ≥ 1 − H(2t/n)`" — is the achievability statement captured by
  `exists_correctsErrors_of_rate_le`: for *any* target dimension `k` at or below the bound
  `n · (1 − H₂(2t/n))`, a code of dimension `≥ k` correcting `t` errors exists. Nothing is weakened:
  the code must genuinely correct `t` errors (`minDist ≥ 2t + 1`), exactly N&C's "protecting against
  errors on up to `t` bits".
* **The `4 * t ≤ n` regime.** N&C phrase the bound "for large `n`"; the argument of `H` in (10.63)
  is `2t/n`, and the entropy ball-volume bound `∑_{i ≤ 2t} C(n, i) ≤ 2 ^ (n H₂(2t/n))` is valid
  precisely when `2t/n ≤ 1/2`, i.e. `4t ≤ n`. This is the natural domain of the bound (below it the
  right-hand side of (10.63) is not the operative estimate), not a specialisation of the claim.
* **Base of the entropy.** N&C's `H` here is the base-`2` binary Shannon entropy (bits), so
  `H₂ = Real.binEntropyBit`; the natural-log `Real.binEntropy` would be off by a factor of `log 2`
  and would not yield the `2 ^ (·)` bitstring count.
* **Generality.** The existence is over the binary field `ZMod 2`, matching N&C's binary codes; the
  field-agnostic matrix count is proved over an arbitrary finite field, so the binary case is a
  specialisation of a more general lemma, never a strengthening of hypotheses.
* **Constructiveness.** The proof is the standard Varshamov parity-check averaging (a union/counting
  bound over low-weight words), faithful to the "quite simple" existence proof N&C leaves as the
  exercise; it establishes existence, as the bound asks, without exhibiting a specific code.
-/
