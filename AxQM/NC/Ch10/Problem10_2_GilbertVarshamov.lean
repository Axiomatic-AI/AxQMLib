/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.CSSGilbertVarshamov

/-!
# Nielsen & Chuang, Problem 10.2 — the Gilbert–Varshamov bound for CSS codes

*(N&C §10.4.2 / end-of-chapter, p. 495.)*

Prove Gilbert-Varshamov bound for CSS codes k/n>=1-2H(2t/n) (and general stabilizer form).

## What the problem asks, and what is proved

N&C §10.4.2 establishes the **CSS construction** as background: from a *nested pair* of classical
binary linear codes `C₂ ⊆ C₁ ⊆ 𝔽₂ⁿ` in which **both `C₁` and `C₂⊥` correct `t` errors**, the
coset states `CSS(C₁, C₂)` form an `[n, k₁ − k₂]` quantum code correcting `t` qubit errors
(`k₁ = dim C₁`, `k₂ = dim C₂`). The text then says of the Gilbert–Varshamov bound that *"the proof
… is left as an end of chapter problem"*. So the content Problem 10.2 asks one to **prove** is the
existence, at the claimed rate, of such a nested pair: a Gilbert–Varshamov *counting/averaging*
argument over classical linear codes. The factor of `2` in `1 − 2 H(2t/n)` is exactly the two
independent distance constraints — one on `C₁`, one on `C₂⊥` — each of which consumes one factor
`H(2t/n)` of the Hamming-ball volume in the count.

This item's formalisation is that classical Gilbert–Varshamov existence bound. It is proved in
full — `sorry`-free, no new `axiom` — as two theorems in `ToMathlib/`, namespace
`LinearCode` (`ToMathlib/InformationTheory/Coding/CSSGilbertVarshamov.lean`):

* `LinearCode.exists_nestedPair_minDist_ge` — **counting form**. For block length `n` and
  parameters `a, b, d` with `1 ≤ d`, `a ≤ n`, and the joint ball-volume condition
  `(∑_{i < d} C(n,i)) · (2^(n−a) + 2^(a+b)) < 2^n`, there is a nested pair
  `C₂ ⊆ C₁ ⊆ (Fin n → ZMod 2)` with `d ≤ minDist C₁`, `d ≤ minDist C₂⊥`, and
  `b + dim C₂ ≤ dim C₁` (so the CSS dimension `dim C₁ − dim C₂ ≥ b`). The proof is a single
  Varshamov averaging argument over one random `(a+b) × n` matrix `M` over `𝔽₂`, with
  `C₁ := ker(top a rows of M)` and `C₂ := ker M`, bounding the two families of "bad" matrices
  (a low-weight word in `C₁`; a low-weight word in the row space `C₂⊥`) below `2^((a+b)·n)`.

* `LinearCode.exists_nestedPair_correctsErrors_of_rate_le` — **entropy/rate form**, i.e.
  eq. (10.122)/(10.74) itself. In the regime `4t ≤ n` (so `2t/n ∈ [0, 1/2]`), for a target CSS
  dimension `k` with `(k : ℝ) + 4 ≤ n · (1 − 2 H₂(2t/n))`, there is a nested pair `C₂ ⊆ C₁` with
  `CorrectsErrors C₁ t`, `CorrectsErrors C₂⊥ t` (each meaning `2t + 1 ≤ minDist`), and
  `k + dim C₂ ≤ dim C₁` — i.e. the achievable CSS rate is `(dim C₁ − dim C₂)/n ≥ 1 − 2 H₂(2t/n)`.
  Obtained from the counting form by taking `d = 2t + 1`, `b = k`, and `a = s + 1` with
  `s = ⌈n · H₂(2t/n)⌉₊` bounding the ball volume `∑_{i ≤ 2t} C(n,i) ≤ 2^(n H₂) ≤ 2^s`.

Given such a pair, the CSS construction of §10.4.2 turns it into the `[n, dim C₁ − dim C₂]` quantum
code correcting `t` qubit errors — so the achievable classical rate `1 − 2 H₂(2t/n)` is exactly the
CSS quantum Gilbert–Varshamov rate of eq. (10.122).

## Formalisation

The formalisation is the collection of `def`s / `theorem`s below, all in `ToMathlib/`.

*The bound itself — `ToMathlib/InformationTheory/Coding/CSSGilbertVarshamov.lean`, namespace
`LinearCode`:*
* `LinearCode.exists_nestedPair_correctsErrors_of_rate_le` — **eq. (10.122)/(10.74)**, the rate
  form: for `4t ≤ n` and `(k : ℝ) + 4 ≤ n · (1 − 2 H₂(2t/n))`, a nested pair `C₂ ≤ C₁` with both
  `C₁` and `dual C₂` (`= C₂⊥`) correcting `t` errors and CSS dimension `dim C₁ − dim C₂ ≥ k`;
* `LinearCode.exists_nestedPair_minDist_ge` — the counting form it is derived from (a single
  Varshamov averaging over one random `(a + b) × n` binary matrix);
* private counting helpers `card_fiber_apply_le`, `card_filter_mulVec_top_eq_zero_le`,
  `card_filter_vecMul_hammingNorm_lt_le` (the shared fibre count + the two "bad-matrix" family
  bounds, one per distance constraint).

*Classical coding-theory results it is built from (also used by Exercise 10.23):*
* linear codes — `ToMathlib/InformationTheory/Coding/LinearCode.lean`: `LinearCode.minDist`
  (eq. (10.61)), `LinearCode.le_minDist_iff`, `LinearCode.CorrectsErrors` (`2t + 1 ≤ minDist`,
  p. 448);
* the classical single-code GV core (Exercise 10.23) in
  `ToMathlib/InformationTheory/Coding/GilbertVarshamov.lean`:
  `LinearCode.exists_finrank_ge_minDist_ge` (counting),
  `LinearCode.exists_correctsErrors_of_rate_le` (rate, eq. (10.63)),
  `card_filter_hammingNorm_lt_le` (ball-volume bound);
* dual codes (§10.4.1) — `ToMathlib/InformationTheory/Coding/DualCode.lean`: `LinearCode.dual`
  (`C⊥`),
  `LinearCode.finrank_dual` (`dim C⊥ = n − dim C`), `LinearCode.dual_ker_mulVecLin` (the dual of a
  kernel code is its row space — the identity that packages `C₂⊥` as the matrix row space);
* the entropy volume bound — `ToMathlib/InformationTheory/Coding/BinomialEntropyBound.lean`:
  `sum_range_choose_le_rpow_mul_binEntropyBit` (`∑_{i ≤ r} C(n,i) ≤ 2 ^ (n · H₂(r/n))` when
  `2r ≤ n`), which supplies the two ball-volume factors that make the CSS rate `1 − 2 H₂`.

The quantum CSS construction of §10.4.2 turning such a pair into an `[n, dim C₁ − dim C₂]` quantum
code correcting `t` qubit errors is the subject of Exercise 10.51.

## Content

The verifiable content is classical binary linear codes (`LinearCode (ZMod 2) (Fin n)`), their
minimum distance, dual, Hamming-ball volumes, and binary entropy `H₂ = Real.binEntropyBit` (the
base-`2` entropy, needed for the bitstring counting bound `V(n, r) ≤ 2^(n H₂(r/n))`). Compare the
classical single-code Gilbert–Varshamov bound of `Exercise10_23_GilbertVarshamov`
(`LinearCode.exists_correctsErrors_of_rate_le`).

The quantum side of the CSS construction — the coset states `|x + C₂⟩` as `PureState`s on `qubitⁿ`,
their cross-coset orthonormality, the code dimension `2^(k₁−k₂)`, and Knill–Laflamme `t`-qubit
correctability — is the §10.4.2 background, treated in the CSS-code items (Exercise 10.51 "the check
matrix is the stabilizer of `CSS(C₁, C₂)`; use Theorem 10.8 for `t`-qubit correction", Exercise
10.27, Exercises 12.35/12.36) and not repeated here.
## Faithfulness

* **Statement.** The theorem is eq. (10.122) as stated: for any target rate strictly below
  `1 − 2 H₂(2t/n)` there is a CSS code (nested pair) of that rate correcting `t` errors — N&C's
  "for some `k` such that `k/n ≥ 1 − 2 H(2t/n)`". No distance requirement is weakened: **both**
  `C₁` and `C₂⊥` are required to correct `t` errors, which is precisely what the CSS construction
  needs (dropping either would give a weaker, non-CSS-usable pair).
* **The additive `+4`.** The rate form asks `(k : ℝ) + 4 ≤ n(1 − 2 H₂(2t/n))` rather than the bare
  `k ≤ n(1 − 2 H₂(2t/n))`. The constant `4` (absorbing the ceiling slack in `s` and the strictness
  of the counting condition) is `O(1)` and vanishes from the *rate* `k/n` as `n → ∞`, matching
  N&C's asymptotic phrasing of the Gilbert–Varshamov bound (10.74). It is not a strengthening of the
  hypothesis in any way that changes the asymptotic claim.
* **Base of the entropy.** N&C's `H` in the coding-theory bounds is the base-`2` binary entropy
  (bits), so `H₂ = Real.binEntropyBit`; the natural-log `Real.binEntropy` would be off by a factor
  of `log 2` and would not give the `2^(·)` bitstring count.
* **The stabilizer challenge (10.123)** — the general (non-CSS) stabilizer Gilbert–Varshamov bound
  `k/n ≥ 1 − 2 log(3) t/n − H(2t/n)` — is set by N&C in explicitly optional language: *"As a
  challenge, you may like to try proving the Gilbert–Varshamov bound for a general stabilizer
  code…"*. The mandatory imperative *"Prove"* governs only the CSS form (10.122); (10.123) is a
  suggested extension, not part of the required claim, and no other item owns it. It is also
  a genuinely separate development — an averaging over isotropic subspaces of the symplectic space
  `𝔽₂^{2n}` with the `3^(weight)` Pauli-error enumeration producing the `log 3` term, not the
  classical nested-pair matrix count. It is therefore
  not claimed; the *required* content of Problem 10.2 — the
  CSS bound (10.122) — is proved here in full, with no distance constraint weakened.
-/
