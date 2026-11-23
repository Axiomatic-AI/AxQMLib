/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.HighFidelityEntropy

/-!
# Nielsen & Chuang, Exercise 12.30 (simplifying the spike-distribution entropy)

*(N&C p. 594.)*

Simplify (12.199) to obtain the S(rho) expression in Lemma 12.19.

**The setup.** In the proof of Lemma 12.19 ("high fidelity implies low entropy"), N&C bound the
entropy of a density matrix `ρ` on `2n` qubits by that of the worst-case diagonal matrix `ρ_max`,
whose eigenvalues form a *spike*: one mass `1 - 2^(-s)` and the residual weight `2^(-s)` spread
uniformly over the other `2^(2n) - 1` eigenvalues. Equation (12.199) writes its base-`2` entropy as

`S(ρ_max) = -(1 - 2^(-s)) log(1 - 2^(-s)) - 2^(-s) log(2^(-s) / (2^(2n) - 1))`,

and the exercise is to simplify this to the Lemma's expression
`S(ρ) < (2n + s + 1 / ln 2) · 2^(-s) + O(2^(-2s))`.

**The simplification.** Splitting the second logarithm gives `2^(-s) log(2^(2n) - 1) + s · 2^(-s)`
(the `s · 2^(-s)` and `2n · 2^(-s)` terms), and the first term expands as `-(1-x) log(1-x) =
x / ln 2 + O(x²)` with `x = 2^(-s)` (the `2^(-s) / ln 2` term). Two facts make the estimate clean:
`log_2(2^(2n) - 1) < 2n` and `-(1-x) log(1-x) < x`. Both overestimates push the same way, so the
strict bound `S(ρ_max) < (2n + s + 1 / ln 2) · 2^(-s)` holds *without* the `O(2^(-2s))` slack of the
book; the honest two-sided expansion (with the exact leading coefficient `log_2(2^(2n) - 1)` and an
explicit `O(2^(-2s))` remainder) is recorded separately.

## The formalisation

The content is the real-analysis simplification of an entropy expression. The formalisation is in
`ToMathlib/InformationTheory/HighFidelityEntropy.lean`, in the `Real` namespace (alongside
`Real.binEntropyBit`):

* `Real.spikeEntropyBit s n` — the base-`2` spike entropy, i.e. the right-hand side of eq. (12.199);
* `Real.spikeEntropyBit_eq_binEntropyBit_add` — the first algebraic step, splitting the second
  logarithm to expose `binEntropyBit (2^(-s)) + 2^(-s) · logb 2 (2^(2n) - 1)`;
* `Real.spikeEntropyBit_lt` — the simplified bound of Lemma 12.19,
  `spikeEntropyBit s n < (2n + s + 1 / ln 2) · 2^(-s)` for `0 < s`, `1 ≤ n`;
* `Real.abs_spikeEntropyBit_sub_le` — the honest asymptotic form with an explicit `O(2^(-2s))`
  remainder and the exact leading coefficient `logb 2 (2^(2n) - 1)`.
-/
