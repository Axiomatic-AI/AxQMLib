/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.MutualInformationMap

/-!
# N&C Exercise 11.9 — mutual information is not always superadditive

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.9, p. 509.

Show mutual information is not always superadditive via a copied-variable example.

Here `H(X : Y) = H(X) + H(Y) − H(X, Y)` is the Shannon mutual information, and the four random
variables are perfectly correlated copies of a single fair bit.

## Where the formalisation lives

The exercise quantifies over a distribution `p : Ω → ℝ` on a finite sample space, random variables
`Ω → Fin 2` and the real-valued quantity `Real.mutualInfoMap`. Compare Problem 11.4, which points to
the neighbouring `Real.condEntropyMap` counterexample.

The declarations are all in `ToMathlib/Analysis/SpecialFunctions/MutualInformationMap.lean`:

* `Real.mutualInfoMap` — the **mutual information** `H(f : g) = H(f) + H(g) − H(f, g)` of two
  random variables `f g` on a common finite sample space, built on the pushforward-law entropy
  `Real.entropyMap` (the random-variable sibling of the joint-distribution `Real.mutualInfo`).
* `Real.exists_mutualInfo_not_superadditive_counterexample` — **the exercise**: an explicit finite
  probability space with random variables `X₁, X₂, Y₁, Y₂` realising `X₂ ≡ Y₁ ≡ Y₂ ≡ X₁` for which
  `H(X₁ : Y₁) + H(X₂ : Y₂) > H(X₁, X₂ : Y₁, Y₂)`, i.e. eq. (11.35) fails. The witness is the fair
  bit `Ω = Fin 2` (uniform `p ≡ 1/2`) with all four variables the identity; each mutual information
  is `log 2`, so the left side is `2 log 2` and the right side `log 2`, a gap of a full bit.
* `Real.not_forall_mutualInfo_superadditive` — its packaging as the refutation: superadditivity of
  the mutual information is **not** a theorem.

## Faithfulness

The exercise's copied-variable hypothesis `X₂ ≡ Y₁ ≡ Y₂ ≡ X₁` is machine-checked, not asserted:
the witness sets all four variables to a single random variable (the identity on the fair bit), and
the joint laws `(X₁, X₂)` and `(Y₁, Y₂)` are the genuine pushforwards of that variable, so the
perfect correlation the exercise relies on is derived rather than posited. N&C measure entropy in
*bits* (base-2 logarithm); the library measures it in *nats* (natural logarithm). The failure is a
strict inequality whose gap is `log b 2 > 0` in any base `b > 1`, hence base-independent: a faithful
reformulation, not a weakening.
-/
