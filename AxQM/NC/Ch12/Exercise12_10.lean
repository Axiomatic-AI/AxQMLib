/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.ComposedChannel

/-!
# Nielsen & Chuang, Exercise 12.10 (composed channels)

*(N&C p. 553.)*

Composed channels: C(N2 o N1) <= min(C(N1),C(N2)); strict example.

Exercise 12.10 is a purely information-theoretic statement about *classical* discrete memoryless
channels: it compares the information capacities `max_{p(x)} H(X : Y)` (the right-hand side of
Shannon's noisy channel coding theorem, N&C Theorem 12.7, `Theorem12_7`) of a series composition
and its factors. Compare `Theorem12_7` and `Exercise12_9`.

Entropy is in *nats* (natural log) rather than N&C's *bits*, so N&C's `1` is our `log 2`; capacities
scale by this global factor, so the results are faithful reformulations. The bound is in fact
base-independent.

## The formalisation

The formalisation is in `ToMathlib/InformationTheory/ComposedChannel.lean`. It uses the discrete
memoryless channel / information capacity of `ToMathlib/InformationTheory/NoisyChannel.lean`, the
classical data-processing inequality of
`ToMathlib/Analysis/SpecialFunctions/DataProcessingInequality.lean`, and the binary symmetric
channel
of `ToMathlib/InformationTheory/BinaryChannels.lean` (`Exercise12_9`).

**Part 1 — the series composition and the capacity bound:**

* `Real.channelComp` — the **series composition** `N₂ ∘ N₁` of two channels `q₁ : ι → κ → ℝ`,
  `q₂ : κ → μ → ℝ`, with conditional law `p(z | x) = ∑_y q₁(y | x) q₂(z | y)`.
* `Real.isChannel_channelComp` — the composition is again a discrete memoryless channel.
* `Real.channelTriple` — the tripartite input–intermediate–output joint law
  `p(x) q₁(y | x) q₂(z | y)`, whose Markov-chain structure (`Real.isMarkovChain_channelTriple`)
  drives the two data-processing bounds.
* `Real.channelMutualInfo_channelComp_le_left` / `..._le_right` — the per-input-distribution
  bounds `H(X : Z) ≤ H(X : Y)` and `H(X : Z) ≤ H(Y : Z)` from the data-processing inequality.
* `Real.channelCapacity_channelComp_le_min` — **Exercise 12.10 (bound):**
  `C(N₂ ∘ N₁) ≤ min (C(N₁)) (C(N₂))`. Composing channels can only lose information.

**Part 2 — an example where the inequality is strict:**

* `Real.channelComp_bscChannel_self` — two identical binary symmetric channels in series form a
  binary symmetric channel with the *compounded* crossover probability `2 p (1 - p)`.
* `Real.channelCapacity_channelComp_bscChannel_lt_min` — **Exercise 12.10 (strict example):** for a
  nondegenerate crossover `0 < p < 1/2` and `N₁ = N₂ = bscChannel p`, the bound is *strict*,
  `C(N₂ ∘ N₁) < min (C(N₁)) (C(N₂))`.

The strict example is Nielsen & Chuang's own running channel on this page: composing two binary
symmetric channels `bscChannel p` compounds the crossover to `2 p (1 - p)`, which for `0 < p < 1/2`
satisfies `p < 2 p (1 - p) ≤ 1/2`. Since the binary entropy is strictly increasing on `[0, 1/2]`
(`Real.binEntropy_strictMonoOn`) and the capacity of `bscChannel r` is `log 2 - H(r)`
(`Real.bscChannel_channelCapacity`, from `Exercise12_9`), the composite capacity
`log 2 - H(2 p (1 - p))` lies strictly below the common single-channel capacity `log 2 - H(p)`. Two
identical channels give the cleanest witness — the minimum on the right is then a single value —
while still exhibiting the compounding of noise that makes the composition strictly worse.
-/
