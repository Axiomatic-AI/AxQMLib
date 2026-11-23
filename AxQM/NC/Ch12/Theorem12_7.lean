/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.ChannelCodingTheorem

/-!
# Nielsen & Chuang, Theorem 12.7 (Shannon's noisy channel coding theorem)

*(N&C p. 553.)*

Shannon's noisy channel coding theorem: C(N) = max_p(x) H(X:Y).

Theorem 12.7 is a purely information-theoretic statement about *classical* discrete
memoryless channels: it equates the *operational* capacity `C(N)` (the supremum of rates
achievable by encoding/decoding schemes with vanishing error) with the *information* capacity
`max_{p(x)} H(X : Y)`. Compare the neighbouring classical results Theorem 12.4 (`Theorem12_4`) and
Theorem 12.2.

## The formalisation

The formalisation is in `ToMathlib/InformationTheory/`, built on the mutual information of a
joint distribution (`ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`). N&C's `H(X : Y)`
for a channel fed input distribution `p` is `Real.channelMutualInfo q p`, and the right-hand side
`max_{p(x)} H(X : Y)` of eq. (12.67) is `Real.channelCapacity q`. Entropy is in nats (natural
log) rather than N&C's bits, so
the operational capacity (in bits) equals the information capacity (in nats) *divided by `log 2`*;
the identities and bounds below are base-independent, so this is a faithful reformulation.

**The headline theorem (eq. (12.67), `C(N) = max_{p(x)} H(X : Y)`):**

* `Real.channelOpCapacity_eq_channelCapacity_div`
  (`ToMathlib/InformationTheory/ChannelCodingTheorem.lean`):
  `channelOpCapacity q = channelCapacity q / log 2`. This **is** Theorem 12.7 — the equality of the
  operational and information capacities — proved as the
  `le_antisymm` of the converse and achievability directions below.

**The information capacity `max_{p(x)} H(X : Y)` (the RHS of (12.67)):**

* `Real.IsChannel` — a discrete memoryless channel `q : ι → κ → ℝ`, `q x y = p(y | x)` nonnegative
  and normalized over outputs (N&C eqs. (12.64)–(12.65)).
* `Real.channelOutput`, `Real.channelJoint` — the induced output distribution
  `p_Y(y) = ∑ₓ p(x) q(y | x)` and joint law `p(x) q(y | x)` of `(X, Y)`, with their nonnegativity
  and normalization.
* `Real.channelMutualInfo` — the channel mutual information `H(X : Y)` for input distribution `p`.
* `Real.channelMutualInfo_eq` — N&C eq. (12.68): `H(X : Y) = H(Y) − ∑ₓ p(x) H(Y | X = x)`.
* `Real.channelMutualInfo_nonneg`, `Real.channelMutualInfo_le_log_card` — `0 ≤ H(X : Y) ≤ log |κ|`.
* `Real.channelCapacity` — the information capacity `max_{p(x)} H(X : Y)`, with
  `Real.channelCapacity_nonneg`, `Real.channelCapacity_le_log_card`, and `Real.le_channelCapacity`.
* `Real.exists_isMaxOn_channelMutualInfo` — the `max` of (12.67) is a genuine attained maximum: the
  simplex of input distributions is compact and `channelMutualInfo` is continuous, so the supremum
  is realized at some input distribution. (This capacity-attaining input is what achievability is
  lifted over.)

**The operational capacity `C(N)` (the LHS of (12.67)):**

* `Real.ChannelCode` — a length-`n`, `M`-message block code: an encoder `Cₙ : Fin M → (Fin n → ι)`
  and decoder `Dₙ : (Fin n → κ) → Fin M` (N&C p. 551, with the intended `M = ⌈2 ^ (n R)⌉`).
* `Real.channelSeqProb` — the memoryless `n`-use transition law `p(y | x) = ∏ⱼ q(yⱼ | xⱼ)`, a
  probability distribution over output strings (`Real.sum_channelSeqProb`).
* `Real.ChannelCode.condErrorProb`, `Real.ChannelCode.maxErrorProb` — the conditional error
  probability `p(Dₙ(Y) ≠ m | X = Cₙ(m))` and the block error probability
  `max_m p(Dₙ(Y) ≠ m | X = Cₙ(m))` (N&C eq. (12.66)), each in `[0, 1]`.
* `Real.IsAchievableRate`, `Real.channelOpCapacity` — a rate `R` is achievable when a code family
  with `⌈2 ^ (n R)⌉` messages has block error `→ 0`; `C(N)` is the supremum of achievable rates,
  with `Real.channelOpCapacity_nonneg` and `Real.le_channelOpCapacity`.
* `Real.ChannelCode.half_le_maxErrorProb_of_card_lt`,
  `Real.channelOpCapacity_le_log_card_div` — the trivial converse (pigeonhole): a code with more
  than `|ι|ⁿ` messages has block error `≥ 1/2`, so `C(N) ≤ log₂ |ι|` (also giving `BddAbove`, hence
  a well-defined `sSup`).

**The converse `C(N) ≤ max_{p(x)} H(X : Y)` (complete).** This is proved outright as
`Real.channelOpCapacity_le_channelCapacity_div` (`channelOpCapacity q ≤ channelCapacity q / log 2`,
in `ToMathlib/InformationTheory/NoisyChannel.lean`). It bounds the mutual information
`H(X₁, …, Xₙ : Y₁, …, Yₙ)` of `n` channel uses by `n · max_{p(x)} H(X : Y)` via the
*single-letterization* of the output entropy — the `n`-variable **subadditivity of the Shannon
entropy** `H(Y₁, …, Yₙ) ≤ ∑ᵢ H(Yᵢ)` (`Real.entropyMap_pi_le`,
`ToMathlib/Analysis/SpecialFunctions/EntropySubadditive.lean` — n.b. its two-variable form is N&C
Theorem 11.3) — together with the already-formalised classical Fano inequality
(`Real.condEntropy_le_binEntropy_add_mul_log`, `ToMathlib/InformationTheory/Fano.lean`) and the
classical data-processing inequality `H(X : Z) ≤ H(X : Y)`
(`Real.mutualInfo_marginalFstLast_le_marginalSnd`,
`ToMathlib/Analysis/SpecialFunctions/DataProcessingInequality.lean`, N&C Theorem 11.5).

The two general **single-letterization ingredients** for the mutual-information bound
`H(X₁, …, Xₙ : Y₁, …, Yₙ) ≤ n · max_{p(x)} H(X : Y)` are `Real.entropy_pi_prod`
(product-distribution entropy additivity `H(∏ⱼ rⱼ) = ∑ⱼ H(rⱼ)`, in
`ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`, factoring the noise entropy
`H(Yⁿ | Xⁿ = xⁿ) = ∑ⱼ H(q(·|xⱼ))`) and `Real.entropy_le_sum_entropy_proj` (coordinate subadditivity
`H(Yⁿ) ≤ ∑ⱼ H(Yⱼ)`, in `ToMathlib/Analysis/SpecialFunctions/EntropySubadditive.lean`). Assembling
them
gives the **channel single-letterization bound** `Real.channelMutualInfo_channelSeqProb_le`
(`H(Xⁿ : Yⁿ) ≤ n • channelCapacity q`); combined with the converse joint law
`Real.ChannelCode.jointLaw` of `(W, Xⁿ, Yⁿ)` (a uniform message `W`, its codeword `Xⁿ = Cₙ(W)`, and
the output `Yⁿ`), Fano, and data-processing on the Markov chain `W → Xⁿ → Yⁿ`
(`Real.ChannelCode.one_sub_fanoErrorProb_mul_log_le`), the average error `P̄ₑ → 0` drives
`R log 2 ≤ C`, and `csSup_le` lifts it to `channelOpCapacity q ≤ channelCapacity q / log 2`.

**The achievability `C(N) ≥ max_{p(x)} H(X : Y)` (complete).** The matching direction
`Real.channelCapacity_div_le_channelOpCapacity` (`channelCapacity q / log 2 ≤ channelOpCapacity q`,
in `ToMathlib/InformationTheory/ChannelCodingTheorem.lean`) is proved outright by the **classical
jointly-typical random-coding argument** (Cover–Thomas, Theorem 7.7.1). The chain:

* **Joint AEP** (`ToMathlib/InformationTheory/ChannelTypicalSequence.lean`):
  `Real.channelPairSeqProb`
  (the iid product law of `(Xⁿ, Yⁿ)`) and the jointly typical set `Real.channelTypicalPairs`, with
  the joint asymptotic equipartition `Real.exists_le_sum_channelTypicalPairs` (typical pairs carry
  mass `≥ 1 − δ` for large `n`); and the **packing bound** `Real.sum_indep_channelTypicalPairs_le`
  (under the independent pair law `Real.channelIndepPairProb`, the jointly typical set has mass
  `≤ exp(−n(H(X : Y) − 3ε))`), resting on the three-entropy decomposition
  `Real.channelMutualInfo_eq_entropy_add_entropy_sub_entropy` (`H(X : Y) = H(X) + H(Y) − H(X, Y)`).
* **Random coding** (`ToMathlib/InformationTheory/ChannelRandomCoding.lean`,
  `ToMathlib/InformationTheory/ChannelRandomCodingLimit.lean`): the random codebook law
  `Real.channelCodebookProb`, the joint-typicality decoder `Real.channelJointTypicalCode`, and the
  union bound `Real.channelRandomCode_expectedAvgError_le` giving
  `Real.tendsto_expectedError_channelRandomCode` — for `R log 2 < H(X : Y)` the codebook-*averaged*
  decoding error tends to `0`.
* **Expurgation** (`ToMathlib/InformationTheory/ChannelExpurgation.lean`): `Real.ChannelCode.comp`
  and
  `Real.exists_channelCode_maxErrorProb_le` — average error `≤ a` on `M` messages yields *maximum*
  error `≤ 2a` on `⌈M/2⌉` messages (the probabilistic method + message sub-selection), converting
  N&C's average-error criterion to the maximum-error criterion of eq. (12.66).
* **Fixed-input achievability** (`ToMathlib/InformationTheory/ChannelAchievability.lean`):
  `Real.isAchievableRate_of_lt_channelMutualInfo` — assembling the probabilistic method
  (`Real.exists_le_weighted_sum`), the per-`n` expurgation, and the rate arithmetic
  (`Real.isAchievableRate_of_forall_exists_maxErrorProb_le`) into: `R log 2 < channelMutualInfo q p
  ⟹ IsAchievableRate q R`.

Lifting fixed-input achievability over the capacity-attaining input
(`exists_isMaxOn_channelMutualInfo`) gives `channelCapacity_div_le_channelOpCapacity`: for every
`R < channelCapacity q / log 2`, `R log 2 < channelCapacity q = channelMutualInfo q p⋆` so `R` is
achievable, hence `R ≤ channelOpCapacity q`; as this holds for all such `R`, the supremum obeys it.

**The equality.** `le_antisymm` of the converse and achievability directions yields the headline
`Real.channelOpCapacity_eq_channelCapacity_div`, `C(N) = max_{p(x)} H(X : Y)`. Note that N&C proves
Theorem 12.7 **nowhere in the classical text** — it states eq. (12.67) without proof and instead
develops the quantum Holevo–Schumacher–Westmoreland theorem (Theorem 12.8, `Theorem12_8`), leaving
the classical derivation to Exercise 12.12 ("Adapt the HSW proof to prove Shannon's noisy channel
coding theorem"). The formalisation here proves the full classical equality directly via the
Cover–Thomas random-coding route, which is **strictly more** than the textbook establishes.

## Summary

Both capacity definitions (`Real.channelCapacity = max_{p(x)} H(X : Y)`,
`Real.channelOpCapacity = C(N)`) and the full equality
`Real.channelOpCapacity_eq_channelCapacity_div : channelOpCapacity q = channelCapacity q / log 2`
are in `ToMathlib/InformationTheory/` (converse in `NoisyChannel.lean`,
achievability across `ChannelTypicalSequence.lean` → `ChannelRandomCoding.lean` →
`ChannelRandomCodingLimit.lean` → `ChannelExpurgation.lean` → `ChannelAchievability.lean` →
`ChannelCodingTheorem.lean`).
-/
