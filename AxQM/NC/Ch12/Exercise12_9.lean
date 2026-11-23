/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.BinaryChannels

/-!
# Nielsen & Chuang, Exercise 12.9 (erasure channel capacity)

*(N&C p. 553.)*

Erasure channel: capacity is 1-p; and exceeds binary symmetric channel capacity.

Exercise 12.9 is a purely information-theoretic computation about *classical* discrete memoryless
channels: it evaluates the information capacity `max_{p(x)} H(X : Y)` (the right-hand side of
Shannon's noisy channel coding theorem, N&C Theorem 12.7, `Theorem12_7`) for the erasure channel
and the binary symmetric channel.

Entropy is in *nats* (natural log) rather than N&C's *bits*, so N&C's `1` is our `log 2`; capacities
scale by this global factor, so the results are faithful reformulations.

## The formalisation

The formalisation is in `ToMathlib/InformationTheory/BinaryChannels.lean`, built on the discrete
memoryless channel / information capacity of `ToMathlib/InformationTheory/NoisyChannel.lean`.

**Part (1) — the erasure channel and its capacity `1 − p`:**

* `Real.erasureChannel` — the erasure channel `Fin 2 → Option (Fin 2) → ℝ` with erasure probability
  `r` (`none` is the erasure symbol `e`, `some z` the transmitted bit).
* `Real.isChannel_erasureChannel` — it is a discrete memoryless channel for `0 ≤ r ≤ 1`.
* `Real.erasureChannel_channelMutualInfo` — `H(X : Y) = (1 − r) · H(X)`.
* `Real.erasureChannel_channelCapacity` — the capacity is `(1 − r) · log 2` (N&C's `1 − p`, nats).

The capacity computation uses `Real.channelCapacity_eq_of_isMaxOn` — a reusable "capacity as an
attained maximum" tool added to `ToMathlib/InformationTheory/NoisyChannel.lean` (it is about the
general `channelCapacity` API, not binary channels specifically).

**Part (2) — the binary symmetric channel and the capacity comparison:**

* `Real.bscChannel` — the binary symmetric channel `Fin 2 → Fin 2 → ℝ` with crossover probability
  `p` (bit transmitted with probability `1 − p`, flipped with probability `p`).
* `Real.isChannel_bscChannel` — it is a discrete memoryless channel for `0 ≤ p ≤ 1`.
* `Real.bscChannel_channelMutualInfo` — `H(X : Y) = H(Y) − H(p)`.
* `Real.bscChannel_channelCapacity` — the capacity is `log 2 − H(p)` (N&C's `1 − H(p)`, nats).
* `Real.binEntropy_gt_mul_log_two` — the reusable binary-entropy inequality `H(p) > p · log 2` on
  `0 < p ≤ 1/2`.
* `Real.erasureChannel_capacity_gt_bsc` — **Exercise 12.9 (2):** for `0 < p ≤ 1/2` the erasure
  capacity exceeds the BSC capacity, `channelCapacity (bscChannel p) < channelCapacity
  (erasureChannel p)`.
* `Real.channelCapacity_erasureChannel_lt_bscChannel_at_one` — the formal *refutation* of the
  unrestricted claim: at `p = 1` the erasure capacity (`0`) is strictly *less* than the BSC
  capacity (`log 2`), so the `0 < p ≤ 1/2` hypothesis is genuinely needed.

The comparison reduces to `H(p) > p · log 2`, since erasure capacity `= (1 − p)·log 2` and BSC
capacity `= log 2 − H(p)`. **Fidelity note.** N&C states part (2) unrestricted, but it is *false* as
printed: as `p → 1` the near-inverting BSC has capacity approaching `log 2` while the erasure
channel's approaches `0`, so `H(p) > p·log 2` fails for `p` near `1`. We therefore both prove the
faithful restricted claim on the standard binary-symmetric-channel noise regime `0 < p ≤ 1/2` (where
the usual BSC convention lives — a crossover `p > 1/2` is relabelled to `1 − p`) *and* formally
refute the universal statement with the concrete counterexample `p = 1`
(`channelCapacity_erasureChannel_lt_bscChannel_at_one`), rather than silently weaken the textbook's
wording. Intuitively (N&C's
"why is this plausible?") the erasure receiver is *told* which bits were lost, whereas the BSC's
flips are silent and must be inferred — a strictly harder task, so the erasure channel transmits
strictly more information.
-/
