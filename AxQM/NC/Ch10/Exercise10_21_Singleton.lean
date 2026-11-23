/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.SingletonBound

/-!
# Nielsen & Chuang, Exercise 10.21 — the Singleton bound

*(N&C §10.4.1, p. 449.)*

Singleton bound: an [n,k,d] code satisfies n-k >= d-1.

## What the exercise asks, and what is proved

An `[n, k, d]` linear code is a `k`-dimensional subspace of the length-`n` word space with minimum
distance `d`; in the library's conventions (`LinearCode`, N&C §10.4.1) these are
`n = Fintype.card ι`, `k = Module.finrank K C`, and `d = LinearCode.minDist C`. The Singleton bound
`n − k ≥ d − 1` is
proved in the equivalent form `d ≤ n − k + 1` (the two agree because a nontrivial code has `d ≥ 1`).

The formalisation is in `ToMathlib/InformationTheory/Coding/SingletonBound.lean`, alongside the
classical-coding development (`LinearCode`, `minDist`, `GeneratorMatrix`, `GilbertVarshamov`).

## Declarations

All in `ToMathlib/InformationTheory/Coding/SingletonBound.lean`, in namespace `LinearCode`, over an
arbitrary field `K` (N&C's binary code is `K = ZMod 2`):

* `LinearCode.finrank_le_of_card_compl_lt_minDist` — **the puncturing bound**, the reusable core:
  for a coordinate set `S` whose complement is smaller than the minimum distance
  (`(Sᶜ.card : ℕ∞) < minDist C`), restricting codewords to `S` is injective, so
  `Module.finrank K C ≤ S.card`.
* `LinearCode.singleton_bound` — **the exercise itself**: for a nontrivial code `C ≠ ⊥`,
  `minDist C ≤ (Fintype.card ι - Module.finrank K C + 1 : ℕ)`, i.e. `d ≤ n − k + 1` (equivalently
  N&C's `n − k ≥ d − 1`).

## Faithfulness

* **Statement.** N&C's `n − k ≥ d − 1` is captured as `d ≤ n − k + 1` (`singleton_bound`). Since a
  nontrivial code has `d ≥ 1`, subtracting `1` recovers the book's inequality exactly; nothing is
  weakened. The minimum distance is compared in `ℕ∞` on the left, matching the `LinearCode.minDist`
  API used throughout the coding development.
* **The `C ≠ ⊥` hypothesis.** The trivial code `{0}` has `minDist = ⊤` and no nonzero codeword, and
  hence no well-defined finite `d` and no `[n, k, d]` parameters; excluding it is faithful to the
  textbook's `[n, k, d]` notation, not a specialisation of the claim.
* **Generality.** The bound is proved over an arbitrary field `K`, so N&C's binary `K = ZMod 2` is a
  special case. The proof is the standard puncturing argument (delete `d − 1` coordinates; the
  restriction to the rest is injective on the code), phrased through the same
  `Module.finrank`/`Fintype.card` conventions as the surrounding files.
-/
