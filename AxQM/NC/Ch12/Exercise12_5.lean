/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.VariableLengthCode

/-!
# Nielsen & Chuang, Exercise 12.5 (variable-length zero-error data compression)

*(N&C p. 542.)*

Variable-length zero-error data compression to any R > H(X) with zero error prob.

The exercise is a purely information-theoretic statement about a concrete variable-length binary
encoding of length-`n` blocks from a finite alphabet: a leading flag bit selects a short
fixed-length index into the typical set or a long uncompressed index, the code is losslessly
decodable (injective), and its expected length per symbol is bounded by any `R > H(X)`.

## The formalisation

The formalisation is in `ToMathlib/InformationTheory/VariableLengthCode.lean`, built on the theorem
of typical sequences (`ToMathlib/InformationTheory/TypicalSequence.lean`, N&C Theorem 12.2). Entropy
is in nats (`Real.entropy`, natural log) while N&C's rate is in bits, so the codeword lengths are
genuine bit counts and the threshold `R > H(X)` (bits) is written `entropy p < Real.log 2 * R`.

**The code and its structural properties:**

* `Real.binBlockCode` — the reusable fixed-length binary block code: a finite type of at most
  `2 ^ w` elements embeds injectively into the length-`w` binary strings `Fin w → Bool`.
* `Real.typicalWidth` / `Real.atypicalWidth` — the two body widths `⌈log₂ |T(n,ε)|⌉` and
  `⌈log₂ dⁿ⌉` (via `Nat.clog 2`).
* `Real.typicalCode` — the variable-length encoder `(Fin n → α) → List Bool`: a flag bit followed by
  a fixed-length index into the typical set (flag `false`) or the full alphabet (flag `true`).
* `Real.typicalCode_length` — the codeword length is `typicalWidth + 1` on typical inputs and
  `atypicalWidth + 1` on atypical inputs (the `+ 1` is the flag bit).
* `Real.typicalCode_injective` — **zero probability of error**: the encoder is injective, so the
  decoder recovers every source block exactly.

**The compression theorem:**

* `Real.atypicalWidth_le` — `atypicalWidth α n ≤ n · ⌈log₂ d⌉`: the uncompressed index costs at most
  `⌈log₂ d⌉` bits per symbol.
* `Real.typicalWidth_le` — `⌈log₂ |T(n,ε)|⌉ ≤ n(H+ε)/log 2 + 1`: the typical index is short, since
  `|T(n,ε)| ≤ exp(n(H+ε))` (N&C Theorem 12.2 (2)).
* `Real.exists_typicalCode_expectedLength_le` — **Exercise 12.5**: for any `R` with
  `entropy p < Real.log 2 * R` (i.e. `R > H(X)` in bits) there is a width `ε > 0` and a block length
  `N` such that for all `n ≥ N` the code `typicalCode p n ε` is injective (zero error) and has
  expected length `∑ₓ pⁿ(x) · (len x) ≤ n · R` (an average of `R` bits per source symbol). The
  typical branch carries almost all the probability at rate `≈ H(X)/log 2`, while the atypical
  branch carries vanishing probability (`1 - P(T) ≤ δ` for large `n`), so the additive constants
  are absorbed as `n → ∞`.
-/
