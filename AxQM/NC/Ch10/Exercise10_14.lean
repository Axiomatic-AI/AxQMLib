/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.RepetitionCode

/-!
# Nielsen & Chuang, Exercise 10.14 — generator matrix of the `[rk, k]` repetition code

*(N&C §10.4.1, p. 446.)*

Write generator matrix encoding k bits using r repetitions each ([rk,k] linear code, rk x k).

## What the exercise asks, and what is proved

This is a statement about a classical linear code. Following
N&C §10.4.1, a generator matrix `G` is an `n × k` matrix, a message `x` is encoded as the column
vector `G *ᵥ x`, and the code is the span of the columns of `G`. The formalisation is in
`ToMathlib/InformationTheory/Coding/RepetitionCode.lean`, alongside the rest of the classical-coding
development (`LinearCode`, `DualCode`, …).

The `rk` codeword positions are indexed by `Fin k × Fin r`, position `(j, s)` being the `s`-th copy
of message symbol `j` — exactly N&C's ordering for the `[6, 2]` example (10.54), whose columns are
`(1,1,1,0,0,0)` and `(0,0,0,1,1,1)`.

## Declarations

All in `ToMathlib/InformationTheory/Coding/RepetitionCode.lean`, over an arbitrary field `K` (N&C's
binary code is `K = ZMod 2`):

* `repetitionGenerator K k r` — **the `rk × k` generator matrix** the exercise asks for:
  `G (j, s) i = 1` iff `i = j`; its `i`-th column is the indicator of the `r` copies of symbol `i`.
* `repetitionGenerator_mulVec` — encoding **repeats each symbol** `r` times: `(G *ᵥ x) (j, s) = x j`
  (N&C eqs. (10.55)–(10.56)).
* `repetitionGenerator_mulVecLin_injective` — for `0 < r` the columns are linearly independent, so
  every message is **uniquely encoded** (N&C's condition, p. 446).
* `repetitionCode K k r` — the code itself, the column span `LinearMap.range (…).mulVecLin`.
* `mem_repetitionCode_iff` — for `0 < r`, a word is a codeword iff it is constant on each block.
* `repetitionCode_finrank` — for `0 < r`, the code has dimension `k`; with block length
  `#(Fin k × Fin r) = k * r`, this is the `[rk, k]` claim.

## Faithfulness

* **Statement.** `repetitionGenerator` is precisely the `rk × k` matrix requested; the `[rk, k]`
  content is split into the block length `k * r` (the cardinality of the index type) and the
  dimension `repetitionCode_finrank = k`. Nothing is weakened.
* **The hypothesis `0 < r`.** The uniqueness/dimension results carry `0 < r` because a symbol must
  be repeated at least once for the columns to be independent — this is the honest hypothesis, not a
  specialisation of the exercise (`r = 0` is the degenerate empty-repetition case N&C does not
  intend). The generator matrix and its encoding action carry no such hypothesis.
* **Generality.** The field is arbitrary; N&C's `ZMod 2` is a special case, and (as N&C themselves
  remark in Exercise 10.19) these constructions extend beyond `ZMod 2`.
-/
