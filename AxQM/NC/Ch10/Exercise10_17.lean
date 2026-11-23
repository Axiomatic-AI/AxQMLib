/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.RepetitionCode

/-!
# Nielsen & Chuang, Exercise 10.17 — a parity-check matrix for the [6, 2] repetition code

*(N&C §10.4.1, p. 447.)*

Find a parity check matrix for the [6,2] repetition code of (10.54).

## What the exercise asks, and what is proved

N&C (p. 447) give an *alternative* definition of a linear code: an `[n, k]` code is the set of words
`x` with `H x = 0` for an `n − k` by `n` **parity-check matrix** `H` with linearly independent rows,
i.e. the code is the *kernel* of `H` (eq. (10.57)). The exercise asks for such an `H` for the
`[6, 2]` repetition code of (10.54), which encodes two bits by repeating each of them three times.

The formalisation is in `ToMathlib/InformationTheory/Coding/RepetitionCode.lean`, alongside the
rest of the repetition-code development (`repetitionGenerator`, `repetitionCode`, …).

## Declarations

All in `ToMathlib/InformationTheory/Coding/RepetitionCode.lean`, over an arbitrary field `K` (N&C's
binary code is `K = ZMod 2`), for the `[k(m+1), k]` repetition code with `r = m + 1` repetitions:

* `repetitionParityCheck K k m` — **the parity-check matrix**: the `k·m × k(m+1)` matrix `H` whose
  row `(j, s)` imposes `x (j, s.castSucc) = x (j, s.succ)` (entry `1` at `(j, s.castSucc)`, `−1` at
  `(j, s.succ)`, `0` elsewhere). Over `ZMod 2` (where `−1 = 1`) this is the all-`0`/`1` matrix N&C
  describe.
* `repetitionParityCheck_mulVec` — `H` computes adjacent differences within each block.
* `repetitionParityCheck_ker` — **the exercise itself**:
  `ker (repetitionParityCheck K k m).mulVecLin = repetitionCode K k (m + 1)`, i.e. `H` is a
  parity-check matrix for the repetition code (its kernel is the code, N&C eq. (10.57)).
* `repetitionParityCheck_rank`, `repetitionParityCheck_row_linearIndependent` — `H` has full row
  rank `k·m = n − k`, so its rows are linearly independent — N&C's requirement (p. 447).

The `[6, 2]` code of (10.54) is the instance `k = 2`, `m = 2`: `repetitionParityCheck K 2 2` is a
`4 × 6` parity-check matrix for `repetitionCode K 2 3`, and `repetitionParityCheck_ker` specialized
to `k = 2`, `m = 2` is Exercise 10.17. Over `ZMod 2` its four rows are

```
⎡ 1 1 0 0 0 0 ⎤
⎢ 0 1 1 0 0 0 ⎥
⎢ 0 0 0 1 1 0 ⎥
⎣ 0 0 0 0 1 1 ⎦
```

(columns indexed `(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)`), the two-block analogue of N&C's
`[3, 1]` example `H = [[1,1,0],[0,1,1]]` (10.58).

## Faithfulness

* **Statement.** "Parity-check matrix for the code" is captured exactly by N&C's own equivalent
  characterization: `H` whose kernel is the code (`repetitionParityCheck_ker`), with linearly
  independent rows (`repetitionParityCheck_row_linearIndependent`). Nothing is weakened.
* **Signed vs. binary entries.** N&C work over `ZMod 2`, where `−1 = 1`, so the `[6, 2]` instance
  has the all-`0`/`1` entries the book displays. The general definition uses signed adjacent
  differences because over a general field only the *difference* `x(j,s) − x(j,s+1)` — not the
  sum — vanishes
  exactly on constant blocks; N&C note in Exercise 10.19 that these constructions extend beyond
  `ZMod 2`, and this is the honest generalization.
* **Generality.** The construction and its parity-check property hold for every `[k(m+1), k]`
  repetition code, with the `[6, 2]` code as the `k = 2`, `m = 2` case; the exercise's specific
  answer is recovered by instantiation, not re-proved.
-/
