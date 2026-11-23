/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.GeneratorMatrix

/-!
# Nielsen & Chuang, Exercise 10.15 — adding one column of `G` to another gives the same code

*(N&C §10.4.1, p. 446.)*

Adding one column of G to another gives a generator matrix generating the same code.

## What the exercise asks, and what is proved

This is a statement about a classical linear code. Following
N&C §10.4.1, a generator matrix `G` is an `m × n` matrix, a message `x` is encoded as the column
vector `G *ᵥ x`, and the code it generates is the span of the columns of `G` — the range of the
encoding map `x ↦ G *ᵥ x` (`Matrix.mulVecLin`). The formalisation is in
`ToMathlib/InformationTheory/Coding/GeneratorMatrix.lean`, alongside the rest of the
classical-coding development (`LinearCode`, `RepetitionCode`, …).

## Declarations

All in `ToMathlib/InformationTheory/Coding/GeneratorMatrix.lean`, over an arbitrary commutative ring
`R` (N&C's binary code is `R = ZMod 2`):

* `Matrix.addCol M i j` — **the elementary column operation** of the exercise: adds column `i` to
  column `j`, replacing column `j` of `M` with `col j + col i` and leaving the other columns
  unchanged (right multiplication by `Matrix.transvection i j 1`).
* `Matrix.addCol_apply`, `Matrix.addCol_col` — the entry-level and column-family descriptions of
  `addCol`.
* `Matrix.range_mulVecLin_addCol` — **the exercise itself**: for distinct columns `i ≠ j`,
  `LinearMap.range (M.addCol i j).mulVecLin = LinearMap.range M.mulVecLin`, i.e. `M.addCol i j`
  generates the same code as `M`.

## Faithfulness

* **Statement.** The "code" is exactly N&C's set of codewords `{G *ᵥ x}` = the column span
  (`Matrix.range_mulVecLin`), matching the `RepetitionCode` convention; `addCol` is precisely
  "adding one column to another". Nothing is weakened.
* **The hypothesis `i ≠ j`.** N&C says "*one* column … to *another*", i.e. two distinct columns;
  the honest operation adds a column to a *different* one. This is not a specialisation but the
  content of the exercise (adding a column to itself would double it — a different operation).
* **Generality.** The coefficients range over an arbitrary commutative ring, so N&C's `ZMod 2` is a
  special case and (as N&C remark in Exercise 10.19) the result extends beyond `ZMod 2`; over a
  field the two ranges are equal linear codes in the sense of `LinearCode`.
-/
