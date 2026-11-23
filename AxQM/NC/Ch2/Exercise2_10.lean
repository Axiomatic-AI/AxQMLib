/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.RankOneMatrix

/-!
# Nielsen & Chuang, Exercise 2.10 (Matrix representation of `|v_j⟩⟨v_k|`)

Matrix representation of the operator |v_j><v_k| in the |v_i> basis.

**Answer.** Its matrix element in row `i`, column `l` is the number N&C compute from the
completeness relation (p. 68): `⟨v_i| (|v_j⟩⟨v_k|) |v_l⟩ = ⟨v_i|v_j⟩ ⟨v_k|v_l⟩ = δ_{ij} δ_{kl}`.
So the matrix is `1` at row `j`, column `k` and `0` everywhere else — the single-entry matrix
`E_{jk}` (`Matrix.single j k 1`).

The statement is pure linear algebra about a general inner-product space: the "operator"
`|v_j⟩⟨v_k|` is Mathlib's rank-one map `InnerProductSpace.rankOne`, and "matrix representation
with respect to the `|v_i⟩` basis" is `LinearMap.toMatrixOrthonormal`.

## The formalisation

In `ToMathlib/Analysis/InnerProductSpace/RankOneMatrix.lean`:

* `LinearMap.toMatrixOrthonormal_rankOne` — for an orthonormal basis `b : OrthonormalBasis n 𝕜 E`
  of a finite-dimensional inner product space,
  `toMatrixOrthonormal b (rankOne 𝕜 (b j) (b k)) = Matrix.single j k 1`.

## N&C ↦ Mathlib dictionary and fidelity

* `V` is a finite-dimensional inner-product space `E` over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`; N&C's
  `ℂ` is the special case). N&C's `|v_i⟩` orthonormal basis is `b : OrthonormalBasis n 𝕜 E` with `n`
  a `Fintype` index set (N&C's `1, …, d`).
* The **operator** `|v_j⟩⟨v_k|` is `InnerProductSpace.rankOne 𝕜 (b j) (b k)`, whose action
  `z ↦ ⟪b k, z⟫ • b j` is exactly the ket-bra: Mathlib's sesquilinear convention (conjugate-linear
  in the first slot) matches N&C's `⟨v_k|z⟩`.
* The **matrix representation** in the `|v_i⟩` basis is `LinearMap.toMatrixOrthonormal b`, whose
  `(i, l)` entry is `⟪b i, f (b l)⟫` — precisely N&C's convention that `A` has matrix element
  `⟨w_j|A|v_i⟩` in the `i`th column and `j`th row (p. 68, eq. 2.25).
* The **answer** `Matrix.single j k 1` is N&C's `E_{jk}` (the single-entry / standard-basis matrix
  with a `1` at position `(j, k)`), obtained from `δ_{ij} δ_{kl}` via orthonormality.

The statement is a faithful transcription, not a weakening: it fixes no dimension, holds for every
pair of basis indices `j, k`, and computes the full matrix (all entries), which is what "the matrix
representation" asks for.
-/
