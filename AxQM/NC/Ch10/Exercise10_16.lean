/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.ParityCheck
import ToMathlib.InformationTheory.Coding.ParityCheckStandardForm

/-!
# Nielsen & Chuang, Exercise 10.16 — parity-check row operations and the standard form

*(N&C §10.4.1, p. 447.)*

Adding one row of parity check matrix to another leaves code unchanged; standard form [A|I].

## What the exercise asks, and where the formalisation is

A parity-check matrix `H` and its code are pure linear algebra over a field. The formalisation is
in `ToMathlib/InformationTheory/Coding/ParityCheck.lean` (first claim) and
`ToMathlib/InformationTheory/Coding/ParityCheckStandardForm.lean` (standard form), alongside the
classical-coding development (`LinearCode`, `DualCode`, `RepetitionCode`, …).

Following N&C §10.4.1 eq. (10.57), the code specified by a parity-check matrix `H` is the kernel of
`x ↦ H *ᵥ x`, i.e. the words `x` with `H *ᵥ x = 0`. This is `LinearCode.ofParityCheck H`.

## Declarations

Over an arbitrary field `K` (N&C's binary codes are `K = ZMod 2`):

In `ToMathlib/InformationTheory/Coding/ParityCheck.lean`:

* `LinearCode.ofParityCheck` — **the code cut out by a parity-check matrix** `H`, the kernel
  `LinearMap.ker H.mulVecLin` (N&C eq. (10.57)).
* `LinearCode.mem_ofParityCheck_iff` — its codewords are exactly the words annihilated by `H`.
* `LinearCode.ofParityCheck_updateRow_add` — **the exercise's first claim**: for `a ≠ b`, adding
  row `a` to row `b` (replacing `H b` by `H b + H a`) yields a parity-check matrix for the *same*
  code.
* `LinearCode.ofParityCheck_updateRow_add_smul` — the general elementary row operation
  `H b + c • H a` (`c = 1` is N&C's statement; over `ZMod 2` the only nontrivial coefficient is
  `1`).

In `ToMathlib/InformationTheory/Coding/ParityCheckStandardForm.lean` (standard form, second claim):

* `Matrix.exists_injective_isUnit_submatrix_of_mulVecLin_surjective` — the linear-algebra crux: a
  full-row-rank matrix (one with `x ↦ H *ᵥ x` surjective) has an **invertible square column
  submatrix**, the invertible `(n − k) × (n − k)` minor.
* `LinearCode.ofParityCheck_mul_left_of_isUnit` — **an invertible row operation leaves the code
  unchanged**, packaging an entire Gaussian-elimination sequence of `ofParityCheck_updateRow_add`
  steps into a single unit `E`.
* `LinearCode.exists_isUnit_submatrix_eq_one_of_mulVecLin_surjective` — **the standard form**: a
  full-row-rank parity check `H` can be reduced by an invertible row operation `E` and a choice of
  `n − k` coordinates `f` to a matrix `E * H` with an identity submatrix on those coordinates,
  `(E * H).submatrix id f = 1`, checking the same code `ofParityCheck (E * H) = ofParityCheck H`.

## Faithfulness

* **First claim.** `ofParityCheck_updateRow_add` is exactly N&C's "adding one row of the parity
  check matrix to another does not change the code", stated as an equality of the two codes; the
  `_add_smul` generalisation strengthens rather than weakens it. The proof is elementary and uses no
  invertibility machinery.
* **Standard form `[A | I_{n−k}]`.** `exists_isUnit_submatrix_eq_one_of_mulVecLin_surjective` is
  N&C's second sentence: "using Gaussian elimination [the invertible row operation `E`] and swapping
  of bits [the choice `f` of which `n − k` coordinates carry the identity block] it is possible to
  assume the standard form `[A | I_{n−k}]`". The identity block sits on the coordinates `f` and the
  remaining columns of `E * H` form `A`; reordering the coordinates so that `f` comes last displays
  `E * H = [A | I]`. The full-row-rank hypothesis is not a weakening but a necessity — `[A | I]` has
  rank `n − k`, exactly the rank of an `[n, k]` code's parity check. See that file's module
  docstring for the design of the statement (an identity submatrix rather than a physically permuted
  `Matrix.fromCols A 1`, avoiding a `ι ≃ κ ⊕ μ` reindexing) and its faithfulness discussion.
-/
