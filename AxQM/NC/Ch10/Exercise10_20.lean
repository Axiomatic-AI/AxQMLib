/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.ParityCheckDistance

/-!
# Nielsen & Chuang, Exercise 10.20 — distance from the columns of a parity-check matrix

*(N&C §10.4.1, p. 448.)*

If any d-1 columns of H independent but some d dependent, code defined by H has distance d.

## What the exercise asks, and what is proved

N&C present the code **defined by `H`** as the kernel of the parity check, `{x | H x = 0}` (eq.
(10.57)), and its **distance** `d(C)` as the least Hamming weight of a nonzero codeword (eq.
(10.61)). A word `x` satisfies `H x = 0` exactly when the columns of `H`, weighted by the entries of
`x`, sum to zero: `H *ᵥ x = ∑ⱼ xⱼ · (column j of H)`. So a nonzero codeword of weight `w` is
precisely a nontrivial linear dependence among the `w` columns of `H` in its support, and the code's
distance is the least number of linearly *dependent* columns of `H`. The exercise's hypotheses —
every `d − 1` columns independent, some `d` columns dependent — therefore pin the distance to
exactly `d`. This is what is proved.

The formalisation is in `ToMathlib/InformationTheory/Coding/ParityCheckDistance.lean`, alongside
the classical-coding development (`LinearCode`, `RepetitionCode`, `GeneratorMatrix`,
`ParityCheckMatrix`, `StandardFormGenerator`).

## Declarations

All in `ToMathlib/InformationTheory/Coding/ParityCheckDistance.lean`, in namespace `Matrix`, with
`H`
a parity-check matrix whose columns are the family `fun j => Hᵀ j` and whose code is
`LinearMap.ker H.mulVecLin`. The two `mulVec_*` bridges hold over an arbitrary commutative semiring
(pure matrix–vector algebra); the distance results range over an arbitrary field `K`, as
`LinearCode.minDist` requires (N&C's binary code is `K = ZMod 2`):

* `Matrix.mulVec_eq_sum_smul_transpose` — `H *ᵥ x = ∑ i, x i • Hᵀ i`: matrix–vector multiplication
  as the combination of the columns of `H` weighted by the entries of `x`.
* `Matrix.mulVec_eq_sum_of_subset` — the same restricted to the columns in the support of `x`; the
  bridge between codewords and column dependencies.
* `Matrix.minDist_ker_le_of_not_linearIndepOn` — a linearly *dependent* set `s` of columns bounds
  the distance from above, `d(C) ≤ #s`.
* `Matrix.le_minDist_ker_iff_forall_linearIndepOn` — the characterization: `d ≤ d(C)` iff every set
  of fewer than `d` columns of `H` is linearly independent.
* `Matrix.minDist_ker_eq_of_columns` — **the exercise itself**: if every set of fewer than `d`
  columns is independent and some `d` columns are dependent, then `d(C) = d`.

## Faithfulness

* **Statement.** "The code defined by `H`" is `LinearMap.ker H.mulVecLin` (N&C eq. (10.57), the same
  convention as Exercises 10.18/10.19); "has distance `d`" is `LinearCode.minDist … = d`. "Any
  `d − 1` columns of `H` are linearly independent" is rendered as *every* set of `< d` columns being
  linearly independent (`∀ s, #s < d → LinearIndepOn …`): a set of `d − 1` columns being independent
  forces every smaller subset to be independent too (`LinearIndepOn.mono`), so the two readings
  coincide, and it is the `≤ d − 1` reading that the conclusion `d(C) = d` genuinely requires. "Some
  set of `d` columns is linearly dependent" is `∃ s, #s = d ∧ ¬ LinearIndepOn …`, with `d` columns
  exactly. Nothing is weakened.
* **Generality.** N&C's codes are binary (`ZMod 2`); the distance results are formalised over an
  arbitrary field `K`, an honest strengthening (`ZMod 2` is a special case) consistent with the
  surrounding development, whose minimum-distance theory (`LinearCode.minDist`) is over a general
  field. The two `mulVec_*` column bridges are proved over any commutative semiring, so they are
  reusable throughout the `CommSemiring`/`CommRing` coding development.
-/
