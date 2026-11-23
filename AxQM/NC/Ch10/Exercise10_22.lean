/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.HammingCode

/-!
# Nielsen & Chuang, Exercise 10.22 — the binary Hamming codes

*(N&C §10.4.2, p. 449.)*

All Hamming codes have distance 3, correct a single-bit error; are [2^r-1,2^r-r-1,3] codes.

## What the exercise asks, and where the formalisation is

The Hamming code, its parity-check matrix, and its minimum distance are linear algebra over the
two-element field `ZMod 2`. The formalisation is in
`ToMathlib/InformationTheory/Coding/HammingCode.lean`, alongside the rest of the classical-coding
development (`LinearCode`, `ParityCheck`, `ParityCheckDistance`, `RepetitionCode`, …).

Following N&C §10.4.2, the Hamming code with parameter `r` is modelled by its parity-check matrix
`H_r`, whose `2^r − 1` columns are indexed by the nonzero vectors `{v : Fin r → ZMod 2 // v ≠ 0}`,
the column indexed by `v` being `v` itself. The code is `LinearMap.ker H_r.mulVecLin` (N&C
eq. (10.57)), and its distance is the least number of linearly dependent columns of `H_r`
(Exercise 10.20, `Matrix.minDist_ker_eq_of_columns`).

## Declarations

All in `ToMathlib/InformationTheory/Coding/HammingCode.lean`, in namespace `Matrix`, over `ZMod 2`:

* `Matrix.hammingParityCheck r` — **the binary Hamming parity-check matrix** `H_r`, the
  `r × (2^r − 1)` matrix whose columns are all the nonzero binary `r`-vectors.
* `Matrix.hammingCode r` — **the Hamming code**, `LinearCode.ofParityCheck (hammingParityCheck r)`.
* `Matrix.hammingParityCheck_linearIndepOn_of_card_lt_three` — any fewer than three columns of `H_r`
  are linearly independent (the `d − 1 = 2` independence hypothesis of Exercise 10.20).
* `Matrix.hammingParityCheck_exists_three_dependent` — for `r ≥ 2` some three columns of `H_r` are
  linearly dependent (the `d = 3` dependence hypothesis of Exercise 10.20).
* `Matrix.hammingCode_minDist` — **the exercise's distance claim**: for `r ≥ 2` the Hamming code has
  minimum distance exactly `3`.
* `Matrix.hammingCode_correctsErrors_one` — **the exercise's correction claim**: for `r ≥ 2` the
  Hamming code corrects a single-bit error (distance `3 ≥ 2·1 + 1`).
* `Matrix.hammingCode_length` — **the length parameter** `n`: the block length is `2^r − 1`, the
  number of nonzero binary `r`-vectors.
* `Matrix.hammingParityCheck_mulVecLin_surjective` — the check map `x ↦ H_r *ᵥ x` is **surjective**
  (`H_r` has full row rank `r`): every vector is `0` or itself a column of `H_r`. This is the
  full-row-rank fact underlying the dimension count.
* `Matrix.hammingCode_finrank` — **the dimension parameter** `k = 2^r − r − 1`: by rank–nullity, the
  code (the kernel of the full-row-rank check map) has dimension `n − r = (2^r − 1) − r`.

Together `Matrix.hammingCode_length` (`n = 2^r − 1`), `Matrix.hammingCode_finrank`
(`k = 2^r − r − 1`) and `Matrix.hammingCode_minDist` (`d = 3`) exhibit the Hamming code as a
`[2^r − 1, 2^r − r − 1, 3]` code, completing the exercise.

## Faithfulness

* **Distance `= 3`, not `≥ 3`.** The exercise asserts the codes *have* distance `3`; the
  formalisation proves the exact equality `Matrix.hammingCode_minDist`, combining "any two columns
  independent" with "some three columns dependent" via Exercise 10.20 — not merely a bound.
* **Single-error correction** is the standard `d ≥ 2t + 1` criterion at `t = 1`
  (`LinearCode.CorrectsErrors`), a genuine consequence of distance `3` rather than a re-assertion.
* **Dimension `k = 2^r − r − 1`, derived not assumed.** The dimension is *computed* from the
  parity-check matrix: the check map is shown surjective (full row rank `r`), and then the exact
  dimension follows by the rank–nullity theorem, `k = n − r`. It is the exact value, and — unlike
  the distance claim — it holds for *every* `r` (at `r = 1` the code is `[1, 0, ·]`, dimension `0`),
  so `Matrix.hammingCode_finrank` carries no `r ≥ 2` hypothesis.
* **Range of `r`.** For `r = 1` there is only one nonzero column, so the "three dependent columns"
  and the distance-`3` claim genuinely require `r ≥ 2` (already `[3, 1, 3]` at `r = 2`, the
  repetition code); the theorems carry this hypothesis, faithful to N&C's regime of interest.
* **Binary.** N&C's Hamming codes are binary (`ZMod 2`); the distance-`3` count is intrinsically
  binary (over a larger field two distinct nonzero columns can be scalar multiples, hence
  dependent), so the formalisation is stated over `ZMod 2` with no spurious generalisation.
-/
