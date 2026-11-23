/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Minimum distance from the columns of a parity-check matrix

Following Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.1, the code
**defined by a parity-check matrix** `H` is the kernel of the check map `x ↦ H *ᵥ x`
(`LinearMap.ker H.mulVecLin`; N&C eq. (10.57)). A word `x` is a codeword exactly when the columns
of `H` weighted by the entries of `x` sum to zero — `H *ᵥ x = ∑ⱼ xⱼ • (column j of H)` — so a
nonzero codeword of Hamming weight `w` is precisely a nontrivial linear dependence among `w`
columns of `H`. Consequently the minimum distance of the code is the least number of linearly
*dependent* columns of `H`.

This file proves **Nielsen & Chuang, Exercise 10.20** (p. 448): *if any `d − 1` columns of `H` are
linearly independent, but some `d` columns are linearly dependent, then the code defined by `H` has
distance `d`.*

The columns of `H : Matrix parity ι K` are the family `fun j => Hᵀ j : ι → (parity → K)` (the `j`-th
column of `H` is the `j`-th row of `Hᵀ`), and "a set `s` of columns is linearly independent" is
`LinearIndepOn K (fun j => Hᵀ j) ↑s`.

## Main results

* `Matrix.mulVec_eq_sum_smul_transpose`: `H *ᵥ x = ∑ i, x i • Hᵀ i` — matrix–vector multiplication
  as the combination of the columns of `H` weighted by the entries of `x` (the commutative form of
  `Matrix.mulVec_eq_sum`, dropping the `MulOpposite.op`).
* `Matrix.minDist_ker_le_of_not_linearIndepOn`: a *dependent* set `s` of columns bounds the distance
  from above, `d(C) ≤ #s` — the dependence gives a nonzero codeword supported on `s`.
* `Matrix.le_minDist_ker_iff_forall_linearIndepOn`: **the characterization** — `d ≤ d(C)` iff every
  set of fewer than `d` columns of `H` is linearly independent. This packages "any `d − 1` columns
  independent ⟺ no nonzero codeword of weight `< d`".
* `Matrix.minDist_ker_eq_of_columns`: **Exercise 10.20** — combining the two, if every set of fewer
  than `d` columns is independent and some `d` columns are dependent, then `d(C) = d`.

## Implementation notes

The bridge between codewords and column dependencies is `Matrix.mulVec_eq_sum_of_subset`: for a
word `x` vanishing off a finset `s`, `H *ᵥ x = ∑ i ∈ s, x i • Hᵀ i`. A dependence among the
columns in `s` — a nonzero coefficient vector `f` with `∑ i ∈ s, f i • Hᵀ i = 0` (via
`linearIndepOn_finset_iff`) — becomes the codeword `fun i => if i ∈ s then f i else 0`, whose
support lies in `s`; conversely a nonzero codeword's support is a dependent set. Hamming weight is
the cardinality of the support finset (`hammingNorm x = {i | x i ≠ 0}.card`), so weights and
dependent-set sizes match up directly. This indicator-codeword construction is isolated in
`minDist_ker_le_of_not_linearIndepOn`; the `≥` direction of the characterization then reuses that
lemma by contraposition rather than rebuilding the indicator.

The two `mulVec_*` lemmas are stated over an arbitrary commutative semiring (they are pure
matrix–vector algebra); the distance results range over an arbitrary field `K`, which is what
`LinearCode.minDist` requires. N&C's binary codes are the case `K = ZMod 2`.
-/

@[expose] public section

namespace Matrix

section Columns

variable {R : Type*} {parity ι : Type*} [CommSemiring R] [Fintype ι]

/-- Matrix–vector multiplication as a combination of the **columns** of `H`: `H *ᵥ x` is the sum of
the columns of `H` (the rows `Hᵀ i` of the transpose) weighted by the entries `x i`. This is the
commutative form of `Matrix.mulVec_eq_sum`, without the `MulOpposite.op` needed in the
noncommutative statement. -/
theorem mulVec_eq_sum_smul_transpose (H : Matrix parity ι R) (x : ι → R) :
    H *ᵥ x = ∑ i, x i • Hᵀ i := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.transpose_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- If a word `x` vanishes off a finset `s`, then `H *ᵥ x` is the combination of just the columns of
`H` indexed by `s`: `H *ᵥ x = ∑ i ∈ s, x i • Hᵀ i`. This is the bridge turning a codeword (or a
column dependence) supported on `s` into a relation among the columns in `s`. -/
theorem mulVec_eq_sum_of_subset (H : Matrix parity ι R) {x : ι → R} {s : Finset ι}
    (hx : ∀ i ∉ s, x i = 0) : H *ᵥ x = ∑ i ∈ s, x i • Hᵀ i := by
  rw [mulVec_eq_sum_smul_transpose]
  exact (Finset.sum_subset (Finset.subset_univ s)
    (fun i _ hi => by rw [hx i hi, zero_smul])).symm

end Columns

section Distance

variable {K : Type*} {parity ι : Type*} [Field K] [Fintype ι] [DecidableEq K]

/-- A **linearly dependent set of columns bounds the distance**: if the columns of `H` indexed by a
finset `s` are linearly dependent, then the code `ker H.mulVecLin` defined by `H` has minimum
distance at most `#s`. The dependence, extended by zero, is a nonzero codeword supported on `s` and
hence of Hamming weight at most `#s`. -/
theorem minDist_ker_le_of_not_linearIndepOn (H : Matrix parity ι K) {s : Finset ι}
    (hs : ¬ LinearIndepOn K (fun j => Hᵀ j) (↑s : Set ι)) :
    LinearCode.minDist (LinearMap.ker H.mulVecLin) ≤ (s.card : ℕ∞) := by
  classical
  rw [linearIndepOn_finset_iff] at hs
  push Not at hs
  obtain ⟨f, hf0, i0, hi0s, hi0⟩ := hs
  set x : ι → K := fun i => if i ∈ s then f i else 0
  have hval : ∀ i, x i = if i ∈ s then f i else 0 := fun _ => rfl
  have hxsupp : ∀ i ∉ s, x i = 0 := fun i hi => by rw [hval, ite_eq_right hi]
  have hxmem : x ∈ LinearMap.ker H.mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_eq_sum_of_subset H hxsupp, ← hf0]
    exact Finset.sum_congr rfl (fun i hi => by rw [hval i, ite_eq_left hi])
  have hxne : x ≠ 0 := fun h => hi0 (by simpa [hval, hi0s] using congrFun h i0)
  calc LinearCode.minDist (LinearMap.ker H.mulVecLin)
      ≤ (hammingNorm x : ℕ∞) := LinearCode.minDist_le_hammingNorm hxmem hxne
    _ ≤ (s.card : ℕ∞) := by
        rw [Nat.cast_le]
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter] at hi
        by_contra hcon
        exact hi.2 (hxsupp i hcon)

/-- **The distance–column-independence characterization.** A lower bound `d ≤ d(C)` on the minimum
distance of the code `C = ker H.mulVecLin` defined by a parity-check matrix `H` holds exactly when
every set of fewer than `d` columns of `H` is linearly independent. Equivalently, `d ≤ d(C)` iff `H`
has no nonzero codeword of weight `< d`, which is the same as no nontrivial dependence among fewer
than `d` columns. -/
theorem le_minDist_ker_iff_forall_linearIndepOn (H : Matrix parity ι K) (d : ℕ) :
    (d : ℕ∞) ≤ LinearCode.minDist (LinearMap.ker H.mulVecLin) ↔
      ∀ s : Finset ι, s.card < d → LinearIndepOn K (fun j => Hᵀ j) (↑s : Set ι) := by
  constructor
  · -- If the distance is `≥ d`, a `< d`-column set cannot be dependent, else it would lower `d(C)`.
    intro h s hs
    by_contra hdep
    have hle := minDist_ker_le_of_not_linearIndepOn H hdep
    have hcard : (d : ℕ∞) ≤ (s.card : ℕ∞) := h.trans hle
    rw [Nat.cast_le] at hcard
    omega
  · -- Conversely, every nonzero codeword's support is a dependent column set, hence of size `≥ d`.
    intro h
    rw [LinearCode.le_minDist_iff]
    intro c hc hc0
    rw [Nat.cast_le]
    by_contra hlt
    push Not at hlt
    set s : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hsdef
    have hscard : s.card = hammingNorm c := rfl
    have hsc : s.card < d := by rw [hscard]; exact hlt
    have hli := h s hsc
    rw [linearIndepOn_finset_iff] at hli
    have hcsupp : ∀ i ∉ s, c i = 0 := by
      intro i hi
      rw [hsdef, Finset.mem_filter] at hi
      push Not at hi
      exact hi (Finset.mem_univ i)
    have hsum : ∑ i ∈ s, c i • Hᵀ i = 0 := by
      rw [← mulVec_eq_sum_of_subset H hcsupp]
      rwa [LinearMap.mem_ker, mulVecLin_apply] at hc
    have hall := hli c hsum
    refine hc0 (funext fun i => ?_)
    by_cases hi : i ∈ s
    · exact hall i hi
    · exact hcsupp i hi

/-- **Nielsen & Chuang, Exercise 10.20** (p. 448). If every set of fewer than `d` columns of the
parity-check matrix `H` is linearly independent (equivalently, any `d − 1` columns are independent),
but some set of `d` columns is linearly dependent, then the code `ker H.mulVecLin` defined by `H`
has minimum distance exactly `d`. -/
theorem minDist_ker_eq_of_columns (H : Matrix parity ι K) {d : ℕ}
    (hindep : ∀ s : Finset ι, s.card < d → LinearIndepOn K (fun j => Hᵀ j) (↑s : Set ι))
    (hdep : ∃ s : Finset ι, s.card = d ∧ ¬ LinearIndepOn K (fun j => Hᵀ j) (↑s : Set ι)) :
    LinearCode.minDist (LinearMap.ker H.mulVecLin) = (d : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨s, hscard, hsdep⟩ := hdep
    calc LinearCode.minDist (LinearMap.ker H.mulVecLin)
        ≤ (s.card : ℕ∞) := minDist_ker_le_of_not_linearIndepOn H hsdep
      _ = (d : ℕ∞) := by rw [hscard]
  · exact (le_minDist_ker_iff_forall_linearIndepOn H d).mpr hindep

end Distance

end Matrix
