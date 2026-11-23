/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.ParityCheck
public import ToMathlib.InformationTheory.Coding.ParityCheckDistance
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The binary Hamming codes

Following Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.2 (p. 449), the
**Hamming code** with parameter `r` is the binary linear code whose parity-check matrix `H_r` has as
its columns *all* the `2^r − 1` nonzero binary vectors of length `r`. This file constructs `H_r` and
its code and proves the first-order facts of N&C **Exercise 10.22**: the code has minimum distance
`3`, so it corrects a single-bit error, and its block length is `n = 2^r − 1`.

The columns of `H_r` are indexed by the subtype `{v : Fin r → ZMod 2 // v ≠ 0}` of nonzero vectors,
and the column indexed by `v` is `v` itself (`H_r i v = v i`, so `H_rᵀ w = ↑w`). This makes the
distance argument a direct instance of Exercise 10.20
(`Matrix.minDist_ker_eq_of_columns`): the columns *are* the nonzero vectors, so

* any *two* distinct columns are linearly independent — over `ZMod 2` the only nonzero scalar is
  `1`, so a nontrivial relation between two distinct nonzero vectors would force them equal; while
* some *three* columns are dependent — for `r ≥ 2` the columns `e₀`, `e₁`, `e₀ + e₁` sum to zero.

Hence the least number of dependent columns is `3`, which is the code's minimum distance.

## Main definitions

* `Matrix.hammingParityCheck r`: the `r × (2^r − 1)` binary Hamming parity-check matrix `H_r`.
* `Matrix.hammingCode r`: the Hamming code, `LinearCode.ofParityCheck (hammingParityCheck r)`
  (`= ker (hammingParityCheck r).mulVecLin`, N&C eq. (10.57)), with the unfolding/membership API
  `Matrix.hammingCode_eq` and `Matrix.mem_hammingCode_iff`.

## Main results

* `Matrix.hammingCode_minDist`: **Exercise 10.22, distance.** For `r ≥ 2` the Hamming code has
  minimum distance exactly `3`.
* `Matrix.hammingCode_correctsErrors_one`: **Exercise 10.22, correction.** For `r ≥ 2` the Hamming
  code corrects a single-bit error (distance `3 ≥ 2·1 + 1`).
* `Matrix.hammingCode_length`: **Exercise 10.22, length.** The block length is `n = 2^r − 1`, the
  number of nonzero binary `r`-vectors.
* `Matrix.hammingParityCheck_mulVecLin_surjective`: the check map `x ↦ H_r *ᵥ x` is **surjective**
  (`H_r` has full row rank `r`) — every vector is `0` or itself a column of `H_r`.
* `Matrix.hammingCode_finrank`: **Exercise 10.22, dimension.** The code has dimension
  `k = 2^r − r − 1`, by rank–nullity from the full row rank `r`.

Together with the distance `d = 3` and length `n = 2^r − 1`, this proves the Hamming code is a
`[2^r − 1, 2^r − r − 1, 3]` code, completing Exercise 10.22.

## Implementation notes

Everything here is classical linear algebra over the two-element field `ZMod 2`. Compare the rest
of the classical-coding development (`LinearCode`, `ParityCheck`, `ParityCheckDistance`,
`RepetitionCode`, …). The distance-3 count is genuinely binary: over a larger field two distinct
nonzero vectors can be scalar multiples (hence dependent), so "any two columns independent" would
fail; N&C's Hamming codes are binary, matching `K = ZMod 2`.
-/

@[expose] public section

/-- Over `ZMod 2`, a linear relation `c • u + d • v = 0` between two distinct nonzero vectors is
trivial (`c = d = 0`): the only nonzero scalar is `1`, so the sole nontrivial relation would be
`u + v = 0`, i.e. `u = v`, contradicting distinctness. This is the pairwise linear independence of
the columns of the Hamming parity-check matrix. -/
private theorem eq_zero_and_eq_zero_of_zmod2_smul_add_smul {r : ℕ} {u v : Fin r → ZMod 2}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) {c d : ZMod 2} (h : c • u + d • v = 0) :
    c = 0 ∧ d = 0 := by
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hZ : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hZ c with rfl | rfl <;> rcases hZ d with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, one_smul, zero_add] at h; exact (hv h).elim
  · rw [one_smul, zero_smul, add_zero] at h; exact (hu h).elim
  · rw [one_smul, one_smul] at h
    exact (huv (funext fun i => key _ _ (congrFun h i))).elim

namespace Matrix

variable {r : ℕ}

/-- The **binary Hamming parity-check matrix** `H_r`: the `r × (2^r − 1)` matrix over `ZMod 2` whose
columns are exactly the nonzero binary vectors of length `r`. The columns are indexed by the subtype
`{v : Fin r → ZMod 2 // v ≠ 0}`, and the column indexed by `v` is `v` itself: `H_r i v = v i`
(Nielsen & Chuang, §10.4.2, p. 449). -/
def hammingParityCheck (r : ℕ) : Matrix (Fin r) {v : Fin r → ZMod 2 // v ≠ 0} (ZMod 2) :=
  Matrix.of fun i v => (v : Fin r → ZMod 2) i

/-- The columns of the Hamming parity-check matrix are the nonzero vectors themselves: the column
indexed by `w` (the `w`-th row of the transpose) is `↑w`. -/
@[simp] theorem hammingParityCheck_transpose_apply (w : {v : Fin r → ZMod 2 // v ≠ 0}) :
    (hammingParityCheck r)ᵀ w = (w : Fin r → ZMod 2) := rfl

/-- Each column of the Hamming parity-check matrix is nonzero. -/
theorem hammingParityCheck_transpose_ne_zero (w : {v : Fin r → ZMod 2 // v ≠ 0}) :
    (hammingParityCheck r)ᵀ w ≠ 0 := by
  rw [hammingParityCheck_transpose_apply]; exact w.2

/-- The **Hamming code** with parameter `r`: the binary linear code cut out by the Hamming
parity-check matrix `H_r`, i.e. the words annihilated by `H_r` (Nielsen & Chuang, §10.4.2,
eq. (10.57)). -/
noncomputable def hammingCode (r : ℕ) : LinearCode (ZMod 2) {v : Fin r → ZMod 2 // v ≠ 0} :=
  LinearCode.ofParityCheck (hammingParityCheck r)

/-- The Hamming code is the kernel of its parity-check map — the unfolding lemma giving
`hammingCode`'s parity-check presentation without reaching through the definitions. -/
theorem hammingCode_eq (r : ℕ) :
    hammingCode r = LinearMap.ker (hammingParityCheck r).mulVecLin := rfl

/-- A word `x` is a codeword of the Hamming code exactly when `H_r` annihilates it,
`H_r *ᵥ x = 0` (Nielsen & Chuang, eq. (10.57)). -/
theorem mem_hammingCode_iff {r : ℕ} {x : {v : Fin r → ZMod 2 // v ≠ 0} → ZMod 2} :
    x ∈ hammingCode r ↔ hammingParityCheck r *ᵥ x = 0 :=
  LinearCode.mem_ofParityCheck_iff

/-- **Any fewer-than-three columns of `H_r` are linearly independent.** A set `s` of fewer than
three columns of the Hamming parity-check matrix is linearly independent: a nontrivial relation
would be supported on one column (impossible, the columns are nonzero) or on two distinct columns
(impossible over `ZMod 2`, by `eq_zero_and_eq_zero_of_zmod2_smul_add_smul`). This is the `d − 1 = 2`
independence hypothesis of Exercise 10.20. -/
theorem hammingParityCheck_linearIndepOn_of_card_lt_three
    (s : Finset {v : Fin r → ZMod 2 // v ≠ 0}) (hs : s.card < 3) :
    LinearIndepOn (ZMod 2) (fun j => (hammingParityCheck r)ᵀ j) (↑s : Set _) := by
  classical
  rw [linearIndepOn_finset_iff]
  intro g hg i hi
  by_contra hgi
  -- Restrict to the support `T` of `g` inside `s`; it is nonempty (contains `i`) and small.
  set T : Finset {v : Fin r → ZMod 2 // v ≠ 0} := s.filter (fun j => g j ≠ 0) with hTdef
  have hTsub : T ⊆ s := Finset.filter_subset _ _
  have hiT : i ∈ T := Finset.mem_filter.mpr ⟨hi, hgi⟩
  have hTg : ∀ j ∈ T, g j ≠ 0 := fun j hj => (Finset.mem_filter.mp hj).2
  have hsum : ∑ j ∈ T, g j • (hammingParityCheck r)ᵀ j = 0 :=
    (Finset.sum_subset hTsub fun x hxs hxT => by
      have hx0 : g x = 0 := by by_contra hx; exact hxT (Finset.mem_filter.mpr ⟨hxs, hx⟩)
      rw [hx0, zero_smul]).trans hg
  have hTcard : T.card ≤ 2 := le_trans (Finset.card_le_card hTsub) (by omega)
  have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨i, hiT⟩
  rcases (by omega : T.card = 1 ∨ T.card = 2) with hc | hc
  · -- One-column relation: a single nonzero column would have to vanish.
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hga : g a ≠ 0 := hTg a (by rw [ha]; exact Finset.mem_singleton_self a)
    rw [ha, Finset.sum_singleton] at hsum
    rcases smul_eq_zero.mp hsum with h | h
    · exact hga h
    · exact hammingParityCheck_transpose_ne_zero a h
  · -- Two-column relation: two distinct nonzero binary columns are independent.
    obtain ⟨a, b, hab, ha⟩ := Finset.card_eq_two.mp hc
    have hga : g a ≠ 0 := hTg a (by rw [ha]; exact Finset.mem_insert_self a {b})
    rw [ha, Finset.sum_pair hab] at hsum
    have hcolab : (hammingParityCheck r)ᵀ a ≠ (hammingParityCheck r)ᵀ b := by
      rw [hammingParityCheck_transpose_apply, hammingParityCheck_transpose_apply]
      exact Subtype.coe_injective.ne hab
    exact hga (eq_zero_and_eq_zero_of_zmod2_smul_add_smul
      (hammingParityCheck_transpose_ne_zero a) (hammingParityCheck_transpose_ne_zero b)
      hcolab hsum).1

/-- **Some three columns of `H_r` are linearly dependent** (for `r ≥ 2`). The three columns
`e₀ = single 0 1`, `e₁ = single 1 1` and `e₀ + e₁` are distinct nonzero vectors summing to zero, so
they form a linearly dependent set of exactly three columns. This is the `d = 3` dependence
hypothesis of Exercise 10.20. -/
theorem hammingParityCheck_exists_three_dependent (hr : 2 ≤ r) :
    ∃ s : Finset {v : Fin r → ZMod 2 // v ≠ 0}, s.card = 3 ∧
      ¬ LinearIndepOn (ZMod 2) (fun j => (hammingParityCheck r)ᵀ j) (↑s : Set _) := by
  classical
  set i0 : Fin r := ⟨0, by omega⟩ with hi0
  set i1 : Fin r := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set u : Fin r → ZMod 2 := Pi.single i0 1 with hu
  set v : Fin r → ZMod 2 := Pi.single i1 1 with hv
  set w : Fin r → ZMod 2 := u + v with hw
  have hu0 : u ≠ 0 := by
    intro h; have h2 := congrFun h i0
    simp only [hu, Pi.single_eq_same, Pi.zero_apply] at h2
    exact one_ne_zero h2
  have hv0 : v ≠ 0 := by
    intro h; have h2 := congrFun h i1
    simp only [hv, Pi.single_eq_same, Pi.zero_apply] at h2
    exact one_ne_zero h2
  have hw0 : w ≠ 0 := by
    intro h; have h2 := congrFun h i0
    simp only [hw, hu, hv, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
      add_zero] at h2
    exact one_ne_zero h2
  have huv : u ≠ v := by
    intro h; have h2 := congrFun h i0
    simp only [hu, hv, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h2
    exact one_ne_zero h2
  have huw : u ≠ w := by
    intro h; have h2 := congrFun h i1
    simp only [hw, hu, hv, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne.symm,
      zero_add] at h2
    exact zero_ne_one h2
  have hvw : v ≠ w := by
    intro h; have h2 := congrFun h i0
    simp only [hw, hu, hv, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
      add_zero] at h2
    exact zero_ne_one h2
  refine ⟨{⟨u, hu0⟩, ⟨v, hv0⟩, ⟨w, hw0⟩}, ?_, ?_⟩
  · rw [Finset.card_eq_three]
    exact ⟨⟨u, hu0⟩, ⟨v, hv0⟩, ⟨w, hw0⟩,
      fun h => huv (congrArg Subtype.val h),
      fun h => huw (congrArg Subtype.val h),
      fun h => hvw (congrArg Subtype.val h), rfl⟩
  · rw [linearIndepOn_finset_iff]
    push Not
    refine ⟨fun _ => 1, ?_, ⟨u, hu0⟩, Finset.mem_insert_self _ _, one_ne_zero⟩
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp only [one_smul, hammingParityCheck_transpose_apply, hw]
      funext i
      simp only [Pi.add_apply]
      exact (show ∀ a b : ZMod 2, a + (b + (a + b)) = 0 by decide) (u i) (v i)
    · simp only [Finset.mem_singleton]
      exact fun h => hvw (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => huv (congrArg Subtype.val h), fun h => huw (congrArg Subtype.val h)⟩

/-- **Nielsen & Chuang, Exercise 10.22 (distance).** For `r ≥ 2` the binary Hamming code has minimum
distance exactly `3`: any two of its parity-check columns are linearly independent, but some three
are dependent (`Matrix.minDist_ker_eq_of_columns`, Exercise 10.20). -/
theorem hammingCode_minDist (hr : 2 ≤ r) : LinearCode.minDist (hammingCode r) = 3 := by
  rw [hammingCode_eq, minDist_ker_eq_of_columns (hammingParityCheck r) (d := 3)
    hammingParityCheck_linearIndepOn_of_card_lt_three
    (hammingParityCheck_exists_three_dependent hr)]
  rfl

/-- **Nielsen & Chuang, Exercise 10.22 (single-error correction).** For `r ≥ 2` the binary Hamming
code corrects a single-bit error: its minimum distance `3` is at least `2·1 + 1`. -/
theorem hammingCode_correctsErrors_one (hr : 2 ≤ r) : (hammingCode r).CorrectsErrors 1 := by
  simp only [LinearCode.CorrectsErrors, hammingCode_minDist hr]
  norm_num

/-- **Nielsen & Chuang, Exercise 10.22 (length).** The block length of the binary Hamming code is
`n = 2^r − 1`: the number of nonzero binary `r`-vectors, i.e. the number of columns of `H_r`. -/
theorem hammingCode_length (r : ℕ) :
    Fintype.card {v : Fin r → ZMod 2 // v ≠ 0} = 2 ^ r - 1 := by
  rw [Fintype.card_subtype_compl]
  simp [ZMod.card, Fintype.card_fin]

/-- **The Hamming parity-check map is surjective** (`H_r` has full row rank `r`). The range of
`x ↦ H_r *ᵥ x` is the span of the columns of `H_r`, and *every* vector `w : Fin r → ZMod 2` lies in
that span: if `w = 0` trivially, and otherwise `w` is *itself* a column of `H_r` (the column indexed
by `⟨w, hw⟩`). Hence the columns span the whole check space `Fin r → ZMod 2` and the map is onto.
This is the full-row-rank fact `n − k = r` underlying the code's dimension count. -/
theorem hammingParityCheck_mulVecLin_surjective (r : ℕ) :
    Function.Surjective (hammingParityCheck r).mulVecLin := by
  rw [← LinearMap.range_eq_top, range_mulVecLin, Submodule.eq_top_iff']
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

/-- **Nielsen & Chuang, Exercise 10.22 (dimension).** The binary Hamming code has dimension
`k = 2^r − r − 1` — the last of its `[2^r − 1, 2^r − r − 1, 3]` parameters. The parity-check map has
full row rank `r` (`hammingParityCheck_mulVecLin_surjective`), so by the rank–nullity theorem the
code — the kernel of that map — has dimension `n − r = (2^r − 1) − r = 2^r − r − 1`, where
`n = 2^r − 1` is the block length (`hammingCode_length`). -/
theorem hammingCode_finrank (r : ℕ) :
    Module.finrank (ZMod 2) (hammingCode r) = 2 ^ r - r - 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (hammingParityCheck r).mulVecLin
  rw [LinearMap.range_eq_top.mpr (hammingParityCheck_mulVecLin_surjective r), finrank_top,
    Module.finrank_pi, Fintype.card_fin, Module.finrank_pi, hammingCode_length] at hrn
  rw [hammingCode_eq]
  omega

end Matrix
