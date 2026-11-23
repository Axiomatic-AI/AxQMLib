/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Linear codes and their minimum distance

A **linear code** of block length `ι` over a field `K` is a `K`-subspace of the word space
`ι → K` (Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.1). Its codewords
are the elements of the subspace, and — because the subspace is closed under subtraction — its
error-correcting power is governed by a single number, the *minimum distance*: the least Hamming
weight of a nonzero codeword.

This file develops the minimum-distance theory needed to state and prove the Gilbert–Varshamov
bounds (classical: N&C Exercise 10.23; quantum/CSS: N&C Problem 10.2).

## Main definitions

* `LinearCode K ι`: a linear code, i.e. a `Submodule K (ι → K)`.
* `LinearCode.minDist C`: the minimum distance `d(C)`, the least Hamming weight of a nonzero
  codeword (N&C eq. (10.61)), valued in `ℕ∞` (with `⊤` for the trivial code `{0}`).
* `LinearCode.CorrectsErrors C t`: `C` *corrects `t` errors*, meaning `d(C) ≥ 2t + 1` (N&C p. 448).

## Main results

* `LinearCode.le_minDist_iff_pairwise`: `d ≤ d(C)` iff every two distinct codewords are at Hamming
  distance `≥ d`. This is the equivalence of N&C's two forms of the distance — the minimum over
  distinct pairs (10.60) and the minimum nonzero weight (10.61) — which holds because the code is
  linear (`x - y` is again a codeword).
* `LinearCode.correctsErrors_iff`: `C` corrects `t` errors iff every two distinct codewords are at
  Hamming distance `≥ 2t + 1`.
* `LinearCode.CorrectsErrors.eq_of_hammingDist_le`: **nearest-neighbour decoding** — if `C` corrects
  `t` errors then no word lies within Hamming distance `t` of two distinct codewords; the radius-`t`
  balls around codewords are pairwise disjoint, so a corrupted word with at most `t` flips decodes
  to a unique codeword.

## Implementation notes

The minimum distance is taken in `ℕ∞` so that it is total: the trivial code `{0}` has no nonzero
codeword and thus minimum distance `⊤` (the infimum of the empty set). All facts are phrased through
the order characterizations `le_minDist_iff` / `le_minDist_iff_pairwise`, so no use of it ever
needs to extract a natural-number value.

The coefficients range over an arbitrary field `K`; the binary Gilbert–Varshamov applications
specialize to `K = ZMod 2`.
-/

@[expose] public section

/-- A **linear code** of block length `ι` over a field `K`: a `K`-subspace of the word space
`ι → K`, whose elements are the codewords (Nielsen & Chuang, §10.4.1). An `[n, k]` code in the
textbook's notation is one with `n = #ι` and `k = Module.finrank K C`. -/
abbrev LinearCode (K ι : Type*) [Field K] : Type _ := Submodule K (ι → K)

namespace LinearCode

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K]

/-- The **minimum distance** `d(C)` of a linear code: the least Hamming weight of a nonzero
codeword (Nielsen & Chuang, eq. (10.61)), valued in `ℕ∞`. The trivial code `{0}`, having no nonzero
codeword, has minimum distance `⊤`. -/
noncomputable def minDist (C : LinearCode K ι) : ℕ∞ :=
  ⨅ c ∈ {c : ι → K | c ∈ C ∧ c ≠ 0}, (hammingNorm c : ℕ∞)

/-- A lower bound `d ≤ d(C)` holds exactly when every nonzero codeword has Hamming weight at least
`d`. -/
theorem le_minDist_iff {C : LinearCode K ι} {d : ℕ∞} :
    d ≤ minDist C ↔ ∀ c ∈ C, c ≠ 0 → d ≤ (hammingNorm c : ℕ∞) := by
  simp only [minDist, le_iInf₂_iff, Set.mem_ofPred_eq, and_imp]

/-- The minimum distance is at most the weight of any given nonzero codeword. -/
theorem minDist_le_hammingNorm {C : LinearCode K ι} {c : ι → K} (hc : c ∈ C) (hc0 : c ≠ 0) :
    minDist C ≤ (hammingNorm c : ℕ∞) :=
  iInf₂_le c ⟨hc, hc0⟩

/-- **The two forms of the code distance agree** (Nielsen & Chuang, eqs. (10.60) = (10.61)). A lower
bound `d ≤ d(C)` on the minimum *weight* is equivalent to the same lower bound on the Hamming
*distance* between every two distinct codewords. The forward direction uses linearity: for
codewords `x ≠ y` the difference `-x + y` is a nonzero codeword of weight `d(x, y)`. -/
theorem le_minDist_iff_pairwise {C : LinearCode K ι} {d : ℕ∞} :
    d ≤ minDist C ↔ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ (hammingDist x y : ℕ∞) := by
  rw [le_minDist_iff]
  refine ⟨fun h x hx y hy hxy => ?_, fun h c hc hc0 => ?_⟩
  · have hmem : -x + y ∈ C := C.add_mem (C.neg_mem hx) hy
    rw [hammingDist_eq_hammingNorm]
    exact h _ hmem (fun H => hxy (neg_add_eq_zero.mp H))
  · have := h 0 C.zero_mem c hc hc0.symm
    rwa [hammingDist_zero_left] at this

/-- A linear code **corrects `t` errors** when its minimum distance is at least `2t + 1`
(Nielsen & Chuang, p. 448): decoding a corrupted word to the nearest codeword recovers from up to
`t` symbol errors. -/
def CorrectsErrors (C : LinearCode K ι) (t : ℕ) : Prop := (↑(2 * t + 1) : ℕ∞) ≤ minDist C

/-- `C` corrects `t` errors iff every two distinct codewords are at Hamming distance at least
`2t + 1`. -/
theorem correctsErrors_iff {C : LinearCode K ι} {t : ℕ} :
    CorrectsErrors C t ↔ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y := by
  simp only [CorrectsErrors, le_minDist_iff_pairwise, Nat.cast_le]

/-- **Nearest-neighbour decoding is unambiguous** for a `t`-error-correcting code. If `C` corrects
`t` errors then no word `z` lies within Hamming distance `t` of two distinct codewords: the
radius-`t` Hamming balls about the codewords are pairwise disjoint. Consequently a codeword
corrupted in at most `t` positions is recovered uniquely. -/
theorem CorrectsErrors.eq_of_hammingDist_le {C : LinearCode K ι} {t : ℕ}
    (h : CorrectsErrors C t) {x y z : ι → K} (hx : x ∈ C) (hy : y ∈ C)
    (hzx : hammingDist z x ≤ t) (hzy : hammingDist z y ≤ t) : x = y := by
  by_contra hxy
  have hxy' : 2 * t + 1 ≤ hammingDist x y := correctsErrors_iff.mp h x hx y hy hxy
  have htri : hammingDist x y ≤ hammingDist z x + hammingDist z y := hammingDist_triangle_left x y z
  omega

end LinearCode
