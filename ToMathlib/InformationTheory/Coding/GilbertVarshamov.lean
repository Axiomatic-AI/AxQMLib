/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.LinearCode
public import ToMathlib.InformationTheory.Coding.BinomialEntropyBound
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# The Gilbert–Varshamov existence bound for binary linear codes

The **Gilbert–Varshamov bound** guarantees the existence of good linear codes: a binary linear code
of block length `n`, dimension at least `k`, and minimum distance at least `d` exists as long as the
Hamming-ball volume `∑_{i < d} C(n, i)` does not exceed `2 ^ (n - k)` (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, §10.4.1 eq. (10.63) and Exercise 10.23).

This file proves the combinatorial heart of that bound — the *counting form* — over the field
`ZMod 2`, and then the classical entropy form `k / n ≥ 1 - H₂(2t/n)` (N&C (10.63), Exercise 10.23),
obtained by combining the counting form with the entropy bound on the ball volume
(`sum_range_choose_le_rpow_mul_binEntropyBit` of
`ToMathlib.InformationTheory.Coding.BinomialEntropyBound`).

## Main results

* `LinearCode.exists_finrank_ge_minDist_ge`: if `∑_{i < d} C(n, i) ≤ 2 ^ (n - k)`, then there is a
  binary linear code `C ⊆ (Fin n → ZMod 2)` with `k ≤ Module.finrank (ZMod 2) C` and
  `d ≤ LinearCode.minDist C`. Taking `d = 2t + 1` yields a code correcting `t` errors.
* `LinearCode.exists_correctsErrors_of_rate_le`: the **entropy (rate) form** of the classical
  Gilbert–Varshamov bound (N&C Exercise 10.23, eq. (10.63)). In the regime `4t ≤ n`, if the target
  rate obeys `k ≤ n · (1 - H₂(2t/n))` (i.e. `k/n ≥ 1 - H₂(2t/n)`), then a binary linear code of
  dimension at least `k` correcting `t` errors exists.
* `card_parityChecks_mulVec_eq_zero`: the matrix count above, over an arbitrary finite field.
* `card_filter_hammingNorm_lt_le`: the Hamming-ball volume bound (binary).

## Implementation notes

The proof is the standard **Varshamov averaging argument** over parity-check matrices. A code with a
parity-check matrix `H : Matrix (Fin (n-k)) (Fin n) (ZMod 2)` is `LinearMap.ker H.mulVecLin`; it has
dimension at least `k` (rank-nullity) and minimum distance `≥ d` exactly when no nonzero word of
weight `< d` lies in its kernel. For a fixed nonzero word `w`, the map `H ↦ H *ᵥ w` is a
*surjective* linear map, so exactly a `2 ^ (-(n-k))` fraction of the `2 ^ ((n-k)·n)` matrices
annihilate `w` (`card_parityChecks_mulVec_eq_zero`, stated over any finite field). A union bound
over the fewer-than-`2 ^ (n-k)` nonzero low-weight words (bounded by the ball volume,
`card_filter_hammingNorm_lt_le`) then leaves at least one matrix whose kernel avoids all of them,
and that kernel is the desired code.

The matrix-counting step is field-agnostic and so is stated for an arbitrary finite field `K`
(count `(#K) ^ (m·n - m)`); the existence theorem itself is over `ZMod 2` (the binary case of N&C),
whose hypothesis `∑_{i < d} C(n, i)` is the GF(2) ball volume — the ball count uses that a binary
word is determined by its support (`hammingNorm w = #{support}`, and distinct words have distinct
supports).
-/

open Finset Matrix

public section

variable {n : ℕ}

/-- The Hamming weight of a word equals the cardinality of its support as a `Finset`. -/
private theorem hammingNorm_eq_card_filter (w : Fin n → ZMod 2) :
    hammingNorm w = (Finset.univ.filter (fun j => w j ≠ 0)).card := rfl

/-- **Ball-volume bound.** The number of binary words of length `n` and Hamming weight `< d` is at
most the Hamming-ball volume `∑_{i < d} C(n, i)`. (A word is sent injectively to its support, a
subset of `Fin n` of cardinality equal to its weight.) -/
theorem card_filter_hammingNorm_lt_le (d : ℕ) :
    (Finset.univ.filter (fun w : Fin n → ZMod 2 => hammingNorm w < d)).card
      ≤ ∑ i ∈ Finset.range d, (n.choose i) := by
  -- Every binary word is determined by its support, giving an injection into small subsets.
  have hkey : ∀ x y : ZMod 2, (x ≠ 0 ↔ y ≠ 0) → x = y := by decide
  have hinj : Set.InjOn (fun w : Fin n → ZMod 2 => Finset.univ.filter (fun j => w j ≠ 0))
      ↑(Finset.univ.filter (fun w : Fin n → ZMod 2 => hammingNorm w < d)) := by
    intro a _ b _ hab
    funext j
    apply hkey
    have := Finset.ext_iff.mp hab j
    simpa using this
  calc (Finset.univ.filter (fun w : Fin n → ZMod 2 => hammingNorm w < d)).card
      ≤ (Finset.univ.filter (fun s : Finset (Fin n) => s.card < d)).card := by
        refine Finset.card_le_card_of_injOn _ (fun w hw => ?_) hinj
        rw [Finset.mem_coe, Finset.mem_filter] at hw
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [← hammingNorm_eq_card_filter]; exact hw.2⟩
    _ = ∑ i ∈ Finset.range d, (n.choose i) := by
        rw [show (Finset.univ.filter (fun s : Finset (Fin n) => s.card < d))
            = (Finset.range d).biUnion (fun i => Finset.univ.powersetCard i) from ?_]
        · rw [Finset.card_biUnion ?_]
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          · intro i _ j _ hij
            simp only [Finset.disjoint_left, Finset.mem_powersetCard]
            rintro s ⟨_, hs⟩ ⟨_, hs'⟩
            exact hij (hs ▸ hs')
        · ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
            Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ]
          exact ⟨fun h => ⟨s.card, h, rfl⟩, fun ⟨i, hi, hs⟩ => hs ▸ hi⟩

/-- **Counting parity-check matrices with a fixed word in their kernel.** Over a finite field `K`,
for a nonzero word `w` exactly `(#K) ^ (m·n - m)` of the `(#K) ^ (m·n)` matrices
`H : Matrix (Fin m) (Fin n) K` satisfy `H *ᵥ w = 0`. The map `H ↦ H *ᵥ w` is a surjective linear map
onto `Fin m → K` (a single nonzero coordinate of `w` lets one hit any target), so its kernel has
dimension `m·n - m` by rank-nullity. -/
theorem card_parityChecks_mulVec_eq_zero {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) {w : Fin n → K} (hw : w ≠ 0) :
    (Finset.univ.filter (fun H : Matrix (Fin m) (Fin n) K => H *ᵥ w = 0)).card
      = (Fintype.card K) ^ (m * n - m) := by
  classical
  -- The evaluation-at-`w` linear map, linear in the matrix.
  let ev : Matrix (Fin m) (Fin n) K →ₗ[K] (Fin m → K) :=
    { toFun := fun H => H *ᵥ w
      map_add' := fun A B => Matrix.add_mulVec A B w
      map_smul' := fun c A => Matrix.smul_mulVec c A w }
  -- `ev` is surjective because `w ≠ 0`: scale the standard column at a nonzero coordinate.
  have hsurj : Function.Surjective ev := by
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hw
    intro y
    refine ⟨Matrix.of (fun i j => if j = j0 then y i * (w j0)⁻¹ else 0), ?_⟩
    funext i
    change ∑ j, (if j = j0 then y i * (w j0)⁻¹ else 0) * w j = y i
    rw [Finset.sum_eq_single j0]
    · rw [ite_eq_left rfl, mul_assoc, inv_mul_cancel₀ hj0, mul_one]
    · intro b _ hb; rw [ite_eq_right hb, zero_mul]
    · intro hj0'; exact absurd (Finset.mem_univ j0) hj0'
  have hrange : Module.finrank K ↥(LinearMap.range ev) = m := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]
  have hmatrix : Module.finrank K (Matrix (Fin m) (Fin n) K) = m * n := by
    rw [Module.finrank_matrix]; simp
  have hker : Module.finrank K ↥(LinearMap.ker ev) = m * n - m := by
    have h := LinearMap.finrank_range_add_finrank_ker ev
    rw [hrange, hmatrix] at h; omega
  rw [← Fintype.card_subtype]
  have hcong : Nat.card {H // H *ᵥ w = 0} = Nat.card ↥(LinearMap.ker ev) :=
    Nat.card_congr (Equiv.subtypeEquivRight
      (fun H => ⟨fun h => LinearMap.mem_ker.mpr h, fun h => LinearMap.mem_ker.mp h⟩))
  rw [← Nat.card_eq_fintype_card, hcong, Module.natCard_eq_pow_finrank (K := K), hker]
  simp [Nat.card_eq_fintype_card]

namespace LinearCode

/-- **Gilbert–Varshamov existence bound** (counting form, binary case; N&C Exercise 10.23). If the
Hamming-ball volume `∑_{i < d} C(n, i)` is at most `2 ^ (n - k)`, then there exists a binary linear
code `C ⊆ (Fin n → ZMod 2)` of dimension at least `k` and minimum distance at least `d`.

Specialising to `d = 2 t + 1` produces a code of rate `≥ k / n` correcting `t` errors, the
content of the classical Gilbert–Varshamov bound (10.63). -/
theorem exists_finrank_ge_minDist_ge {n k d : ℕ} (hk : k ≤ n)
    (hV : (∑ i ∈ Finset.range d, (n.choose i)) ≤ 2 ^ (n - k)) :
    ∃ C : LinearCode (ZMod 2) (Fin n),
      k ≤ Module.finrank (ZMod 2) C ∧ (d : ℕ∞) ≤ LinearCode.minDist C := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- `d = 0`: the full space works.
    refine ⟨⊤, ?_, ?_⟩
    · rw [finrank_top, Module.finrank_fin_fun]; exact hk
    · subst hd0; simp
  -- Main case `d ≥ 1`.
  set m := n - k with hm
  have hmmn : m ≤ m * n := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · simp [hm0]
    · have hn : 1 ≤ n := by omega
      calc m = m * 1 := (mul_one m).symm
        _ ≤ m * n := Nat.mul_le_mul_left m hn
  -- The "bad" words: nonzero, of weight `< d`.
  set bad : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun w => w ≠ 0 ∧ hammingNorm w < d) with hbad
  -- Step A: there are fewer than `2 ^ m` bad words.
  have hbad_card : bad.card < 2 ^ m := by
    have hsub : bad ⊂ Finset.univ.filter (fun w : Fin n → ZMod 2 => hammingNorm w < d) := by
      refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨0, ?_, ?_⟩
      · intro w hw; rw [hbad, Finset.mem_filter] at hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2.2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hd⟩
      · rw [hbad]; simp
    calc bad.card
        < (Finset.univ.filter (fun w : Fin n → ZMod 2 => hammingNorm w < d)).card :=
          Finset.card_lt_card hsub
      _ ≤ ∑ i ∈ Finset.range d, (n.choose i) := card_filter_hammingNorm_lt_le d
      _ ≤ 2 ^ (n - k) := hV
      _ = 2 ^ m := by rw [hm]
  -- Step B: a matrix whose kernel avoids every bad word.
  have hexists : ∃ H : Matrix (Fin m) (Fin n) (ZMod 2), ∀ w ∈ bad, H *ᵥ w ≠ 0 := by
    let killers : (Fin n → ZMod 2) → Finset (Matrix (Fin m) (Fin n) (ZMod 2)) :=
      fun w => Finset.univ.filter (fun H => H *ᵥ w = 0)
    by_contra hcon
    simp only [not_exists, not_forall, not_ne_iff] at hcon
    have hsub : (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2)))
        ⊆ bad.biUnion killers := by
      intro H _
      obtain ⟨w, hwbad, hHw⟩ := hcon H
      exact Finset.mem_biUnion.mpr ⟨w, hwbad, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHw⟩⟩
    have hcard_univ :
        (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).card = 2 ^ (m * n) := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        Module.natCard_eq_pow_finrank (K := ZMod 2)]
      have hfr : Module.finrank (ZMod 2) (Matrix (Fin m) (Fin n) (ZMod 2)) = m * n := by
        rw [Module.finrank_matrix]; simp
      rw [hfr]; simp [Nat.card_eq_fintype_card, ZMod.card]
    have hbu : (bad.biUnion killers).card ≤ bad.card * 2 ^ (m * n - m) := by
      refine le_trans Finset.card_biUnion_le ?_
      rw [← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun w hw => ?_
      have hcnt := card_parityChecks_mulVec_eq_zero (K := ZMod 2) m
        (Finset.mem_filter.mp (hbad ▸ hw)).2.1
      rw [ZMod.card] at hcnt
      exact le_of_eq hcnt
    have h1 : 2 ^ (m * n) ≤ bad.card * 2 ^ (m * n - m) :=
      calc 2 ^ (m * n) = (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).card :=
            hcard_univ.symm
        _ ≤ (bad.biUnion killers).card := Finset.card_le_card hsub
        _ ≤ bad.card * 2 ^ (m * n - m) := hbu
    have h2 : bad.card * 2 ^ (m * n - m) < 2 ^ m * 2 ^ (m * n - m) :=
      mul_lt_mul_of_pos_right hbad_card (by positivity)
    have h3 : 2 ^ m * 2 ^ (m * n - m) = 2 ^ (m * n) := by
      rw [← pow_add]; congr 1; omega
    omega
  obtain ⟨H, hH⟩ := hexists
  -- The code is the kernel of the parity-check map.
  refine ⟨LinearMap.ker (Matrix.mulVecLin H), ?_, ?_⟩
  · -- Dimension `≥ k` by rank-nullity.
    have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin H)
    rw [Module.finrank_fin_fun] at hrn
    have hle : Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin H)) ≤ m :=
      calc Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin H))
          ≤ Module.finrank (ZMod 2) (Fin m → ZMod 2) := Submodule.finrank_le _
        _ = m := Module.finrank_fin_fun _
    omega
  · -- Minimum distance `≥ d`.
    rw [LinearCode.le_minDist_iff]
    intro c hc hc0
    rw [show ((d : ℕ) : ℕ∞) ≤ (hammingNorm c : ℕ∞) ↔ d ≤ hammingNorm c from Nat.cast_le]
    by_contra hlt
    rw [not_le] at hlt
    have hcbad : c ∈ bad :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0, hlt⟩
    have hHc : H *ᵥ c = 0 := by
      have := (LinearMap.mem_ker).mp hc
      rwa [Matrix.mulVecLin_apply] at this
    exact hH c hcbad hHc

/-- **Classical Gilbert–Varshamov bound, entropy (rate) form** (Nielsen & Chuang, Exercise 10.23,
eq. (10.63)). In the regime `4t ≤ n` (so the entropy argument `2t/n` lies in `[0, 1/2]`), if the
target rate satisfies `k ≤ n · (1 - H₂(2t/n))` — equivalently `k / n ≥ 1 - H₂(2t/n)`, with
`H₂ = Real.binEntropyBit` the base-`2` binary entropy — then there exists a binary linear code
`C ⊆ (Fin n → ZMod 2)` of dimension at least `k` that corrects `t` errors.

This is the achievability content of the classical bound: good codes of rate up to `1 - H₂(2t/n)`
exist. It is obtained from the counting form `exists_finrank_ge_minDist_ge` (with `d = 2t + 1`) by
bounding the Hamming-ball volume `∑_{i ≤ 2t} C(n, i) ≤ 2 ^ (n · H₂(2t/n)) ≤ 2 ^ (n - k)`, the middle
step being `sum_range_choose_le_rpow_mul_binEntropyBit` and the last the rate hypothesis. -/
theorem exists_correctsErrors_of_rate_le {n k t : ℕ} (h4t : 4 * t ≤ n)
    (hrate : (k : ℝ) ≤ n * (1 - Real.binEntropyBit (2 * t / n))) :
    ∃ C : LinearCode (ZMod 2) (Fin n),
      k ≤ Module.finrank (ZMod 2) C ∧ CorrectsErrors C t := by
  -- Entropy regime for the volume bound: `2 · (2t) ≤ n`.
  have hrn : 2 * (2 * t) ≤ n := by omega
  -- The entropy argument `2t/n` lies in `[0, 1]`, so `H₂(2t/n) ≥ 0`.
  have hp0 : (0 : ℝ) ≤ 2 * t / n := by positivity
  have hp1 : (2 * t / n : ℝ) ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast (show 2 * t ≤ n by omega)) (by positivity)
  have hH0 : (0 : ℝ) ≤ Real.binEntropyBit (2 * t / n) := Real.binEntropyBit_nonneg hp0 hp1
  -- Hence `k ≤ n` as naturals, from the rate hypothesis.
  have hkn : k ≤ n := by
    have hnn : (0 : ℝ) ≤ n := by positivity
    have : (k : ℝ) ≤ n := by nlinarith [hrate, hH0, hnn]
    exact_mod_cast this
  -- Ball-volume bound in `ℕ`: `∑_{i ≤ 2t} C(n, i) ≤ 2 ^ (n - k)`.
  have hV : (∑ i ∈ Finset.range (2 * t + 1), (n.choose i)) ≤ 2 ^ (n - k) := by
    have key : (∑ i ∈ Finset.range (2 * t + 1), (n.choose i : ℝ)) ≤ (2 : ℝ) ^ (n - k) := by
      refine (sum_range_choose_le_rpow_mul_binEntropyBit hrn).trans ?_
      rw [← Real.rpow_natCast (2 : ℝ) (n - k)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [Nat.cast_sub hkn]
      push_cast
      linarith [hrate]
    exact_mod_cast key
  -- Apply the counting-form existence theorem with `d = 2t + 1`.
  exact exists_finrank_ge_minDist_ge (d := 2 * t + 1) hkn hV

end LinearCode

end
