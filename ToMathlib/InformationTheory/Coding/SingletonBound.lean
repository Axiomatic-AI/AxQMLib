/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi

/-!
# The Singleton bound for linear codes

For a linear `[n, k, d]` code — block length `n = #ι`, dimension `k = Module.finrank K C`, and
minimum distance `d = LinearCode.minDist C` — the **Singleton bound** states that
`n − k ≥ d − 1`, equivalently `d ≤ n − k + 1` (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Exercise 10.21, p. 449).

The bound is a **puncturing** argument. Delete `d − 1` of the `n` coordinates: the restriction of a
codeword to the remaining `n − (d − 1)` coordinates is injective on the code, because a codeword in
its kernel is supported on the `d − 1` deleted coordinates, hence has Hamming weight `≤ d − 1 < d`,
hence — being a codeword of weight below the minimum distance — is `0`. An injective linear map out
of the code bounds its dimension by that of the target, `k ≤ n − (d − 1)`, which is the Singleton
bound.

## Main results

* `LinearCode.finrank_le_of_card_compl_lt_minDist`: the **puncturing bound**. For any set `S` of
  coordinates whose complement is smaller than the minimum distance (`#Sᶜ < d(C)`), restricting
  codewords to `S` is injective, so `Module.finrank K C ≤ #S`. This is the reusable core.
* `LinearCode.singleton_bound`: **the Singleton bound**, `d(C) ≤ n − k + 1`, for any nontrivial code
  `C ≠ ⊥` (N&C Exercise 10.21). Reads as N&C's `n − k ≥ d − 1` after subtracting the `1` (legitimate
  because a nontrivial code has `d ≥ 1`).

## Implementation notes

The minimum distance lives in `ℕ∞`. The trivial code `{0}` has `d = ⊤` and no finite `[n, k, d]`
parameters, so the Singleton bound is stated for `C ≠ ⊥`; there the minimum distance is a genuine
natural number `1 ≤ d ≤ n`, extracted via `ENat.toNat`. The puncturing bound itself needs no such
hypothesis: it is an inequality between naturals gated by the `ℕ∞` comparison `#Sᶜ < d(C)`, vacuous
exactly when it should be.

Deleting `d − 1` coordinates is realized by choosing any `T ⊆ ι` with `#T = d − 1` (possible since
`d − 1 ≤ n`, `Finset.exists_subset_card_eq`) and keeping `S = Tᶜ`; the restriction map is the
precomposition `LinearMap.funLeft` with the inclusion `↥S ↪ ι`.

The coefficients range over an arbitrary field `K` (N&C's binary code is `K = ZMod 2`).
-/

@[expose] public section

namespace LinearCode

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq K]

/-- **Puncturing bound.** If a set `S` of coordinate positions has complement smaller than the
minimum distance of the code (`#Sᶜ < d(C)`), then restricting codewords to the positions in `S` is
injective on `C`, so the dimension of the code is at most `#S`.

A codeword `c` killed by the restriction vanishes off `S`, i.e. is supported on `Sᶜ`, so
`hammingNorm c ≤ #Sᶜ < d(C)`; a nonzero codeword of weight below the minimum distance cannot exist,
so `c = 0`. This is the linear-algebra heart of the Singleton bound. -/
theorem finrank_le_of_card_compl_lt_minDist [DecidableEq ι] (C : LinearCode K ι) {S : Finset ι}
    (hS : (Sᶜ.card : ℕ∞) < minDist C) : Module.finrank K C ≤ S.card := by
  -- The restriction of a word to the coordinates in `S`, as a linear map out of the code.
  set π : C →ₗ[K] (S → K) := (LinearMap.funLeft K K (Subtype.val)).comp C.subtype
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨c, hc⟩ hc0
    -- A codeword in the kernel vanishes on every position of `S`.
    have hvanish : ∀ i ∈ S, c i = 0 := by
      intro i hi
      have := congrFun hc0 ⟨i, hi⟩
      simpa [π, LinearMap.funLeft_apply] using this
    have hcz : c = 0 := by
      by_contra hcne
      -- Then `c` is a nonzero codeword, so `d(C) ≤ hammingNorm c`.
      have h1 : minDist C ≤ (hammingNorm c : ℕ∞) := minDist_le_hammingNorm hc hcne
      -- But its support lies in `Sᶜ`, so `hammingNorm c ≤ #Sᶜ`.
      have hsub : (Finset.univ.filter (fun i => c i ≠ 0)) ⊆ Sᶜ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Finset.mem_compl]
        exact fun hiS => hi (hvanish i hiS)
      have h2 : hammingNorm c ≤ Sᶜ.card := by
        rw [hammingNorm]; exact Finset.card_le_card hsub
      -- Contradiction: `d(C) ≤ hammingNorm c ≤ #Sᶜ < d(C)`.
      have : minDist C ≤ (Sᶜ.card : ℕ∞) := le_trans h1 (by exact_mod_cast h2)
      exact absurd (lt_of_le_of_lt this hS) (lt_irrefl _)
    exact Subtype.ext hcz
  calc Module.finrank K C ≤ Module.finrank K (S → K) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = S.card := by rw [Module.finrank_pi, Fintype.card_coe]

/-- **The Singleton bound** (Nielsen & Chuang, Exercise 10.21, p. 449). A nontrivial linear
`[n, k, d]` code satisfies `d ≤ n − k + 1`, i.e. `n − k ≥ d − 1`, where `n = #ι` is the block
length, `k = Module.finrank K C` the dimension, and `d = minDist C` the minimum distance.

The hypothesis `C ≠ ⊥` rules out the trivial code `{0}`, which has no finite minimum distance (no
nonzero codeword) and so no `[n, k, d]` parameters. For any nontrivial code the minimum distance is
a genuine natural number `1 ≤ d ≤ n`.

Take `S = Tᶜ` for a set `T` of `d − 1` deleted coordinates: then `#Sᶜ = d − 1 < d`, so the
puncturing bound gives `k ≤ #S = n − (d − 1)`, which rearranges to `d ≤ n − k + 1`. -/
theorem singleton_bound (C : LinearCode K ι) (hC : C ≠ ⊥) :
    minDist C ≤ (Fintype.card ι - Module.finrank K C + 1 : ℕ) := by
  classical
  obtain ⟨c₀, hc₀, hc₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
  -- The minimum distance is finite (bounded by the weight of any nonzero codeword).
  have hle0 : minDist C ≤ (hammingNorm c₀ : ℕ∞) := minDist_le_hammingNorm hc₀ hc₀ne
  have htop : minDist C ≠ ⊤ := (lt_of_le_of_lt hle0 (ENat.natCast_lt_top _)).ne
  set m : ℕ := (minDist C).toNat
  have hmeq : (m : ℕ∞) = minDist C := ENat.natCast_toNat htop
  -- `1 ≤ d`: every nonzero codeword has positive weight.
  have h1m : 1 ≤ m := by
    have h : (1 : ℕ∞) ≤ minDist C :=
      le_minDist_iff.mpr fun c hc hcne => by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hammingNorm_ne_zero_iff.mpr hcne)
    rw [← hmeq] at h; exact_mod_cast h
  -- `d ≤ n`: a nonzero codeword has weight at most `n`.
  have hmn : m ≤ Fintype.card ι := by
    have h : minDist C ≤ (Fintype.card ι : ℕ∞) :=
      le_trans hle0 (by exact_mod_cast hammingNorm_le_card_fintype)
    rw [← hmeq] at h; exact_mod_cast h
  -- `k ≤ n`: the code is a subspace of the `n`-dimensional word space.
  have hkn : Module.finrank K C ≤ Fintype.card ι := by
    have h := Submodule.finrank_le C
    rwa [Module.finrank_pi] at h
  -- Delete `d − 1` coordinates: choose `T` with `#T = d − 1`, keep `S = Tᶜ`.
  obtain ⟨T, -, hT⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := m - 1)
      (by rw [Finset.card_univ]; omega)
  have hpunc : ((Tᶜ)ᶜ.card : ℕ∞) < minDist C := by
    rw [compl_compl, hT, ← hmeq]; exact_mod_cast (show m - 1 < m by omega)
  have hfr : Module.finrank K C ≤ (Tᶜ).card := finrank_le_of_card_compl_lt_minDist C hpunc
  rw [Finset.card_compl, hT] at hfr
  rw [← hmeq]
  exact_mod_cast (show m ≤ Fintype.card ι - Module.finrank K C + 1 by omega)

end LinearCode
