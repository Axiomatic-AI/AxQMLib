/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Analysis.LocallyConvex.Separation
public import ToMathlib.Data.Fintype.EquivOfMultisetMap

/-!
# Majorization of real vectors

Majorization is an order on real vectors capturing the idea that one vector is more spread out
(less "disordered") than another.  For `x y : ι → ℝ` on a finite index type `ι` we say `x` is
*majorized* by `y`, `Majorize x y`, when the sum of the `k` largest entries of `x` is at most that
of `y` for every `k`, and the two total sums agree.

The condition is recorded through `largestKSum x k`, the largest sum of any `k` entries of `x`,
defined as a supremum over `k`-element subsets so that no explicit sorting of the entries is
needed.  This form pairs directly with `doublyStochastic` and Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`), towards the representation theorem
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, Proposition 12.11)
`Majorize x y ↔ x = ∑ⱼ pⱼ Pⱼ y` for probabilities `pⱼ` and permutation matrices `Pⱼ`.

## Main definitions

* `largestKSum x k`: the maximum of `∑ i ∈ s, x i` over `k`-element subsets `s`.
* `Majorize x y`: `x` is majorized by `y`.
* `tailSum x t`: the tail/cut function `∑ i, max (x i - t) 0`, the Legendre-type conjugate of
  `largestKSum x` used for the Exercise 12.17 characterisation.

## Main statements

* `Majorize.refl`, `Majorize.sum_eq`: basic properties.
* `majorize_iff_forall_largestKSum`: the definition matches the textbook "sum of the `k` largest
  entries" formulation.
* `Majorize.comp_perm_left`, `Majorize.comp_perm_right`: majorization is unchanged when the entries
  of either vector are permuted; in particular a permutation of `y` is majorized by `y`.
* `convex_setOf_majorize`: the set of vectors majorized by a fixed `y` is convex
  (Nielsen–Chuang, Exercise 12.18).
* `majorize_sum_smul_permMatrix_mulVec`, `Majorize.of_mem_doublyStochastic`: a convex combination of
  permutations of `y` — equivalently, `D *ᵥ y` for a doubly stochastic `D` — is majorized by `y`
  (the easy direction of Proposition 12.11).
* `largestKSum_eq_sum_prefix_of_antitone`: for a decreasing vector the `k` largest entries are the
  leading ones, so `largestKSum` is realised by the prefix sum.
* `Majorize.sum_mul_le_of_antitone`: the Hardy–Littlewood–Pólya inequality for decreasing vectors,
  `∑ i, c i * x i ≤ ∑ i, c i * y i` when `x`, `y`, `c` are antitone and `Majorize x y`
  (proved by summation by parts on the `largestKSum` sequence).
* `Majorize.exists_perm_sum_mul_le`: the coordinate-free consequence for an arbitrary weight vector
  `c`, `∃ σ, ∑ i, c i * x i ≤ ∑ i, c i * y (σ i)`; this is the analytic input to the "hard"
  direction of Proposition 12.11 (that `x ≺ y` implies `x = D *ᵥ y` for a doubly stochastic `D`).
* `Majorize.exists_doublyStochastic_mulVec`: the hard direction — `x ≺ y` implies `x = D *ᵥ y` for
  some doubly stochastic `D` — proved by separating `x` from the compact convex set of such images
  with a hyperplane (`geometric_hahn_banach_closed_point`).
* `majorize_iff_exists_doublyStochastic`: the Hardy–Littlewood–Pólya characterisation
  `Majorize x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x`.
* `majorize_iff_exists_sum_perm`: **Nielsen–Chuang, Proposition 12.11** — `Majorize x y` holds iff
  `x = ∑ⱼ pⱼ Pⱼ y` for a probability distribution `pⱼ` and permutation matrices `Pⱼ`.
* `majorize_iff_forall_tailSum`: **Nielsen–Chuang, Exercise 12.17** — `Majorize x y` holds iff
  `∀ t, tailSum x t ≤ tailSum y t` together with equality of the total sums, via the conjugacy
  `largestKSum_le_tailSum_add` / `exists_tailSum_add_eq_largestKSum` between `tailSum` and
  `largestKSum`.

## Tags

majorization, doubly stochastic, Schur
-/

public section

open Finset Function Matrix
open scoped BigOperators

variable {ι : Type*}

/-- `largestKSum x k` is the largest sum of `k` entries of `x`: the supremum of `∑ i ∈ s, x i` over
`k`-element subsets `s` of the index type.  It equals `0` when `k` exceeds the dimension, since then
no such subset exists. -/
noncomputable def largestKSum (x : ι → ℝ) (k : ℕ) : ℝ :=
  ⨆ s : {s : Finset ι // s.card = k}, ∑ i ∈ (s : Finset ι), x i

private lemma bddAbove_range_subtype_sum [Finite ι] (x : ι → ℝ) (k : ℕ) :
    BddAbove (Set.range fun s : {s : Finset ι // s.card = k} => ∑ i ∈ (s : Finset ι), x i) := by
  have : Fintype ι := Fintype.ofFinite ι
  exact Set.Finite.bddAbove (Set.finite_range _)

/-- Any subset sum of `x` is at most the largest sum of that many entries of `x`. -/
lemma sum_le_largestKSum [Finite ι] (x : ι → ℝ) (s : Finset ι) :
    ∑ i ∈ s, x i ≤ largestKSum x s.card :=
  le_ciSup (bddAbove_range_subtype_sum x s.card) (⟨s, rfl⟩ : {t : Finset ι // t.card = s.card})

/-- The largest sum of `k` entries is at most `c` as soon as every `k`-subset sum is at most `c`
(and there is at least one `k`-subset, i.e. `k ≤ card ι`). -/
lemma largestKSum_le [Fintype ι] {x : ι → ℝ} {k : ℕ} {c : ℝ} (hk : k ≤ Fintype.card ι)
    (h : ∀ s : Finset ι, s.card = k → ∑ i ∈ s, x i ≤ c) :
    largestKSum x k ≤ c := by
  obtain ⟨t, _, ht⟩ :=
    Finset.exists_subset_card_eq (show k ≤ (univ : Finset ι).card by simpa using hk)
  have : Nonempty {s : Finset ι // s.card = k} := ⟨t, ht⟩
  exact ciSup_le fun s => h s s.2

/-- Reindexing the entries of `x` along any equivalence `e : κ ≃ ι` leaves the largest sum of `k`
entries unchanged: the `k`-element subsets of the two index types are in bijection via `e`. -/
lemma largestKSum_comp_equiv {κ : Type*} (x : ι → ℝ) (e : κ ≃ ι) (k : ℕ) :
    largestKSum (x ∘ e) k = largestKSum x k := by
  let E : {s : Finset κ // s.card = k} ≃ {s : Finset ι // s.card = k} :=
    (e.finsetCongr).subtypeEquiv (by intro t; simp [Equiv.finsetCongr_apply])
  have key : ∀ s : {s : Finset κ // s.card = k},
      ∑ i ∈ (s : Finset κ), (x ∘ e) i = ∑ i ∈ (E s : Finset ι), x i := by
    intro s
    simp only [E, Equiv.subtypeEquiv_apply, Equiv.finsetCongr_apply, Finset.sum_map,
      Function.comp_apply, Equiv.coe_toEmbedding]
  calc largestKSum (x ∘ e) k
      = ⨆ s : {s : Finset κ // s.card = k}, ∑ i ∈ (E s : Finset ι), x i := iSup_congr key
    _ = largestKSum x k :=
        Equiv.iSup_comp (g := fun t : {s : Finset ι // s.card = k} => ∑ i ∈ (t : Finset ι), x i) E

/-- Reindexing the entries of `x` by a permutation leaves the largest sum of `k` entries
unchanged. -/
lemma largestKSum_comp_perm (x : ι → ℝ) (σ : Equiv.Perm ι) (k : ℕ) :
    largestKSum (x ∘ σ) k = largestKSum x k :=
  largestKSum_comp_equiv x σ k

/-- `x` is *majorized* by `y` (written `x ≺ y` in the literature): the sum of the `k` largest
entries of `x` is at most the sum of the `k` largest entries of `y` for every `k`, and the total
sums agree.  This is recorded compactly by requiring that every subset sum of `x` is bounded by the
largest equal-sized subset sum of `y`, together with equality of the total sums. -/
def Majorize [Fintype ι] (x y : ι → ℝ) : Prop :=
  (∑ i, x i = ∑ i, y i) ∧ ∀ s : Finset ι, ∑ i ∈ s, x i ≤ largestKSum y s.card

variable [Fintype ι]

/-- Majorization preserves the total sum. -/
lemma Majorize.sum_eq {x y : ι → ℝ} (h : Majorize x y) : ∑ i, x i = ∑ i, y i := h.1

/-- Majorization is reflexive. -/
@[refl]
lemma Majorize.refl (x : ι → ℝ) : Majorize x x :=
  ⟨rfl, fun s => sum_le_largestKSum x s⟩

/-- Majorization is exactly the textbook condition: the sum of the `k` largest entries of `x` is at
most that of `y` for every `k`, together with equality of the total sums. -/
lemma majorize_iff_forall_largestKSum {x y : ι → ℝ} :
    Majorize x y ↔ (∑ i, x i = ∑ i, y i) ∧ ∀ k, largestKSum x k ≤ largestKSum y k := by
  constructor
  · rintro ⟨hsum, h⟩
    refine ⟨hsum, fun k => ?_⟩
    rcases le_or_gt k (Fintype.card ι) with hk | hk
    · exact largestKSum_le hk fun s hs => hs ▸ h s
    · have : IsEmpty {s : Finset ι // s.card = k} := ⟨fun s => by
        have h1 : s.1.card ≤ Fintype.card ι := by simpa using Finset.card_le_card s.1.subset_univ
        have h2 : s.1.card = k := s.2
        omega⟩
      have hz : ∀ z : ι → ℝ, largestKSum z k = 0 := fun z => Real.iSup_of_isEmpty _
      exact le_of_eq ((hz x).trans (hz y).symm)
  · rintro ⟨hsum, h⟩
    exact ⟨hsum, fun s => (sum_le_largestKSum x s).trans (h s.card)⟩

/-- Majorization is unchanged when the entries of the smaller vector are permuted. -/
lemma Majorize.comp_perm_left {x y : ι → ℝ} (σ : Equiv.Perm ι) :
    Majorize (x ∘ σ) y ↔ Majorize x y := by
  rw [majorize_iff_forall_largestKSum, majorize_iff_forall_largestKSum]
  simp only [Function.comp_apply, Equiv.sum_comp, largestKSum_comp_perm]

/-- Majorization is unchanged when the entries of the larger vector are permuted. -/
lemma Majorize.comp_perm_right {x y : ι → ℝ} (σ : Equiv.Perm ι) :
    Majorize x (y ∘ σ) ↔ Majorize x y := by
  rw [majorize_iff_forall_largestKSum, majorize_iff_forall_largestKSum]
  simp only [Function.comp_apply, Equiv.sum_comp, largestKSum_comp_perm]

/-- Any permutation of `y` is majorized by `y`. -/
lemma majorize_comp_perm_self (y : ι → ℝ) (σ : Equiv.Perm ι) : Majorize (y ∘ σ) y :=
  (Majorize.comp_perm_left σ).2 (Majorize.refl y)

/-- Applying a permutation matrix to `y` produces a vector majorized by `y`. -/
lemma majorize_permMatrix_mulVec_self [DecidableEq ι] (y : ι → ℝ) (σ : Equiv.Perm ι) :
    Majorize (σ.permMatrix ℝ *ᵥ y) y := by
  rw [Matrix.permMatrix_mulVec]
  exact majorize_comp_perm_self y σ

/-- Reindexing both vectors along a single equivalence `e : κ ≃ ι` preserves majorization: the
largest-`k`-sum characterization is invariant under a common bijective reindexing of the entries. -/
lemma Majorize.comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) {x y : ι → ℝ} :
    Majorize (x ∘ e) (y ∘ e) ↔ Majorize x y := by
  rw [majorize_iff_forall_largestKSum, majorize_iff_forall_largestKSum]
  simp only [Function.comp_apply, Equiv.sum_comp, largestKSum_comp_equiv]

/-- **Majorization depends only on the value-multisets.**  If `x` and `x'` (resp. `y` and `y'`) have
the same multiset of values, then `x ≺ y ↔ x' ≺ y'`, even across different finite index types.  This
transports a majorization statement to any reindexing of its two vectors — e.g. from an explicitly
sorted spectrum to a quantum state's canonical eigenvalue distribution. -/
lemma majorize_congr_multiset {κ : Type*} [Fintype κ] {x y : ι → ℝ} {x' y' : κ → ℝ}
    (hx : Multiset.map x Finset.univ.val = Multiset.map x' Finset.univ.val)
    (hy : Multiset.map y Finset.univ.val = Multiset.map y' Finset.univ.val) :
    Majorize x y ↔ Majorize x' y' := by
  classical
  obtain ⟨ex, hex⟩ := exists_equiv_of_map_univ_val_eq hx
  obtain ⟨ey, hey⟩ := exists_equiv_of_map_univ_val_eq hy
  have hxe : x = x' ∘ ex := funext fun i => (hex i).symm
  have hye : y = y' ∘ ey := funext fun i => (hey i).symm
  rw [hxe, hye]
  have hrw : (y' ∘ ⇑ey) = (y' ∘ ⇑(ex.symm.trans ey)) ∘ ⇑ex := by funext i; simp
  rw [hrw, Majorize.comp_equiv ex, Majorize.comp_perm_right (ex.symm.trans ey)]

/-- The set of vectors majorized by a fixed `y` is convex (Nielsen–Chuang, Exercise 12.18).  It is
cut out by the total-sum equation together with the half-space conditions
`∑ i ∈ s, x i ≤ largestKSum y s.card`, and each of these is preserved under convex combinations. -/
lemma convex_setOf_majorize (y : ι → ℝ) : Convex ℝ {x | Majorize x y} := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  obtain ⟨hs₁, hl₁⟩ := hx₁
  obtain ⟨hs₂, hl₂⟩ := hx₂
  refine ⟨?_, fun s => ?_⟩
  · calc ∑ i, (a • x₁ + b • x₂) i
        = a * ∑ i, x₁ i + b * ∑ i, x₂ i := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum]
      _ = a * ∑ i, y i + b * ∑ i, y i := by rw [hs₁, hs₂]
      _ = ∑ i, y i := by rw [← add_mul, hab, one_mul]
  · calc ∑ i ∈ s, (a • x₁ + b • x₂) i
        = a * ∑ i ∈ s, x₁ i + b * ∑ i ∈ s, x₂ i := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum]
      _ ≤ a * largestKSum y s.card + b * largestKSum y s.card :=
          add_le_add (mul_le_mul_of_nonneg_left (hl₁ s) ha)
            (mul_le_mul_of_nonneg_left (hl₂ s) hb)
      _ = largestKSum y s.card := by rw [← add_mul, hab, one_mul]

/-- A convex combination of the permutations `σ.permMatrix ℝ *ᵥ y` of `y` is majorized by `y`.  This
is the vector form of the "easy" direction of Nielsen–Chuang, Proposition 12.11:
`x = ∑ⱼ pⱼ Pⱼ y ⟹ x ≺ y`. -/
lemma majorize_sum_smul_permMatrix_mulVec [DecidableEq ι] (y : ι → ℝ)
    {w : Equiv.Perm ι → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hw1 : ∑ σ, w σ = 1) :
    Majorize (∑ σ : Equiv.Perm ι, w σ • (σ.permMatrix ℝ *ᵥ y)) y :=
  (convex_setOf_majorize y).sum_mem (fun σ _ => hw σ) hw1
    (fun σ _ => majorize_permMatrix_mulVec_self y σ)

/-- Applying a doubly stochastic matrix `D` to `y` produces a vector majorized by `y`.  Combined
with Birkhoff's theorem this is the easy direction of the representation theorem (Nielsen–Chuang,
Proposition 12.11): `D *ᵥ y ≺ y`. -/
lemma Majorize.of_mem_doublyStochastic [DecidableEq ι] {D : Matrix ι ι ℝ}
    (hD : D ∈ doublyStochastic ℝ ι) (y : ι → ℝ) : Majorize (D *ᵥ y) y := by
  obtain ⟨w, hw, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  rw [← hwD, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  exact majorize_sum_smul_permMatrix_mulVec y hw hw1

/-- **Majorization does not shrink the support of a nonnegative vector.**  If `x` is majorized by a
nonnegative `y`, then `y` has at most as many nonzero entries as `x`: a more spread-out (majorized)
distribution `x ≺ y` is supported on at least as many coordinates as the more concentrated `y`.

The proof rests on a single observation.  Let `Sx` be the support of `x`.  Because the entries off
`Sx` vanish, the mass on `Sx` is the whole of `∑ x = ∑ y`; majorization then bounds this by the
largest `|Sx|`-entry sum of `y`, `largestKSum y Sx.card`.  Since `y ≥ 0`, that quantity is in turn
at most `∑ y`, so it *equals* `∑ y`: the `|Sx|` largest entries of `y` already carry all of its
mass.  A maximizing `|Sx|`-element set `t₀` therefore satisfies `∑_{t₀} y = ∑ y`, forcing `y` to
vanish on its complement.  So the support of `y` lies in `t₀`, whose cardinality is `|Sx|`. -/
lemma Majorize.card_filter_ne_zero_le {x y : ι → ℝ}
    (h : Majorize x y) (hy : ∀ i, 0 ≤ y i) :
    (univ.filter fun i => y i ≠ 0).card ≤ (univ.filter fun i => x i ≠ 0).card := by
  classical
  -- If the `k` largest entries of the nonnegative `y` already sum to all of `∑ y`, then `y` is
  -- supported on at most `k` coordinates.
  have key : ∀ k : ℕ, k ≤ Fintype.card ι → largestKSum y k = ∑ i, y i →
      (univ.filter fun i => y i ≠ 0).card ≤ k := by
    intro k hk hmass
    obtain ⟨t, _, ht⟩ := Finset.exists_subset_card_eq
      (show k ≤ (univ : Finset ι).card by simpa using hk)
    have : Nonempty {s : Finset ι // s.card = k} := ⟨t, ht⟩
    -- a `k`-subset `t₀` realising the largest `k`-entry sum
    obtain ⟨t0, -, ht0⟩ := Finset.exists_max_image (univ : Finset {s : Finset ι // s.card = k})
      (fun s => ∑ i ∈ (s : Finset ι), y i) univ_nonempty
    have hmax : largestKSum y k = ∑ i ∈ (t0 : Finset ι), y i :=
      le_antisymm (ciSup_le fun s => ht0 s (mem_univ s))
        (le_ciSup (bddAbove_range_subtype_sum y k) t0)
    have ht0mass : ∑ i ∈ (t0 : Finset ι), y i = ∑ i, y i := hmax.symm.trans hmass
    -- `y` carries all its mass on `t₀`, hence vanishes on the complement
    have hcompl : ∑ i ∈ (t0 : Finset ι)ᶜ, y i = 0 := by
      have hsplit := Finset.sum_add_sum_compl (t0 : Finset ι) y
      rw [ht0mass] at hsplit; linarith
    have hzero : ∀ i ∈ (t0 : Finset ι)ᶜ, y i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hy i).mp hcompl
    have hsub : (univ.filter fun i => y i ≠ 0) ⊆ (t0 : Finset ι) := by
      intro i hi
      rw [mem_filter] at hi
      by_contra hit0
      exact hi.2 (hzero i (Finset.mem_compl.mpr hit0))
    exact (Finset.card_le_card hsub).trans_eq t0.2
  refine key _ ?_ (le_antisymm ?_ ?_)
  · simpa using Finset.card_filter_le (univ : Finset ι) _
  · -- `largestKSum y |supp x| ≤ ∑ y`: every subset sum of a nonnegative vector is at most the total
    exact largestKSum_le (by simpa using Finset.card_filter_le (univ : Finset ι) _)
      fun s _ => Finset.sum_le_sum_of_subset_of_nonneg (subset_univ s) fun i _ _ => hy i
  · -- `∑ y ≤ largestKSum y |supp x|`: the support of `x` is a subset carrying all of `∑ x = ∑ y`
    have hmassx : ∑ i ∈ univ.filter (fun i => x i ≠ 0), x i = ∑ i, y i := by
      rw [← h.sum_eq]
      refine Finset.sum_subset (filter_subset _ _) fun i _ hi => ?_
      by_contra hne
      exact hi (mem_filter.mpr ⟨mem_univ i, hne⟩)
    calc ∑ i, y i = ∑ i ∈ univ.filter (fun i => x i ≠ 0), x i := hmassx.symm
      _ ≤ largestKSum y (univ.filter (fun i => x i ≠ 0)).card := h.2 _

/-!
### The Hardy–Littlewood–Pólya inequality

The "hard" direction of Proposition 12.11 — that `x ≺ y` implies `x = D *ᵥ y` for a doubly
stochastic `D` — is proved geometrically by separating `x` from the (compact, convex) set of such
`D *ᵥ y` with a hyperplane.  The analytic fact that rules out any separating hyperplane is
`Majorize.exists_perm_sum_mul_le`: for every weight vector `c`, `∑ i, c i * x i` is at most
`∑ i, c i * y (σ i)` for some permutation `σ`.  It is established here through the classical
Hardy–Littlewood–Pólya inequality for decreasing vectors (`Majorize.sum_mul_le_of_antitone`),
combined with the rearrangement inequality.
-/

/-- When `k ≤ n`, exactly `k` of the indices in `Fin n` satisfy `(i : ℕ) < k`: the leading `k`
indices form the prefix `{0, …, k-1}`. -/
private lemma card_filter_lt {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if i < k then 1 else 0) n,
    ← Finset.card_filter]
  have : {i ∈ range n | i < k} = range k := by ext x; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/-- For an antitone `z : Fin n → ℝ`, any `k`-element subset sum is at most the sum over the first
`k` indices.  Since `z` is decreasing, its `k` largest entries are the leading ones; the pinch
below bounds the entries of `z` outside the prefix by those inside it. -/
private lemma sum_le_sum_prefix_of_antitone {n : ℕ} {z : Fin n → ℝ} (hz : Antitone z) {k : ℕ}
    (hk : k ≤ n) (s : Finset (Fin n)) (hs : s.card = k) :
    ∑ i ∈ s, z i ≤ ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), z i := by
  set P : Finset (Fin n) := univ.filter (fun i : Fin n => (i : ℕ) < k) with hP
  have hPcard : P.card = k := by rw [hP]; exact card_filter_lt k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; rw [Finset.card_eq_zero] at hs; subst hs; simp [Finset.card_eq_zero.mp hPcard]
  rw [← Finset.sum_inter_add_sum_sdiff s P z, ← Finset.sum_inter_add_sum_sdiff P s z,
    Finset.inter_comm P s]
  have hcard : (s \ P).card = (P \ s).card := Finset.card_sdiff_comm (by rw [hs, hPcard])
  have hb : (k - 1) < n := by omega
  set b : ℝ := z ⟨k - 1, hb⟩ with hbdef
  have hBC : ∑ i ∈ s \ P, z i ≤ ∑ i ∈ P \ s, z i := by
    calc ∑ i ∈ s \ P, z i ≤ (s \ P).card • b := by
            apply Finset.sum_le_card_nsmul
            intro i hi
            simp only [Finset.mem_sdiff, hP, mem_filter, Finset.mem_univ, true_and, not_lt] at hi
            exact hz (by simp only [Fin.le_def]; omega)
      _ = (P \ s).card • b := by rw [hcard]
      _ ≤ ∑ i ∈ P \ s, z i := by
            apply Finset.card_nsmul_le_sum
            intro j hj
            simp only [Finset.mem_sdiff, hP, mem_filter, Finset.mem_univ, true_and] at hj
            exact hz (by simp only [Fin.le_def]; omega)
  linarith [hBC]

/-- The largest sum of `k` entries of an antitone `z : Fin n → ℝ` (with `k ≤ n`) is realised by its
first `k` entries: for a decreasing vector the `k` largest entries are exactly the leading ones. -/
lemma largestKSum_eq_sum_prefix_of_antitone {n : ℕ} {z : Fin n → ℝ} (hz : Antitone z) (k : ℕ)
    (hk : k ≤ n) :
    largestKSum z k = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), z i := by
  refine le_antisymm (largestKSum_le (by rw [Fintype.card_fin]; exact hk)
    fun s hs => sum_le_sum_prefix_of_antitone hz hk s hs) ?_
  have hPcard : (univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k := card_filter_lt k hk
  have hle := sum_le_largestKSum z (univ.filter (fun i : Fin n => (i : ℕ) < k))
  rwa [hPcard] at hle

/-- **Hardy–Littlewood–Pólya inequality (decreasing case).**  If `x`, `y`, `c : Fin n → ℝ` are all
antitone and `Majorize x y`, then `∑ i, c i * x i ≤ ∑ i, c i * y i`.  This is a summation by parts
on the `largestKSum` sequence: `M k := largestKSum y k - largestKSum x k` is nonnegative for every
`k` and vanishes at `k = 0, n`, and pairing its increments against the nonincreasing weights `c`
yields the inequality. -/
lemma Majorize.sum_mul_le_of_antitone {n : ℕ} {x y c : Fin n → ℝ} (hx : Antitone x)
    (hy : Antitone y) (hc : Antitone c) (h : Majorize x y) :
    ∑ i, c i * x i ≤ ∑ i, c i * y i := by
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  have ha : ∀ (z : Fin n → ℝ), Antitone z → ∀ i : Fin n,
      largestKSum z (i.val + 1) - largestKSum z i.val = z i := by
    intro z hz i
    rw [largestKSum_eq_sum_prefix_of_antitone hz (i.val + 1) i.isLt,
        largestKSum_eq_sum_prefix_of_antitone hz i.val i.isLt.le]
    have hins : univ.filter (fun j : Fin n => (j : ℕ) < i.val + 1)
        = insert i (univ.filter (fun j : Fin n => (j : ℕ) < i.val)) := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hh | hh
        · exact Or.inr hh
        · exact Or.inl (Fin.ext hh)
      · rintro (rfl | hj) <;> omega
    rw [hins, Finset.sum_insert (by simp)]; ring
  obtain ⟨_, hforall⟩ := majorize_iff_forall_largestKSum.mp h
  set M : ℕ → ℝ := fun k => largestKSum y k - largestKSum x k with hMdef
  set C : ℕ → ℝ := fun i => if hi : i < n then c ⟨i, hi⟩ else 0 with hCdef
  have hconv : ∑ i, (c i * y i - c i * x i)
      = ∑ i ∈ Finset.range n, C i • (M (i + 1) - M i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => C j • (M (j + 1) - M j)) n]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_eq_mul]
    have hCi : C i.val = c i := by simp only [hCdef, i.isLt, dite_eq_left]
    have hMi : M (i.val + 1) - M i.val = y i - x i := by
      simp only [hMdef]; have h1 := ha y hy i; have h2 := ha x hx i; linarith
    rw [hCi, hMi]; ring
  rw [hconv, Finset.sum_range_by_parts C (fun j => M (j + 1) - M j) n]
  have htel : ∀ m, ∑ j ∈ Finset.range m, (M (j + 1) - M j) = M m - M 0 :=
    fun m => Finset.sum_range_sub M m
  have hM0 : M 0 = 0 := by
    simp only [hMdef, largestKSum_eq_sum_prefix_of_antitone hx 0 (Nat.zero_le n),
      largestKSum_eq_sum_prefix_of_antitone hy 0 (Nat.zero_le n)]; simp
  have hMn : M n = 0 := by
    simp only [hMdef]
    have hfull : (univ.filter (fun j : Fin n => (j : ℕ) < n)) = univ := by ext j; simp
    rw [largestKSum_eq_sum_prefix_of_antitone hx n le_rfl,
        largestKSum_eq_sum_prefix_of_antitone hy n le_rfl, hfull, h.sum_eq]; ring
  simp only [htel, hM0, hMn, sub_zero, smul_zero, zero_sub]
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i hi
  rw [Finset.mem_range] at hi
  have hi1 : i + 1 < n := by omega
  have hi0 : i < n := by omega
  rw [smul_eq_mul]
  apply mul_nonpos_of_nonpos_of_nonneg
  · have hCle : C (i + 1) ≤ C i := by
      simp only [hCdef, hi1, hi0, dite_eq_left]
      exact hc (by simp only [Fin.le_def]; omega)
    linarith
  · simp only [hMdef]; linarith [hforall (i + 1)]

/-- The `Fin n` case of `Majorize.exists_perm_sum_mul_le`: sorting `x`, `y`, `c` into decreasing
order (via `Tuple.sort` of their negations) reduces the claim to the decreasing Hardy–Littlewood–
Pólya inequality, with the rearrangement inequality supplying the bound `∑ c i * x i ≤` the
sorted-together pairing. -/
private lemma exists_perm_sum_mul_le_fin {n : ℕ} {x y c : Fin n → ℝ} (h : Majorize x y) :
    ∃ τ : Equiv.Perm (Fin n), ∑ i, c i * x i ≤ ∑ i, c i * y (τ i) := by
  have hanti : ∀ (z : Fin n → ℝ), Antitone (z ∘ (Tuple.sort (fun i => - z i))) := by
    intro z a b hab
    have h2 := Tuple.monotone_sort (fun i => - z i) hab
    simp only [Function.comp_apply] at h2 ⊢; linarith
  set σc := Tuple.sort (fun i => - c i)
  set σx := Tuple.sort (fun i => - x i)
  set σy := Tuple.sort (fun i => - y i)
  have hcA : Antitone (c ∘ σc) := hanti c
  have hxA : Antitone (x ∘ σx) := hanti x
  have hyA : Antitone (y ∘ σy) := hanti y
  have hMsorted : Majorize (x ∘ σx) (y ∘ σy) :=
    (Majorize.comp_perm_left σx).mpr ((Majorize.comp_perm_right σy).mpr h)
  have hI : ∑ i, (c ∘ σc) i * (x ∘ σx) i ≤ ∑ i, (c ∘ σc) i * (y ∘ σy) i :=
    Majorize.sum_mul_le_of_antitone hxA hyA hcA hMsorted
  have hmono : Monovary (c ∘ σc) (x ∘ σx) := Antitone.monovary hcA hxA
  have hA : ∑ i, c i * x i ≤ ∑ i, (c ∘ σc) i * (x ∘ σx) i := by
    have key2 := Monovary.sum_mul_comp_perm_le_sum_mul hmono (σ := σc.trans σx.symm)
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] at key2 ⊢
    rw [← Equiv.sum_comp σc (fun j => c j * x j)]
    exact key2
  refine ⟨σc.symm.trans σy, le_trans hA (le_trans hI (le_of_eq ?_))⟩
  rw [← Equiv.sum_comp σc (fun j => c j * y ((σc.symm.trans σy) j))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- For any weight vector `c`, the paired sum `∑ i, c i * x i` of a majorized vector `x` is at most
`∑ i, c i * y (σ i)` for some permutation `σ` of the (larger) vector `y`.  Equivalently, `x` never
exceeds `y` against any linear functional once `y`'s entries may be permuted; this is the analytic
obstruction to separating `x` from the convex hull of the permutations of `y`, and hence the key
input to the representation theorem (Nielsen–Chuang, Proposition 12.11). -/
lemma Majorize.exists_perm_sum_mul_le {x y : ι → ℝ} (h : Majorize x y) (c : ι → ℝ) :
    ∃ σ : Equiv.Perm ι, ∑ i, c i * x i ≤ ∑ i, c i * y (σ i) := by
  set e := Fintype.equivFin ι with he
  have hM' : Majorize (x ∘ e.symm) (y ∘ e.symm) := by
    rw [majorize_iff_forall_largestKSum]
    refine ⟨?_, fun k => ?_⟩
    · simp only [Function.comp_apply]
      rw [Equiv.sum_comp e.symm x, Equiv.sum_comp e.symm y]; exact h.sum_eq
    · rw [largestKSum_comp_equiv x e.symm k, largestKSum_comp_equiv y e.symm k]
      exact (majorize_iff_forall_largestKSum.mp h).2 k
  obtain ⟨τ, hτ⟩ := exists_perm_sum_mul_le_fin (c := c ∘ e.symm) hM'
  refine ⟨e.trans (τ.trans e.symm), ?_⟩
  have hLHS : ∑ j, c j * x j = ∑ i, (c ∘ e.symm) i * (x ∘ e.symm) i :=
    (Equiv.sum_comp e.symm (fun j => c j * x j)).symm
  have hRHS : ∑ j, c j * y ((e.trans (τ.trans e.symm)) j)
      = ∑ i, (c ∘ e.symm) i * (y ∘ e.symm) (τ i) := by
    rw [← Equiv.sum_comp e.symm (fun j => c j * y ((e.trans (τ.trans e.symm)) j))]
    apply Finset.sum_congr rfl; intro i _
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hLHS, hRHS]; exact hτ

/-!
### The representation theorem (Proposition 12.11)

Combining the analytic obstruction `Majorize.exists_perm_sum_mul_le` with the geometric
Hahn–Banach separation theorem yields the "hard" direction: a majorized vector `x` lies in the
(compact, convex) set of images `D *ᵥ y` of `y` under doubly stochastic matrices `D`.  Together with
the easy direction (`Majorize.of_mem_doublyStochastic`) this gives the Hardy–Littlewood–Pólya
characterisation `Majorize x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x`, and — unwinding `D` into a
convex combination of permutation matrices via Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) — Nielsen–Chuang's Proposition 12.11
`Majorize x y ↔ x = ∑ⱼ pⱼ Pⱼ y`.
-/

/-- **Hard direction of the representation theorem.**  If `x` is majorized by `y`, then `x = D *ᵥ y`
for some doubly stochastic matrix `D`.

The set `S = {D *ᵥ y | D ∈ doublyStochastic ℝ ι}` is the image of the doubly stochastic matrices
under the linear map `L : D ↦ D *ᵥ y`.  It is convex (linear image of the convex set of doubly
stochastic matrices) and closed: by Birkhoff's theorem the doubly stochastic matrices are the convex
hull of the finitely many permutation matrices, so `S` is the convex hull of a finite set.  Were
`x ∉ S`, `geometric_hahn_banach_closed_point` would give a continuous linear functional `f` with
`f a < u < f x` for all `a ∈ S`.  Writing `c i := f (Pi.single i 1)`, we have
`f v = ∑ i, c i * v i`,
so for every permutation `σ` (as `σ.permMatrix ℝ *ᵥ y ∈ S`) this reads `∑ i, c i * y (σ i) < f x =
∑ i, c i * x i` — contradicting `Majorize.exists_perm_sum_mul_le`, which supplies a `σ` with
`∑ i, c i * x i ≤ ∑ i, c i * y (σ i)`. -/
lemma Majorize.exists_doublyStochastic_mulVec [DecidableEq ι] {x y : ι → ℝ} (h : Majorize x y) :
    ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x := by
  classical
  -- the linear map `D ↦ D *ᵥ y`, and the image `S` of the doubly stochastic matrices under it
  let L : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun D => D *ᵥ y
      map_add' := fun A B => Matrix.add_mulVec A B y
      map_smul' := fun a A => Matrix.smul_mulVec a A y }
  set S : Set (ι → ℝ) := ⇑L '' ↑(doublyStochastic ℝ ι) with hSdef
  suffices hxS : x ∈ S from hxS
  by_contra hx
  -- `S` is convex and closed
  have hSconv : Convex ℝ S := convex_doublyStochastic.linear_image L
  have hSclosed : IsClosed S := by
    rw [hSdef, doublyStochastic_eq_convexHull_permMatrix, LinearMap.image_convexHull]
    exact Set.Finite.isClosed_convexHull ℝ
      (Set.Finite.image _ (Set.finite_range fun σ : Equiv.Perm ι => σ.permMatrix ℝ))
  -- separate `x` from `S`
  obtain ⟨f, u, hfs, hfx⟩ := geometric_hahn_banach_closed_point hSconv hSclosed hx
  -- represent `f` as a weighted coordinate sum with weights `c`
  let c : ι → ℝ := fun i => f (Pi.single i 1 : ι → ℝ)
  have hfrepr : ∀ v : ι → ℝ, f v = ∑ i, c i * v i := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsingle : Pi.single i (v i) = v i • (Pi.single i 1 : ι → ℝ) := by
      ext j; simp [Pi.single_apply]
    rw [hsingle, map_smul, smul_eq_mul, mul_comm]
  -- the analytic obstruction contradicts the strict separation
  obtain ⟨σ, hσ⟩ := h.exists_perm_sum_mul_le c
  have hmem : (σ.permMatrix ℝ *ᵥ y) ∈ S := by
    rw [hSdef]; exact ⟨σ.permMatrix ℝ, permMatrix_mem_doublyStochastic, rfl⟩
  have h1 : f (σ.permMatrix ℝ *ᵥ y) < u := hfs _ hmem
  rw [hfrepr] at h1 hfx
  simp only [Matrix.permMatrix_mulVec, Function.comp_apply] at h1
  linarith

/-- **Hardy–Littlewood–Pólya characterisation.**  `x` is majorized by `y` if and only if
`x = D *ᵥ y` for some doubly stochastic matrix `D`.  The forward direction is
`Majorize.exists_doublyStochastic_mulVec`; the reverse is `Majorize.of_mem_doublyStochastic`. -/
theorem majorize_iff_exists_doublyStochastic [DecidableEq ι] {x y : ι → ℝ} :
    Majorize x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x := by
  refine ⟨fun h => h.exists_doublyStochastic_mulVec, ?_⟩
  rintro ⟨D, hD, rfl⟩
  exact Majorize.of_mem_doublyStochastic hD y

/-- **Nielsen–Chuang, Proposition 12.11.**  `x` is majorized by `y` if and only if `x` is a convex
combination of permutations of `y`: there is a probability distribution `w` over permutations `σ`
with `x = ∑ σ, w σ • (σ.permMatrix ℝ *ᵥ y) = ∑ⱼ pⱼ Pⱼ y`.  This packages the doubly stochastic
characterisation `majorize_iff_exists_doublyStochastic` with Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`), which resolves a doubly stochastic `D` into such a
convex combination of permutation matrices. -/
theorem majorize_iff_exists_sum_perm [DecidableEq ι] {x y : ι → ℝ} :
    Majorize x y ↔ ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      x = ∑ σ : Equiv.Perm ι, w σ • (σ.permMatrix ℝ *ᵥ y) := by
  constructor
  · intro h
    obtain ⟨D, hD, hDx⟩ := h.exists_doublyStochastic_mulVec
    obtain ⟨w, hw, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
    refine ⟨w, hw, hw1, ?_⟩
    rw [← hDx, ← hwD, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec]
  · rintro ⟨w, hw, hw1, rfl⟩
    exact majorize_sum_smul_permMatrix_mulVec y hw hw1

/-!
### The tail-sum characterisation (Nielsen–Chuang, Exercise 12.17)

Exercise 12.17 characterises majorization through the *cut* (or *tail*) functions
`tailSum x t = ∑ⱼ max (xⱼ - t) 0`: `x ≺ y` iff `tailSum x t ≤ tailSum y t` for every threshold `t`
and the total sums agree.  The functions `a ↦ max (a - t) 0` are a spanning family of convex
"angle" functions, so this is the instance of the Hardy–Littlewood–Pólya principle "`∑ φ(xⱼ) ≤
∑ φ(yⱼ)` for all convex `φ`" carrying exactly enough information to recover majorization.

The proof is a Legendre-type conjugacy between `tailSum` and `largestKSum`:
`largestKSum x k - k · t ≤ tailSum x t` always (`largestKSum_le_tailSum_add`), with equality at the
threshold `t = ` the `k`-th largest entry (`exists_tailSum_add_eq_largestKSum`, obtained from a
maximising `k`-subset by an exchange argument).  Combined with the largest-`k`-sum form of
majorization (`majorize_iff_forall_largestKSum`) this yields both directions without any sorting.
-/

/-- `tailSum x t = ∑ i, max (x i - t) 0` is the *tail* (or *cut*) function of `x` at threshold `t`:
the sum of the positive parts of the shifted entries `x i - t`.  As a function of `t` it is the
Legendre-type conjugate of `largestKSum x`; Nielsen–Chuang, Exercise 12.17 characterises
majorization through it. -/
noncomputable def tailSum (x : ι → ℝ) (t : ℝ) : ℝ := ∑ i, max (x i - t) 0

/-- The tail function is the sum, over the entries strictly above the threshold, of the shifted
entries `x i - t`: the entries at or below `t` contribute a zero positive part. -/
lemma tailSum_eq_sum_filter (x : ι → ℝ) (t : ℝ) :
    tailSum x t = ∑ i ∈ univ.filter (fun i => t < x i), (x i - t) := by
  rw [tailSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : t < x i
  · rw [ite_eq_left h, max_eq_left (by linarith)]
  · rw [ite_eq_right h, max_eq_right (by linarith [not_lt.mp h])]

/-- The largest sum of `k` entries never exceeds `tailSum x t + k · t`: every `k`-subset sum
`∑ i ∈ s, x i = ∑ i ∈ s, (x i - t) + k · t` is bounded by `tailSum x t + k · t`, since each shifted
entry `x i - t` is at most its positive part `max (x i - t) 0` and these are nonnegative.  This is
the "easy" half of the conjugacy between `largestKSum` and `tailSum`. -/
lemma largestKSum_le_tailSum_add (x : ι → ℝ) (t : ℝ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    largestKSum x k ≤ tailSum x t + k * t := by
  refine largestKSum_le hk fun s hs => ?_
  have hle : ∑ i ∈ s, (x i - t) ≤ tailSum x t := by
    rw [tailSum]
    exact (Finset.sum_le_sum fun i _ => le_max_left _ _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ => le_max_right _ _)
  have hsplit : ∑ i ∈ s, x i = ∑ i ∈ s, (x i - t) + s.card * t := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  rw [hsplit, hs]
  linarith

omit [Fintype ι] in
/-- The largest sum of `0` entries is `0`: the empty subset is the only `0`-element subset. -/
lemma largestKSum_zero [Finite ι] (x : ι → ℝ) : largestKSum x 0 = 0 := by
  have : Nonempty {s : Finset ι // s.card = 0} := ⟨⟨∅, Finset.card_empty⟩⟩
  refine le_antisymm (ciSup_le fun s => ?_) ?_
  · rw [Finset.card_eq_zero.mp s.2]; simp
  · simpa using sum_le_largestKSum x (∅ : Finset ι)

/-- The largest sum of `k` entries is `0` once `k` exceeds the dimension, since no `k`-subset
exists. -/
lemma largestKSum_eq_zero (x : ι → ℝ) {k : ℕ} (h : Fintype.card ι < k) :
    largestKSum x k = 0 := by
  have : IsEmpty {s : Finset ι // s.card = k} := ⟨fun s => by
    have h1 : s.1.card ≤ Fintype.card ι := by simpa using Finset.card_le_card s.1.subset_univ
    have h2 : s.1.card = k := s.2
    omega⟩
  exact Real.iSup_of_isEmpty _

/-- The largest sum of `k` entries is *attained*: when `k ≤ card ι` there is an actual
`k`-element subset whose entry-sum equals `largestKSum x k`. -/
lemma largestKSum_attained (x : ι → ℝ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    ∃ s : Finset ι, s.card = k ∧ largestKSum x k = ∑ i ∈ s, x i := by
  classical
  obtain ⟨t0, -, ht0⟩ :=
    Finset.exists_subset_card_eq (show k ≤ (univ : Finset ι).card by simpa using hk)
  have : Nonempty {s : Finset ι // s.card = k} := ⟨t0, ht0⟩
  obtain ⟨s0, hs0max⟩ :=
    Finite.exists_max (fun s : {s : Finset ι // s.card = k} => ∑ i ∈ (s : Finset ι), x i)
  exact ⟨s0, s0.2, le_antisymm (ciSup_le fun s => hs0max s)
    (le_ciSup (bddAbove_range_subtype_sum x k) s0)⟩

/-- The conjugacy is *tight*: for `1 ≤ k ≤ card`, the bound
`largestKSum y k ≤ tailSum y t + k · t` is attained at the threshold `t = ` the `k`-th largest
entry of `y`.  Concretely, take a maximising `k`-subset `S` (`largestKSum y k = ∑ i ∈ S, y i`) and
let `t` be its smallest entry `y i₀`; an exchange argument shows every entry outside `S` is `≤ t`,
so `tailSum y t` collapses to `∑ i ∈ S, (y i - t) = largestKSum y k - k · t`. -/
lemma exists_tailSum_add_eq_largestKSum {y : ι → ℝ} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) :
    ∃ t : ℝ, tailSum y t + k * t = largestKSum y k := by
  classical
  obtain ⟨S, hScard, hSsum⟩ := largestKSum_attained y hk
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hScard]; omega
  obtain ⟨i0, hi0S, hi0min⟩ := S.exists_min_image y hSne
  refine ⟨y i0, ?_⟩
  -- exchange: every entry outside the maximising set is at most the set's smallest entry `y i₀`
  have hout : ∀ j, j ∉ S → y j ≤ y i0 := by
    intro j hj
    have hjE : j ∉ S.erase i0 := fun h => hj (Finset.mem_of_mem_erase h)
    have hcard' : (insert j (S.erase i0)).card = k := by
      rw [Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem hi0S, hScard]; omega
    have hle : ∑ i ∈ insert j (S.erase i0), y i ≤ ∑ i ∈ S, y i := by
      have hb := sum_le_largestKSum y (insert j (S.erase i0))
      rw [hcard', hSsum] at hb; exact hb
    rw [Finset.sum_insert hjE] at hle
    have hea := S.sum_erase_add y hi0S
    linarith
  -- evaluate the tail function at the threshold `t = y i₀`
  have hzero : ∀ i ∈ (univ : Finset ι), i ∉ S → max (y i - y i0) 0 = 0 :=
    fun i _ hiS => max_eq_right (by linarith [hout i hiS])
  have htail : tailSum y (y i0) = ∑ i ∈ S, (y i - y i0) := by
    rw [tailSum, ← Finset.sum_subset (Finset.subset_univ S) hzero]
    exact Finset.sum_congr rfl fun i hi => max_eq_left (by linarith [hi0min i hi])
  rw [htail, hSsum, Finset.sum_sub_distrib, Finset.sum_const, hScard, nsmul_eq_mul]; ring

/-- **Nielsen–Chuang, Exercise 12.17.**  `x` is majorized by `y` if and only if the tail functions
are pointwise ordered, `tailSum x t ≤ tailSum y t` for every threshold `t`, together with equality
of the total sums.

Forward: `a ↦ max (a - t) 0` is convex, so `tailSum x t = ∑ i ∈ S, (x i - t)` over the entries
above `t` is bounded, via `largestKSum x ≤ largestKSum y`, by `tailSum y t`.  Reverse: for each `k`
the
tail hypothesis at the tight threshold `t` (`exists_tailSum_add_eq_largestKSum` for `y`) gives
`largestKSum x k ≤ tailSum x t + k · t ≤ tailSum y t + k · t = largestKSum y k`, which is the
largest-`k`-sum form of majorization. -/
theorem majorize_iff_forall_tailSum {x y : ι → ℝ} :
    Majorize x y ↔ (∀ t : ℝ, tailSum x t ≤ tailSum y t) ∧ ∑ i, x i = ∑ i, y i := by
  constructor
  · intro h
    obtain ⟨hsum, hlarge⟩ := majorize_iff_forall_largestKSum.mp h
    refine ⟨fun t => ?_, hsum⟩
    obtain ⟨s, hs_card, hxeq⟩ : ∃ s : Finset ι, s.card ≤ Fintype.card ι ∧
        tailSum x t = (∑ i ∈ s, x i) - s.card * t := by
      refine ⟨univ.filter (fun i => t < x i), ?_, ?_⟩
      · rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      · rw [tailSum_eq_sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1 : ∑ i ∈ s, x i ≤ largestKSum y s.card :=
      (sum_le_largestKSum x s).trans (hlarge s.card)
    have h2 : largestKSum y s.card ≤ tailSum y t + s.card * t :=
      largestKSum_le_tailSum_add y t hs_card
    rw [hxeq]; linarith
  · rintro ⟨htail, hsum⟩
    rw [majorize_iff_forall_largestKSum]
    refine ⟨hsum, fun k => ?_⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      exact le_of_eq (by rw [largestKSum_zero x, largestKSum_zero y])
    · rcases le_or_gt k (Fintype.card ι) with hk | hk
      · obtain ⟨t, ht⟩ := exists_tailSum_add_eq_largestKSum hk0 hk
        calc largestKSum x k ≤ tailSum x t + k * t := largestKSum_le_tailSum_add x t hk
          _ ≤ tailSum y t + k * t := by linarith [htail t]
          _ = largestKSum y k := ht
      · exact le_of_eq (by rw [largestKSum_eq_zero x hk, largestKSum_eq_zero y hk])

/-!
### The inductive step of Proposition 12.11 (Nielsen–Chuang, Exercise 12.19)

Nielsen–Chuang prove the representation theorem `majorize_iff_exists_sum_perm` (Proposition 12.11)
by an induction on the dimension using *T-transforms*.  In the inductive step one has decreasing
vectors `x y : Fin (n + 1) → ℝ` with `x ≺ y`, so in particular `x 0 ≤ y 0`; one picks a pivot index
`p ≠ 0` with `y p ≤ x 0 ≤ y (p - 1)` and a weight `t ∈ [0, 1]` with `x 0 = t * y 0 + (1 - t) * y p`,
and mixes entries `0` and `p` of `y` with the doubly stochastic combination `t • 1 + (1 - t) • T`
(`T` the transposition of `0` and `p`).  The image `D y` then has `(D y) 0 = x 0`, and dropping the
leading coordinate of both vectors gives `x' = Fin.tail x` and `y' = Fin.tail (D y)`.  Since `D`
changes only entry `p` of `y` (to `(1 - t) * y 0 + t * y p`) and the discarded entry `0`,
`y' = Fin.tail (Function.update y p ((1 - t) * y 0 + t * y p))`.  Exercise 12.19 asks to verify
`x' ≺ y'`, which then feeds the inductive hypothesis.

`majorize_tail_update_of_antitone` records this verification.  The library establishes Proposition
12.11 itself by the equivalent separating-hyperplane route
(`Majorize.exists_doublyStochastic_mulVec`), so this lemma is not on that path; it is the faithful
formalisation of the exercise.
-/

/-- Reindexing lemma: a prefix sum of `Fin.tail f` — over the first `k` indices of `Fin n` — equals
the sum of `f` over the indices `1, …, k` of `Fin (n + 1)`, the successor map `i ↦ i.succ` being a
bijection between the two index sets. -/
private lemma sum_prefix_filter_tail {n : ℕ} (f : Fin (n + 1) → ℝ) (k : ℕ) :
    ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), Fin.tail f i
      = ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), f i := by
  refine Finset.sum_bij (fun (a : Fin n) (_ : a ∈ _) => a.succ) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, Fin.val_succ] at ha ⊢
    omega
  · intro a₁ _ a₂ _ h
    exact Fin.succ_injective n h
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    refine ⟨b.pred hb0, ?_, Fin.succ_pred b hb0⟩
    simp only [mem_filter, mem_univ, true_and, Fin.val_pred]
    omega
  · intro a _; rfl

/-- For a decreasing `z : Fin (n + 1) → ℝ` and `k ≤ n`, the sum of `z` over the indices `1, …, k`
equals the largest-`(k+1)`-entry sum minus the leading entry `z 0`: since `z` is decreasing, its
`k + 1` largest entries are the leading block `0, …, k`; removing index `0` leaves `1, …, k`. -/
private lemma sum_filter_one_le_eq_largestKSum_sub {n : ℕ} {z : Fin (n + 1) → ℝ} (hz : Antitone z)
    {k : ℕ} (hk : k ≤ n) :
    ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), z i
      = largestKSum z (k + 1) - z 0 := by
  rw [largestKSum_eq_sum_prefix_of_antitone hz (k + 1) (by omega)]
  have hins : univ.filter (fun i : Fin (n + 1) => (i : ℕ) < k + 1)
      = insert 0 (univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hi
      rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
      · exact Or.inl (Fin.ext (by simpa using h0))
      · exact Or.inr ⟨h0, hi⟩
    · rintro (rfl | ⟨_, hi⟩)
      · simp
      · exact hi
  rw [hins, Finset.sum_insert (by simp)]
  ring

/-- **Nielsen–Chuang, Exercise 12.19** (the inductive step of Proposition 12.11).  Let
`x y : Fin (n + 1) → ℝ` be decreasing (`Antitone`) with `x` majorized by `y`.  Fix a pivot `p ≠ 0`
with `y p ≤ x 0 ≤ y (p - 1)` and a weight `t ∈ [0, 1]` with `x 0 = t * y 0 + (1 - t) * y p`.  Form
`y'` by replacing the `p`-th entry of `y` with the complementary convex combination
`(1 - t) * y 0 + t * y p` and dropping the leading coordinate, and drop the leading coordinate of
`x` to form `x'`.  Then `x'` is majorized by `y'`.

N&C's inductive step additionally assumes `0 ≤ t ≤ 1` and `y p ≤ x 0`, which make the replacement a
genuine convex combination (keeping `y'` a doubly stochastic image of `y` for the surrounding
induction).  Those bounds are not needed for `x' ≺ y'` — only `x 0 ≤ y (p - 1)`, together with the
orderings and `x ≺ y`, is used — so they are dropped here for a minimal statement; the lemma then
covers N&C's case a fortiori. -/
theorem majorize_tail_update_of_antitone {n : ℕ} {x y : Fin (n + 1) → ℝ} (hx : Antitone x)
    (hy : Antitone y) (hxy : Majorize x y) {p : Fin (n + 1)} (hp : p ≠ 0) {t : ℝ}
    (hhi : x 0 ≤ y (p - 1)) (hx0 : x 0 = t * y 0 + (1 - t) * y p) :
    Majorize (Fin.tail x) (Fin.tail (Function.update y p ((1 - t) * y 0 + t * y p))) := by
  classical
  set w : ℝ := (1 - t) * y 0 + t * y p with hw
  set yD : Fin (n + 1) → ℝ := Function.update y p w with hyD
  -- algebraic identity relating the mixed entry `w` to the pivot data
  have hwx : w + x 0 = y 0 + y p := by rw [hw, hx0]; ring
  -- the pivot index is positive
  have hp_pos : 0 < (p : ℕ) := by
    rcases Nat.eq_zero_or_pos (p : ℕ) with h | h
    · exact absurd (Fin.ext (by simpa using h)) hp
    · exact h
  -- `x' = Fin.tail x` is decreasing
  have hxtail : Antitone (Fin.tail x) := by
    intro a b hab
    have hsucc : a.succ ≤ b.succ := by
      simp only [Fin.le_def, Fin.val_succ] at hab ⊢; omega
    exact hx hsucc
  -- the leading entry of `yD` is unchanged
  have hyD0 : yD 0 = y 0 := by rw [hyD]; exact Function.update_of_ne (Ne.symm hp) _ _
  -- equal total sums for `x'` and `y'`
  have hsum : ∑ i, Fin.tail x i = ∑ i, Fin.tail yD i := by
    have hAx : ∑ i, x i = x 0 + ∑ i, Fin.tail x i := Fin.sum_univ_succ x
    have hAy : ∑ i, yD i = yD 0 + ∑ i, Fin.tail yD i := Fin.sum_univ_succ yD
    have hD : ∑ i, yD i = w + ((∑ i, y i) - y p) := by
      rw [hyD, Finset.sum_update_of_mem (mem_univ p) y w,
        Finset.sum_sdiff_eq_sub (Finset.subset_univ _), Finset.sum_singleton]
    have hE : ∑ i, x i = ∑ i, y i := hxy.sum_eq
    linarith [hAx, hAy, hyD0, hD, hE, hwx]
  -- majorization via the largest-`k`-sum characterisation
  rw [majorize_iff_forall_largestKSum]
  refine ⟨hsum, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact le_of_eq (by rw [hk0, largestKSum_zero, largestKSum_zero])
  rcases le_or_gt k n with hk | hk
  · -- the substantive range `1 ≤ k ≤ n`
    have hcardP : (univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k := card_filter_lt k hk
    -- the core inequality over the index block `1, …, k` of `Fin (n + 1)`
    have hcore :
        ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), x i
          ≤ ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), yD i := by
      by_cases hpin : p ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1)
      · -- Case A: the pivot lies in the block
        have hAsum :
            ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), yD i
              = w + ((∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), y i)
                  - y p) := by
          rw [hyD, Finset.sum_update_of_mem hpin y w,
            Finset.sum_sdiff_eq_sub (Finset.singleton_subset_iff.mpr hpin), Finset.sum_singleton]
        have hQx := sum_filter_one_le_eq_largestKSum_sub hx hk
        have hQy := sum_filter_one_le_eq_largestKSum_sub hy hk
        have hmaj : largestKSum x (k + 1) ≤ largestKSum y (k + 1) :=
          (majorize_iff_forall_largestKSum.mp hxy).2 (k + 1)
        rw [hAsum, hQx, hQy]; linarith [hwx]
      · -- Case B: the pivot lies beyond the block, so entries are unchanged there
        have hpk : k + 1 ≤ (p : ℕ) := by
          by_contra hcon
          exact hpin (by simp only [mem_filter, mem_univ, true_and]; omega)
        have hBsum :
            ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), yD i
              = ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), y i := by
          rw [hyD]; refine Finset.sum_congr rfl fun i hi => ?_
          exact Function.update_of_ne (by rintro rfl; exact hpin hi) _ _
        rw [hBsum]
        refine Finset.sum_le_sum fun i hi => ?_
        simp only [mem_filter, mem_univ, true_and] at hi
        have hi_le : (i : ℕ) ≤ ((p - 1 : Fin (n + 1)) : ℕ) := by
          rw [Fin.coe_sub_one, ite_eq_right hp]; omega
        calc x i ≤ x 0 := hx (Fin.zero_le i)
          _ ≤ y (p - 1) := hhi
          _ ≤ y i := hy (Fin.le_def.mpr hi_le)
    calc largestKSum (Fin.tail x) k
        = ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), x i := by
          rw [largestKSum_eq_sum_prefix_of_antitone hxtail k hk]; exact sum_prefix_filter_tail x k
      _ ≤ ∑ i ∈ univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k + 1), yD i := hcore
      _ = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), Fin.tail yD i :=
          (sum_prefix_filter_tail yD k).symm
      _ ≤ largestKSum (Fin.tail yD) k := by
          have h := sum_le_largestKSum (Fin.tail yD) (univ.filter (fun i : Fin n => (i : ℕ) < k))
          rwa [hcardP] at h
  · -- `k > n`: both largest sums vanish (no `k`-subset of `Fin n`)
    have hcard : Fintype.card (Fin n) < k := by rw [Fintype.card_fin]; exact hk
    exact le_of_eq (by rw [largestKSum_eq_zero (Fin.tail x) hcard,
      largestKSum_eq_zero (Fin.tail yD) hcard])
