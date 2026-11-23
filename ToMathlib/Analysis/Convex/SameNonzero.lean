/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.Convex.Majorization

/-!
# Real vectors with identical non-zero entries

For finitely-indexed real families `x : ι → ℝ` and `y : κ → ℝ` we record the relation `SameNonzero x
y`: the two families have *identical non-zero entries*, i.e. the multiset of non-zero values of `x`
equals that of `y`. The index types `ι` and `κ` may differ, so this captures equality "up to a
permutation of the entries and the insertion or deletion of zeros" — Nielsen and Chuang's `≅`
relation on vectors (*Quantum Computation and Quantum Information*, Ex. 12.22).

The relation is the natural companion of majorization (`Majorize`, `Mathlib/Analysis/Convex/
Majorization.lean`): where `Majorize` needs a fixed index type, `SameNonzero` is heterogeneous, so
it compares e.g. a spectrum with a spectrum-tensored-with-a-probability-vector (larger dimension).

## Main definitions

* `nonzeroEntries x`: the multiset of non-zero values `x i` (with multiplicity).
* `SameNonzero x y`: `nonzeroEntries x = nonzeroEntries y`.

## Main statements

* `SameNonzero.refl`, `SameNonzero.symm`, `SameNonzero.trans`: `SameNonzero` behaves as a (partial)
  equivalence across index types.
* `mem_nonzeroEntries`, `sum_nonzeroEntries`: membership in and the sum of `nonzeroEntries`.
* `nonzeroEntries_comp_equiv`, `SameNonzero.of_equiv`: reindexing by a bijection preserves the
  non-zero entries.
* `SameNonzero.sum_eq`: identical non-zero entries force equal total sums (over the two, possibly
  different, index types).
* `nonzeroEntries_eq_map_of_forall_ne_zero`: for an entrywise non-zero family `nonzeroEntries` is
  the full image multiset (nothing is filtered out).
* `SameNonzero.exists_equiv`: two entrywise non-zero families with identical non-zero entries are a
  reindexing of one another — `∃ e : ι ≃ κ, y (e i) = x i`; with no zeros to insert or delete, `≅`
  is a genuine permutation of the indices.

## Tags

majorization, multiset, spectrum
-/

public section

open Finset
open scoped BigOperators

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

open scoped Classical in
/-- The multiset of *non-zero* entries of a finitely-indexed real family `x : ι → ℝ`, with
multiplicity: the values `x i` that are non-zero, collected over all `i`. -/
noncomputable def nonzeroEntries (x : ι → ℝ) : Multiset ℝ :=
  ((Finset.univ : Finset ι).val.map x).filter (· ≠ 0)

/-- A real number `r` occurs among the non-zero entries of `x` iff it is non-zero and is a value of
`x`. -/
theorem mem_nonzeroEntries {x : ι → ℝ} {r : ℝ} :
    r ∈ nonzeroEntries x ↔ r ≠ 0 ∧ ∃ i, x i = r := by
  classical
  simp only [nonzeroEntries, Multiset.mem_filter, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ, true_and]
  exact and_comm

/-- The sum of the non-zero entries of `x` is the sum of all the entries of `x` (the zero entries
contribute nothing). -/
theorem sum_nonzeroEntries (x : ι → ℝ) : (nonzeroEntries x).sum = ∑ i, x i := by
  classical
  rw [nonzeroEntries, Finset.sum,
    ← Multiset.sum_filter_add_sum_filter_not (s := Multiset.map x univ.val) (· ≠ 0),
    Multiset.sum_eq_zero fun a ha => not_not.1 (Multiset.mem_filter.1 ha).2, add_zero]

/-- Reindexing by a bijection `e : κ ≃ ι` leaves the multiset of non-zero entries unchanged. -/
theorem nonzeroEntries_comp_equiv (x : ι → ℝ) (e : κ ≃ ι) :
    nonzeroEntries (x ∘ e) = nonzeroEntries x := by
  rw [nonzeroEntries, nonzeroEntries, ← Multiset.map_map x e, ← Equiv.coe_toEmbedding,
    ← Finset.map_val, Finset.map_univ_equiv]

/-- **Padding with an all-zero block preserves the non-zero entries.** Appending a family of zeros
(indexed by a second type `κ`) to `x` leaves its multiset of non-zero entries unchanged:
`nonzeroEntries (Sum.elim x 0) = nonzeroEntries x`. This is the multiset identity behind extending a
partial diagonalizing eigen-family to a full orthonormal basis — the adjoined complement vectors
carry eigenvalue `0` and contribute nothing to the spectrum's non-zero part. -/
theorem nonzeroEntries_sum_elim_zero (x : ι → ℝ) :
    nonzeroEntries (Sum.elim x (fun _ : κ => (0 : ℝ))) = nonzeroEntries x := by
  classical
  have huniv : ((Finset.univ : Finset (ι ⊕ κ)).val)
      = (Finset.univ : Finset ι).val.map Sum.inl + (Finset.univ : Finset κ).val.map Sum.inr := by
    rw [← Finset.univ_disjSum_univ]; rfl
  simp only [nonzeroEntries, huniv, Multiset.map_add, Multiset.map_map, Multiset.filter_add,
    Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hz : Multiset.filter (· ≠ (0 : ℝ))
      (Multiset.map (fun _ : κ => (0 : ℝ)) (Finset.univ : Finset κ).val) = 0 := by
    refine Multiset.filter_eq_nil.mpr fun a ha => ?_
    simp only [Multiset.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    simp
  rw [hz, add_zero]

/-- **A nowhere-zero family's non-zero entries are its whole image multiset.** If `x i ≠ 0` for
every `i`, the non-zero-entries filter discards nothing, so `nonzeroEntries x` is the full image
multiset `map x univ.val`. The companion of `nonzeroEntries_sum_elim_zero`: where that drops padded
zeros, this records that with no zeros present nothing is dropped. -/
theorem nonzeroEntries_eq_map_of_forall_ne_zero {x : ι → ℝ} (hx : ∀ i, x i ≠ 0) :
    nonzeroEntries x = Multiset.map x Finset.univ.val := by
  rw [nonzeroEntries]
  refine Multiset.filter_eq_self.2 fun a ha => ?_
  rw [Multiset.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact hx i

/-- **Identical non-zero entries.** Two finitely-indexed real families `x : ι → ℝ` and `y : κ → ℝ`
(over possibly different index types) have the *same non-zero entries* when the multiset of non-zero
values of `x` equals that of `y`. This is Nielsen and Chuang's `≅` on vectors: equality up to a
permutation of the entries and the insertion/deletion of zeros. -/
def SameNonzero (x : ι → ℝ) (y : κ → ℝ) : Prop :=
  nonzeroEntries x = nonzeroEntries y

namespace SameNonzero

/-- `SameNonzero` is reflexive. -/
theorem refl (x : ι → ℝ) : SameNonzero x x := Eq.refl (nonzeroEntries x)

/-- `SameNonzero` is symmetric (across the two index types). -/
theorem symm {x : ι → ℝ} {y : κ → ℝ} (h : SameNonzero x y) : SameNonzero y x := Eq.symm h

/-- `SameNonzero` is transitive (across the three index types). -/
theorem trans {x : ι → ℝ} {y : κ → ℝ} {z : μ → ℝ}
    (h₁ : SameNonzero x y) (h₂ : SameNonzero y z) : SameNonzero x z := Eq.trans h₁ h₂

/-- `SameNonzero` is symmetric: rephrased as an `Iff` between the two orientations. -/
theorem comm {x : ι → ℝ} {y : κ → ℝ} : SameNonzero x y ↔ SameNonzero y x :=
  ⟨SameNonzero.symm, SameNonzero.symm⟩

/-- Reindexing one family by a bijection is a `SameNonzero`. -/
theorem comp_equiv (x : ι → ℝ) (e : κ ≃ ι) : SameNonzero (x ∘ e) x :=
  nonzeroEntries_comp_equiv x e

/-- Two families related by `y (e i) = x i` for a bijection `e : ι ≃ κ` have identical non-zero
entries. -/
theorem of_equiv {x : ι → ℝ} {y : κ → ℝ} (e : ι ≃ κ) (h : ∀ i, y (e i) = x i) :
    SameNonzero x y := by
  have hx : x = y ∘ e := funext fun i => (h i).symm
  rw [hx]
  exact comp_equiv y e

/-- **Equal full multisets ⟹ identical non-zero entries.** If the (whole) multisets of values of
`x` and `y` agree, then in particular so do their non-zero entries. The multiset-level bridge
feeding spectral applications: a self-adjoint operator's eigenvalues, read off any two eigenbases,
agree as multisets (`LinearMap.IsSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis`), so the two
eigenvalue families are `SameNonzero`. -/
theorem of_multiset_map_eq {x : ι → ℝ} {y : κ → ℝ}
    (h : Finset.univ.val.map x = Finset.univ.val.map y) : SameNonzero x y := by
  change nonzeroEntries x = nonzeroEntries y
  unfold nonzeroEntries
  rw [h]

/-- Identical non-zero entries force equal total sums (summing over the two index types). -/
theorem sum_eq {x : ι → ℝ} {y : κ → ℝ} (h : SameNonzero x y) : ∑ i, x i = ∑ j, y j := by
  rw [← sum_nonzeroEntries x, ← sum_nonzeroEntries y, h]

/-- **Nowhere-zero families with the same non-zero entries are reindexings of each other.** If
`x : ι → ℝ` and `y : κ → ℝ` are both entrywise non-zero (`∀ i, x i ≠ 0`, `∀ j, y j ≠ 0`) and have
identical non-zero entries (`SameNonzero x y`), then there is a bijection `e : ι ≃ κ` of the index
types with `y (e i) = x i` for every `i`. In this case `≅` collapses to a genuine permutation: with
no zeros to insert or delete, the two families differ only by a relabelling of the indices.

This is the tool the reverse direction of Nielsen & Chuang Exercise 12.22's Schmidt bridge needs:
two pure states with the same reduced spectrum have squared-Schmidt-coefficient families that are
`≅`, and — the coefficients being strictly positive — this promotes to a common *ordered* family,
witnessing `SameSchmidtCoeffs`. Proof: entrywise non-zero collapses each `nonzeroEntries` to the
full image multiset (`nonzeroEntries_eq_map_of_forall_ne_zero`), so `SameNonzero x y` upgrades to
equal multisets, and `exists_equiv_of_map_univ_val_eq` extracts the value-preserving bijection. -/
theorem exists_equiv {x : ι → ℝ} {y : κ → ℝ} (hx : ∀ i, x i ≠ 0) (hy : ∀ j, y j ≠ 0)
    (h : SameNonzero x y) : ∃ e : ι ≃ κ, ∀ i, y (e i) = x i := by
  refine exists_equiv_of_map_univ_val_eq ?_
  rw [← nonzeroEntries_eq_map_of_forall_ne_zero hx, ← nonzeroEntries_eq_map_of_forall_ne_zero hy]
  exact h

end SameNonzero

/-- **Truncating a family beyond its support leaves the non-zero entries unchanged.** For a family
`w : ℕ → ℝ` that vanishes from index `k` onward (`∀ n, k ≤ n → w n = 0`), the non-zero entries of
its restriction to the first `m` indices (`m ≥ k`) coincide with those of its restriction to the
first `k`: `nonzeroEntries (fun i : Fin m => w i) = nonzeroEntries (fun i : Fin k => w i)`. The
adjoined `Fin (m - k)` block contributes only zeros. Proof: split `Fin m ≃ Fin k ⊕ Fin (m - k)`
(`finSumFinEquiv`), under which `w` restricts to `Sum.elim (w|_{Fin k}) 0`, and the padded zeros
drop out (`nonzeroEntries_sum_elim_zero`). -/
theorem nonzeroEntries_fin_val_eq_of_forall_ge {w : ℕ → ℝ} {m k : ℕ} (hk : k ≤ m)
    (h : ∀ n, k ≤ n → w n = 0) :
    nonzeroEntries (fun i : Fin m => w ↑i) = nonzeroEntries (fun i : Fin k => w ↑i) := by
  set e : Fin k ⊕ Fin (m - k) ≃ Fin m := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))
  have hcomp : (fun i : Fin m => w ↑i) ∘ e
      = Sum.elim (fun j : Fin k => w ↑j) (fun _ : Fin (m - k) => (0 : ℝ)) := by
    funext x
    cases x with
    | inl j => simp [e, finSumFinEquiv, Fin.castAdd]
    | inr j =>
      simp only [e, Function.comp_apply, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
        finSumFinEquiv_apply_right, Fin.val_natAdd, Sum.elim_inr]
      exact h (k + ↑j) (Nat.le_add_right k ↑j)
  rw [← nonzeroEntries_comp_equiv (fun i : Fin m => w ↑i) e, hcomp, nonzeroEntries_sum_elim_zero]

/-- **Two truncations of a common family, past its support, have identical non-zero entries.** If
`w : ℕ → ℝ` vanishes from index `k` onward, then its restrictions to the first `m` and first `m'`
indices (both `≥ k`) are `SameNonzero`: `(fun i : Fin m => w i) ≅ (fun i : Fin m' => w i)`. This is
the heterogeneous-index bridge behind comparing two spectra read off eigenbases over different
dimensions (e.g. the two reduced factors of a rectangular operator): both are `w` composed with the
inclusion of a `Fin`-range covering `w`'s support, so their non-zero multisets coincide. -/
theorem sameNonzero_fin_val {w : ℕ → ℝ} {m m' k : ℕ} (hm : k ≤ m) (hm' : k ≤ m')
    (h : ∀ n, k ≤ n → w n = 0) :
    SameNonzero (fun i : Fin m => w ↑i) (fun i : Fin m' => w ↑i) :=
  (nonzeroEntries_fin_val_eq_of_forall_ge hm h).trans
    (nonzeroEntries_fin_val_eq_of_forall_ge hm' h).symm
