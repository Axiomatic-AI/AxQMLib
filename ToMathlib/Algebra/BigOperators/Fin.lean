/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Additional `Fin`-indexed big-operator lemmas

A Euclidean-decomposition reindexing lemma for products/sums over `range (m * r)`, and a
`Finset.univ`-splitting lemma for `Fin (a + b)`.
-/

public section

open Finset

variable {ι M : Type*}

namespace Finset

/-- Reindex a product over `range (m * r)` by the Euclidean decomposition `x = j + r * i` with
`i < m` and `j < r`. -/
@[to_additive sum_range_mul_reindex /-- Reindex a sum over `range (m * r)` by the Euclidean
decomposition `x = j + r * i` with `i < m` and `j < r`. -/]
theorem prod_range_mul_reindex [CommMonoid M] (m r : ℕ) (g : ℕ → M) :
    ∏ x ∈ Finset.range (m * r), g x =
      ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range r, g (j + r * i) := by
  rw [← Fin.prod_univ_eq_prod_range g (m * r),
      ← finProdFinEquiv.prod_comp (fun x : Fin (m * r) => g ↑x),
      Fintype.prod_prod_type,
      ← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Finset.range r, g (j + r * i)) m]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Fin.prod_univ_eq_prod_range (fun j => g (j + r * i.val)) r]
  rfl

end Finset

namespace Fin

/-- Multiset analogue of `Fin.sum_univ_add`: the underlying multiset of
`Finset.univ : Finset (Fin (a + b))` splits as the union of `Finset.univ`'s on `Fin a`/`Fin b`
under the `Fin.castAdd`/`Fin.natAdd` embeddings. -/
theorem univ_val_add (a b : ℕ) :
    (Finset.univ : Finset (Fin (a + b))).val =
    (Finset.univ : Finset (Fin a)).val.map (castAdd b) +
    (Finset.univ : Finset (Fin b)).val.map (natAdd a) := by
  rw [← Multiset.map_univ_val_equiv finSumFinEquiv, ← Finset.univ_disjSum_univ,
    Finset.val_disjSum, Multiset.disjSum,
    Multiset.map_add, Multiset.map_map, Multiset.map_map]
  simp [finSumFinEquiv]

end Fin
