/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.GroupTheory.SpecificGroups.Cyclic.OrderValuation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The max-atom product bound for `2`-adic order valuations across a product of cyclic groups

Building on `ToMathlib.GroupTheory.SpecificGroups.Cyclic.OrderValuation` (Nielsen & Chuang's
*Lemma A4.12*: in a finite cyclic group of even order, each single `2`-adic order-valuation level
holds *at most half* the elements), this file proves the combinatorial fan-out over a finite family
of such groups that is the second ingredient of Nielsen & Chuang's factoring analysis
(the `1 - 1/2^{m-1}` bound of *Theorem 5.3* / *Theorem A4.13*).

## Main result

* `IsCyclic.two_pow_mul_card_forall_padicValNat_orderOf_eq_le` : for a nonempty finite index type
  `ι` (`m := #ι`) and finite cyclic groups `G i` each of even order, the tuples `f` whose components
  *all share one common* `2`-adic order-valuation number are rare:
  `2 ^ (m - 1) * #{f | ∀ i j, v₂(orderOf (f i)) = v₂(orderOf (f j))} ≤ ∏ i, |G i|`,
  i.e. their fraction is at most `1 / 2^{m-1}`.

## Implementation notes

The "all components share one valuation" set is the disjoint union, over the possible common value
`t`, of the boxes `{f | ∀ i, v₂(orderOf (f i)) = t}`, whose cardinality factors as a product
`∏ i, #{x : G i | v₂(orderOf x) = t}` (`Fintype.card_piFinset`).  Pinning one distinguished index
`i₀`, each of the remaining `m - 1` factors contributes at most half its group (Lemma A4.12), so the
per-`t` box is at most `(∏_{i ≠ i₀} |G i|) · #{x : G i₀ | v₂ = t} / 2^{m-1}`; summing the pinned
factor over `t` rebuilds `|G i₀|`, giving `∏ i, |G i|` on the right.  The valuation `t` is bounded
by `v₂(|G i₀|)` (every order divides the group order), making the fiber index set finite.
-/

@[expose] public section

open Finset

namespace IsCyclic

/-- **Max-atom product bound.** Let `ι` be a nonempty finite index type with `m := #ι` and let each
`G i` be a finite cyclic group of even order.  Then the tuples all of whose components have the same
`2`-adic order-valuation number occupy at most a `1 / 2^{m-1}` fraction of the product:
`2 ^ (m - 1) * #{f | ∀ i j, v₂(orderOf (f i)) = v₂(orderOf (f j))} ≤ ∏ i, |G i|`.

This is the family generalisation of `IsCyclic.two_mul_card_padicValNat_orderOf_le` (the `m = 1`,
single-group "at most half" statement) and the counting core of Nielsen & Chuang's *Theorem 5.3*. -/
theorem two_pow_mul_card_forall_padicValNat_orderOf_eq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, IsCyclic (G i)] [∀ i, Fintype (G i)]
    (hev : ∀ i, 2 ∣ Fintype.card (G i)) :
    2 ^ (Fintype.card ι - 1) *
        #{f : (i : ι) → G i |
          ∀ i j, padicValNat 2 (orderOf (f i)) = padicValNat 2 (orderOf (f j))}
      ≤ ∏ i, Fintype.card (G i) := by
  classical
  obtain ⟨i₀⟩ : Nonempty ι := inferInstance
  -- Number of elements of `G i` whose order has `2`-adic valuation exactly `t`.
  set c : ι → ℕ → ℕ := fun i t => #{x : G i | padicValNat 2 (orderOf x) = t} with hc
  -- Lemma A4.12: each level occupies at most half of its factor.
  have hbound : ∀ i t, 2 * c i t ≤ Fintype.card (G i) := fun i t =>
    IsCyclic.two_mul_card_padicValNat_orderOf_le (hev i) t
  -- The common valuation is bounded by `v₂(|G i₀|)`, so the fiber index runs over `range (d₀ + 1)`.
  set d₀ : ℕ := padicValNat 2 (Fintype.card (G i₀)) with hd0
  have hi0card : Fintype.card (G i₀) ≠ 0 := Fintype.card_ne_zero
  have hval_le : ∀ x : G i₀, padicValNat 2 (orderOf x) ≤ d₀ := fun x =>
    (Nat.pow_dvd_iff_le_padicValNat' (by norm_num) hi0card).mp
      (dvd_trans Nat.pow_padicValNat_dvd' orderOf_dvd_card)
  -- The "all-equal" set.
  set A : Finset ((i : ι) → G i) :=
    Finset.univ.filter (fun f : (i : ι) → G i =>
      ∀ i j, padicValNat 2 (orderOf (f i)) = padicValNat 2 (orderOf (f j)))
    with hA
  -- Each fiber of `f ↦ v₂(orderOf (f i₀))` over `A` is the box of tuples with all valuations `= t`.
  have hfiber : ∀ t, A.filter (fun f => padicValNat 2 (orderOf (f i₀)) = t)
      = Fintype.piFinset (fun i => {x : G i | padicValNat 2 (orderOf x) = t}) := by
    intro t
    ext f
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hall, ht⟩ i
      exact (hall i i₀).trans ht
    · intro h
      exact ⟨fun i j => (h i).trans (h j).symm, h i₀⟩
  -- ... hence its cardinality is the product of the per-factor level counts.
  have hAt_card : ∀ t, (A.filter (fun f => padicValNat 2 (orderOf (f i₀)) = t)).card
      = ∏ i, c i t := by
    intro t
    rw [hfiber t, Fintype.card_piFinset]
  -- Decompose `#A` as the sum over the common valuation `t`.
  have hmaps : Set.MapsTo (fun f : (i : ι) → G i => padicValNat 2 (orderOf (f i₀)))
      ↑A ↑(Finset.range (d₀ + 1)) := by
    intro f _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (hval_le (f i₀))
  have hAcard : A.card = ∑ t ∈ Finset.range (d₀ + 1), ∏ i, c i t := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_congr rfl (fun t _ => hAt_card t)
  -- Summing the pinned factor over `t` rebuilds `|G i₀|`.
  have hsumci0 : ∑ t ∈ Finset.range (d₀ + 1), c i₀ t = Fintype.card (G i₀) := by
    rw [← Finset.card_univ (α := G i₀)]
    refine (Finset.card_eq_sum_card_fiberwise (fun x _ => ?_)).symm
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (hval_le x)
  -- Per-`t` bound: pull `m - 1` factors, each at most half, out of the product.
  have key : ∀ t, 2 ^ (Fintype.card ι - 1) * ∏ i, c i t
      ≤ (∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i)) * c i₀ t := by
    intro t
    have hcardE : (Finset.univ.erase i₀).card = Fintype.card ι - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
    have hprodE : 2 ^ (Fintype.card ι - 1) * ∏ i ∈ Finset.univ.erase i₀, c i t
        ≤ ∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i) := by
      calc 2 ^ (Fintype.card ι - 1) * ∏ i ∈ Finset.univ.erase i₀, c i t
          = ∏ i ∈ Finset.univ.erase i₀, (2 * c i t) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, hcardE]
        _ ≤ ∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i) :=
            Finset.prod_le_prod (fun i _ => hbound i t)
    calc 2 ^ (Fintype.card ι - 1) * ∏ i, c i t
        = 2 ^ (Fintype.card ι - 1) * (c i₀ t * ∏ i ∈ Finset.univ.erase i₀, c i t) := by
          rw [Finset.mul_prod_erase Finset.univ (fun i => c i t) (Finset.mem_univ i₀)]
      _ = c i₀ t * (2 ^ (Fintype.card ι - 1) * ∏ i ∈ Finset.univ.erase i₀, c i t) := by ring
      _ ≤ c i₀ t * ∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i) :=
          Nat.mul_le_mul_left _ hprodE
      _ = (∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i)) * c i₀ t := by rw [mul_comm]
  -- Assemble.
  calc 2 ^ (Fintype.card ι - 1) * A.card
      = 2 ^ (Fintype.card ι - 1) * ∑ t ∈ Finset.range (d₀ + 1), ∏ i, c i t := by rw [hAcard]
    _ = ∑ t ∈ Finset.range (d₀ + 1), 2 ^ (Fintype.card ι - 1) * ∏ i, c i t := by
        rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range (d₀ + 1),
          (∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i)) * c i₀ t :=
        Finset.sum_le_sum (fun t _ => key t)
    _ = (∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i)) *
          ∑ t ∈ Finset.range (d₀ + 1), c i₀ t := by rw [Finset.mul_sum]
    _ = (∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i)) * Fintype.card (G i₀) := by rw [hsumci0]
    _ = Fintype.card (G i₀) * ∏ i ∈ Finset.univ.erase i₀, Fintype.card (G i) := by rw [mul_comm]
    _ = ∏ i, Fintype.card (G i) :=
        Finset.mul_prod_erase Finset.univ (fun i => Fintype.card (G i)) (Finset.mem_univ i₀)

end IsCyclic
