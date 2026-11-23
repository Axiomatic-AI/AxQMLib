/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.GroupTheory.SpecificGroups.Cyclic.OrderValuation
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The "bad set" of the order-finding reduction as a shared `2`-adic order valuation

For a finite family `G i` of finite cyclic groups of even order, each equipped with a chosen
non-identity involution `neg i` (in the application, the unit `-1`), this file characterises the
tuples `f : Π i, G i` that are **bad** for the factoring-by-order-finding reduction — meaning the
order `r = orderOf f` is odd, or `f ^ (r / 2)` equals the involution `neg` — purely in terms of the
components' `2`-adic order valuations:

`(¬ Even (orderOf f) ∨ f ^ (orderOf f / 2) = neg) ↔ ∀ i j, v₂(orderOf (f i)) = v₂(orderOf (f j))`.

This is the group-theoretic heart of the second reduction step in Nielsen & Chuang's factoring
analysis (their *Theorem 5.3* / *Theorem A4.13*): combined with the counting bound
`IsCyclic.two_pow_mul_card_forall_padicValNat_orderOf_eq_le`
(`ToMathlib.GroupTheory.SpecificGroups.Cyclic.OrderValuationPi`), it bounds the fraction of bad
units.

## Main results

* `IsCyclic.not_even_orderOf_or_pow_orderOf_div_two_eq_iff` : the characterisation above.
* `IsCyclic.eq_of_sq_eq_one_of_ne_one` : a finite cyclic group of even order has a *unique*
  non-identity square root of `1` (its order-`2` element).
* `Pi.padicValNat_orderOf` : in a finite product of finite groups, `vₚ(orderOf x)` is the supremum
  over the factors of `vₚ(orderOf (x i))`.
* `padicValNat_finset_lcm` / `padicValNat_lcm` : `vₚ` of a (finite) least common multiple of nonzero
  numbers is the supremum / maximum of the `vₚ`'s.
* `Nat.not_dvd_div_two_iff_padicValNat_eq` : for `a ∣ b` with `b` even, `a ∤ b / 2` iff
  `v₂ a = v₂ b`.

## Implementation notes

The bridge from the product order to the component orders is `Pi.orderOf` (the product order is the
`Finset.lcm` of the component orders); the `2`-adic valuation of that `lcm` is the supremum of the
component valuations (`Pi.padicValNat_orderOf`), so "all components share one valuation" pins
`v₂(orderOf f)` to that common value.  Uniqueness of the non-identity involution reuses the exact
count `IsCyclic.card_pow_eq_one_of_dvd` (with `c = 2`): the solution set of `x ^ 2 = 1` has exactly
two elements, so two non-identity solutions coincide.
-/

@[expose] public section

open Finset

/-- For a prime `p` and nonzero `a`, `b`, the `p`-adic valuation of their least common multiple is
the maximum of their valuations. -/
theorem padicValNat_lcm {p : ℕ} (hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (Nat.lcm a b) = padicValNat p a ⊔ padicValNat p b := by
  rw [Nat.padicValNat_def, Nat.padicValNat_def, Nat.padicValNat_def,
    ← Nat.factorization_def (Nat.lcm a b) hp, ← Nat.factorization_def a hp,
    ← Nat.factorization_def b hp, Nat.factorization_lcm ha hb, Finsupp.sup_apply]

/-- For a prime `p`, the `p`-adic valuation of a finite least common multiple of nonzero numbers is
the supremum of the individual valuations. -/
theorem padicValNat_finset_lcm {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (s.lcm f) = s.sup fun i => padicValNat p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Nat.padicValNat_def]
  | @insert a s ha ih =>
      have hfa : f a ≠ 0 := hf a (mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (mem_insert_of_mem hi)
      have hL : s.lcm f ≠ 0 := by rw [Ne, Finset.lcm_eq_zero_iff]; simpa using hfs
      rw [Finset.lcm_insert, Finset.sup_insert,
        show GCDMonoid.lcm (f a) (s.lcm f) = Nat.lcm (f a) (s.lcm f) from rfl,
        padicValNat_lcm hp hfa hL, ih hfs]

/-- In a finite product of finite groups, the `p`-adic valuation of the order of an element is the
supremum, over the factors, of the `p`-adic valuations of the component orders. -/
theorem Pi.padicValNat_orderOf {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, Finite (G i)] {p : ℕ} (hp : p.Prime) (x : ∀ i, G i) :
    padicValNat p (orderOf x) = Finset.univ.sup fun i => padicValNat p (orderOf (x i)) := by
  rw [_root_.Pi.orderOf]
  exact padicValNat_finset_lcm hp univ (fun i => orderOf (x i)) (fun i _ => (orderOf_pos (x i)).ne')

/-- If `a ∣ b` and `b` is even, then `a` does *not* divide `b / 2` exactly when `a` and `b` have the
same `2`-adic valuation (i.e. `a` carries the full `2`-part of `b`). -/
theorem Nat.not_dvd_div_two_iff_padicValNat_eq {a b : ℕ} (hab : a ∣ b) (hb2 : 2 ∣ b) (hb0 : b ≠ 0) :
    ¬ a ∣ b / 2 ↔ padicValNat 2 a = padicValNat 2 b := by
  have hda_le : padicValNat 2 a ≤ padicValNat 2 b :=
    (Nat.pow_dvd_iff_le_padicValNat' (by norm_num) hb0).mp (dvd_trans Nat.pow_padicValNat_dvd' hab)
  have hdb1 : 1 ≤ padicValNat 2 b := Nat.padicValNat_def ▸ one_le_multiplicity_of_dvd hb0 hb2
  have hexp : 2 * 2 ^ (padicValNat 2 b - 1) = 2 ^ padicValNat 2 b := by
    rw [← pow_succ']; congr 1; omega
  have key : 2 * (2 ^ (padicValNat 2 b - 1) * ordCompl[2] b) = b := by
    rw [← mul_assoc, hexp, Nat.padicValNat_def, ← Nat.factorization_def b Nat.prime_two,
      Nat.ordProj_mul_ordCompl_eq_self]
  have hdiv : b / 2 = 2 ^ (padicValNat 2 b - 1) * ordCompl[2] b := by
    conv_lhs => rw [← key]
    rw [Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]
  rw [hdiv, Nat.dvd_pow_mul_ordCompl_iff Nat.prime_two hb0 hab]
  omega

/-- A finite cyclic group of even order has a *unique* non-identity square root of `1`: any two
elements `a`, `b` with `a ^ 2 = b ^ 2 = 1` and `a, b ≠ 1` are equal.  (The solution set of
`x ^ 2 = 1` has exactly two elements by `IsCyclic.card_pow_eq_one_of_dvd`.) -/
theorem IsCyclic.eq_of_sq_eq_one_of_ne_one {G : Type*} [Group G] [IsCyclic G] [Fintype G]
    (h2 : 2 ∣ Fintype.card G) {a b : G} (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have hS : #{x : G | x ^ 2 = 1} = 2 := IsCyclic.card_pow_eq_one_of_dvd h2 (by norm_num)
  have h1a : (1 : G) ≠ a := fun h => ha1 h.symm
  have h1b : (1 : G) ≠ b := fun h => hb1 h.symm
  have hsub : ({1, a, b} : Finset G) ⊆ ({x : G | x ^ 2 = 1} : Finset G) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact ha2
    · exact hb2
  have h3 : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h1a, h1b]),
      Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [h3, hS] at hle
  omega

/-- **The "bad set" of the factoring-by-order-finding reduction, over a product of cyclic groups.**

Let `ι` be a nonempty finite index type and let each `G i` be a finite cyclic group of even order,
equipped with a chosen non-identity involution `neg i` (`neg i ^ 2 = 1`, `neg i ≠ 1`; in the
application to `(ZMod N)ˣ`, this is the unit `-1`).  For a tuple `f : Π i, G i`, writing
`r = orderOf f`, the reduction *fails* — `r` is odd, or `f ^ (r / 2) = neg` — if and only if all
components share the same `2`-adic order valuation:

`(¬ Even r ∨ f ^ (r / 2) = neg) ↔ ∀ i j, v₂(orderOf (f i)) = v₂(orderOf (f j))`.

This is the group-theoretic core of Nielsen & Chuang's *Theorem 5.3* / *Theorem A4.13*. -/
theorem IsCyclic.not_even_orderOf_or_pow_orderOf_div_two_eq_iff
    {ι : Type*} [Finite ι] [Nonempty ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, IsCyclic (G i)] [∀ i, Fintype (G i)]
    (hev : ∀ i, 2 ∣ Fintype.card (G i))
    (neg : ∀ i, G i) (hneg2 : ∀ i, neg i ^ 2 = 1) (hneg1 : ∀ i, neg i ≠ 1) (f : ∀ i, G i) :
    (¬ Even (orderOf f) ∨ f ^ (orderOf f / 2) = neg)
      ↔ ∀ i j, padicValNat 2 (orderOf (f i)) = padicValNat 2 (orderOf (f j)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set r := orderOf f with hr
  have hr0 : r ≠ 0 := (orderOf_pos f).ne'
  have hpow : f ^ r = 1 := pow_orderOf_eq_one f
  -- Each component order divides the product order.
  have hdvd : ∀ k, orderOf (f k) ∣ r := fun k =>
    orderOf_dvd_of_pow_eq_one (by have := congrFun hpow k; simpa [Pi.pow_apply] using this)
  -- `v₂` of the product order is the supremum of the component `v₂`'s (`Pi.orderOf`).
  have hsup : padicValNat 2 r = Finset.univ.sup fun i => padicValNat 2 (orderOf (f i)) := by
    rw [hr]; exact Pi.padicValNat_orderOf Nat.prime_two f
  constructor
  · -- A bad tuple forces every component `v₂` to equal `v₂ r`, hence all are equal.
    intro hbad i j
    suffices h : ∀ k, padicValNat 2 (orderOf (f k)) = padicValNat 2 r by rw [h i, h j]
    intro k
    by_cases hE : Even r
    · -- `r` even, so `f ^ (r / 2) = neg`; component `≠ 1`, so it carries the full `2`-part of `r`.
      have hhalf : f ^ (r / 2) = neg := hbad.resolve_left (not_not.mpr hE)
      have hne : (f k) ^ (r / 2) ≠ 1 := by
        have := congrFun hhalf k
        rw [Pi.pow_apply] at this
        rw [this]; exact hneg1 k
      have hnotdvd : ¬ orderOf (f k) ∣ (r / 2) := fun hd => hne (orderOf_dvd_iff_pow_eq_one.mp hd)
      exact (Nat.not_dvd_div_two_iff_padicValNat_eq (hdvd k) hE.two_dvd hr0).mp hnotdvd
    · -- `r` odd, so `v₂ r = 0`, and each component `v₂ ≤ v₂ r = 0`.
      have hvr0 : padicValNat 2 r = 0 :=
        Nat.padicValNat_def ▸ multiplicity_eq_zero_of_not_dvd (mt even_iff_two_dvd.mpr hE)
      have hle : padicValNat 2 (orderOf (f k)) ≤ padicValNat 2 r :=
        (Nat.pow_dvd_iff_le_padicValNat' (by norm_num) hr0).mp
          (dvd_trans Nat.pow_padicValNat_dvd' (hdvd k))
      omega
  · -- Conversely, if all components share one `2`-adic valuation `d`, then `v₂ r = d`.
    intro hall
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have hconst : ∀ k, padicValNat 2 (orderOf (f k)) = padicValNat 2 (orderOf (f i₀)) :=
      fun k => hall k i₀
    have hvr : padicValNat 2 r = padicValNat 2 (orderOf (f i₀)) := by
      rw [hsup, ← Finset.sup_const (Finset.univ_nonempty (α := ι)) (padicValNat 2 (orderOf (f i₀)))]
      exact Finset.sup_congr rfl (fun k _ => hconst k)
    by_cases hd0 : padicValNat 2 r = 0
    · -- `d = 0`: `r` is odd.
      left
      intro hE
      have : 1 ≤ padicValNat 2 r := Nat.padicValNat_def ▸ one_le_multiplicity_of_dvd hr0 hE.two_dvd
      omega
    · -- `d ≥ 1`: `r` is even and each `(f k) ^ (r / 2)` is the non-identity involution `neg k`.
      right
      have h2r : 2 ∣ r :=
        dvd_of_one_le_multiplicity (Nat.padicValNat_def ▸ (by omega : 1 ≤ padicValNat 2 r))
      funext k
      rw [Pi.pow_apply]
      have hvk : padicValNat 2 (orderOf (f k)) = padicValNat 2 r := by rw [hconst k, ← hvr]
      have hnotdvd : ¬ orderOf (f k) ∣ (r / 2) :=
        (Nat.not_dvd_div_two_iff_padicValNat_eq (hdvd k) h2r hr0).mpr hvk
      have hsq : ((f k) ^ (r / 2)) ^ 2 = 1 := by
        rw [← pow_mul, Nat.div_mul_cancel h2r]
        exact orderOf_dvd_iff_pow_eq_one.mp (hdvd k)
      have hne : (f k) ^ (r / 2) ≠ 1 := fun h => hnotdvd (orderOf_dvd_iff_pow_eq_one.mpr h)
      exact IsCyclic.eq_of_sq_eq_one_of_ne_one (hev k) hsq (hneg2 k) hne (hneg1 k)
