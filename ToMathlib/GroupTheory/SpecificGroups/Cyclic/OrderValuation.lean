/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Counting elements of a finite cyclic group by the `2`-adic valuation of their order

In a finite cyclic group `G` the number of elements of each order is controlled by Euler's
totient function (`IsCyclic.card_orderOf_eq_totient`).  This file draws two counting consequences
that are the combinatorial heart of the analysis of Shor's factoring algorithm (Nielsen & Chuang,
*Lemma A4.12*): for the fixed prime `2`, how the elements of `G` distribute across the possible
`2`-adic valuations of their orders.

Throughout, write `n = |G|` and `d = v₂(n)` (`padicValNat 2 n`).

## Main results

* `IsCyclic.card_pow_eq_one_of_dvd` : `#{x | xᶜ = 1} = c` for any divisor `c` of `n`.  (The `≤`
  bound in an arbitrary finite group is `IsCyclic.card_pow_eq_one_le`; here we get the exact count.)
* `IsCyclic.card_orderOf_dvd_of_dvd` : `#{x | orderOf x ∣ c} = c` for any divisor `c` of `n`.
* `IsCyclic.card_padicValNat_orderOf_le` : for a prime `p` and `t ≤ vₚ(n)`, the number of elements
  whose order has `p`-adic valuation `≤ t` is `pᵗ` times the `p`-free part of `n`.
* `IsCyclic.two_mul_card_two_pow_dvd_orderOf` : if `n` is even then **exactly half** the elements
  have order divisible by the full `2`-part `2ᵈ` of `n`, i.e. `2 · #{x | 2ᵈ ∣ orderOf x} = n`.
  This is Nielsen & Chuang's *Lemma A4.12*.
* `IsCyclic.two_mul_card_padicValNat_orderOf_le` : if `n` is even then **at most half** the
  elements share any single value `t` of `v₂(orderOf x)`, i.e. `2 · #{x | v₂(orderOf x) = t} ≤ n`.

## Implementation notes

The supporting arithmetic fact `Nat.dvd_pow_mul_ordCompl_iff` — a divisor `a` of `n` divides
`pᵗ · (p`-free part of `n)` iff `vₚ(a) ≤ t` — turns the divisibility set
`{x | orderOf x ∣ pᵗ · ordComplₚ n}` (counted exactly by `card_orderOf_dvd_of_dvd`) into the
valuation set `{x | vₚ(orderOf x) ≤ t}`.  Both of these are stated for a general prime `p`, since
their proofs are not `2`-specific; only the two "half" results are genuinely about `p = 2`.  The
"at most half" bound then follows because the top level `t = d` already occupies exactly half of
`G`, so every other level is disjoint from it and hence fits in the remaining half.
-/

@[expose] public section

open Finset

namespace Nat

/-- `Nat.pow_dvd_iff_le_multiplicity`, stated with `padicValNat`. -/
theorem pow_dvd_iff_le_padicValNat' {p k n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ padicValNat p n := by
  rw [padicValNat_def]
  exact pow_dvd_iff_le_multiplicity hp hn

/-- `pow_multiplicity_dvd`, stated with `padicValNat`. -/
theorem pow_padicValNat_dvd' {p n : ℕ} : p ^ padicValNat p n ∣ n := by
  rw [padicValNat_def]
  exact pow_multiplicity_dvd p n

/-- For a prime `p` and a divisor `a` of a nonzero `n`, `a` divides `p ^ t` times the `p`-free part
of `n` (that is, `p ^ t * ordCompl[p] n`) exactly when the `p`-adic valuation of `a` is at most
`t`. -/
theorem dvd_pow_mul_ordCompl_iff {p n a t : ℕ} (hp : p.Prime) (hn : n ≠ 0) (ha : a ∣ n) :
    a ∣ p ^ t * ordCompl[p] n ↔ padicValNat p a ≤ t := by
  have hfac : a.factorization p = padicValNat p a := by
    rw [Nat.factorization_def a hp, padicValNat_def]
  constructor
  · intro h
    have hdvd : p ^ padicValNat p a ∣ p ^ t * ordCompl[p] n :=
      dvd_trans (by rw [← hfac]; exact Nat.ordProj_dvd a p) h
    have hcop : Nat.Coprime (p ^ padicValNat p a) (ordCompl[p] n) :=
      (Nat.coprime_ordCompl hp hn).pow_left _
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hcop.dvd_of_dvd_mul_right hdvd)
  · intro h
    have hsplit : a = p ^ padicValNat p a * ordCompl[p] a := by
      rw [← hfac]; exact (Nat.ordProj_mul_ordCompl_eq_self a p).symm
    rw [hsplit]
    exact Nat.mul_dvd_mul (pow_dvd_pow p h) (Nat.ordCompl_dvd_ordCompl_of_dvd ha p)

end Nat

namespace IsCyclic

/-- In a finite cyclic group, the number of solutions of `x ^ c = 1` is exactly `c`, for any
divisor `c` of the group order.  (Compare `IsCyclic.card_pow_eq_one_le`, the `≤` bound available in
an arbitrary finite group.) -/
theorem card_pow_eq_one_of_dvd {G : Type*} [Group G] [IsCyclic G] [Fintype G] [DecidableEq G]
    {c : ℕ} (hc : c ∣ Fintype.card G) (hc0 : c ≠ 0) : #{x : G | x ^ c = 1} = c := by
  rw [← sum_card_orderOf_eq_card_pow_eq_one hc0]
  calc ∑ m ∈ c.divisors, #{x : G | orderOf x = m}
      = ∑ m ∈ c.divisors, m.totient :=
        Finset.sum_congr rfl fun m hm =>
          IsCyclic.card_orderOf_eq_totient (dvd_trans (Nat.dvd_of_mem_divisors hm) hc)
    _ = c := Nat.sum_totient c

/-- In a finite cyclic group, the number of elements whose order divides `c` is exactly `c`, for
any divisor `c` of the group order. -/
theorem card_orderOf_dvd_of_dvd {G : Type*} [Group G] [IsCyclic G] [Fintype G]
    {c : ℕ} (hc : c ∣ Fintype.card G) (hc0 : c ≠ 0) : #{x : G | orderOf x ∣ c} = c := by
  classical
  conv_rhs => rw [← card_pow_eq_one_of_dvd hc hc0]
  congr 1
  ext x
  simp [orderOf_dvd_iff_pow_eq_one]

/-- For a prime `p`, the number of elements of a finite cyclic group whose order has `p`-adic
valuation at most `t` is `p ^ t` times the `p`-free part of the group order, provided
`t ≤ vₚ(|G|)`. -/
theorem card_padicValNat_orderOf_le {G : Type*} [Group G] [IsCyclic G] [Fintype G]
    {p t : ℕ} (hp : p.Prime) (ht : t ≤ padicValNat p (Fintype.card G)) :
    #{x : G | padicValNat p (orderOf x) ≤ t} = p ^ t * ordCompl[p] (Fintype.card G) := by
  have hn : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hfac : (Fintype.card G).factorization p = padicValNat p (Fintype.card G) :=
    (Nat.factorization_def _ hp).trans Nat.padicValNat_def.symm
  have hdvd : p ^ t * ordCompl[p] (Fintype.card G) ∣ Fintype.card G := by
    calc p ^ t * ordCompl[p] (Fintype.card G)
        ∣ p ^ (Fintype.card G).factorization p * ordCompl[p] (Fintype.card G) :=
          Nat.mul_dvd_mul (pow_dvd_pow p (by rw [hfac]; exact ht)) dvd_rfl
      _ = Fintype.card G := Nat.ordProj_mul_ordCompl_eq_self _ p
  have hne : p ^ t * ordCompl[p] (Fintype.card G) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hp.pos.ne') (Nat.ordCompl_pos p hn).ne'
  rw [← card_orderOf_dvd_of_dvd hdvd hne]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (Nat.dvd_pow_mul_ordCompl_iff hp hn orderOf_dvd_card).symm

/-- **Nielsen & Chuang, Lemma A4.12.** In a finite cyclic group of even order `n`, exactly half of
the elements have order divisible by the full `2`-part `2 ^ v₂(n)` of `n`. -/
theorem two_mul_card_two_pow_dvd_orderOf {G : Type*} [Group G] [IsCyclic G] [Fintype G]
    (hev : 2 ∣ Fintype.card G) :
    2 * #{x : G | 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x} = Fintype.card G := by
  have hn : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hfac : (Fintype.card G).factorization 2 = padicValNat 2 (Fintype.card G) :=
    (Nat.factorization_def _ Nat.prime_two).trans Nat.padicValNat_def.symm
  have hd1 : 1 ≤ padicValNat 2 (Fintype.card G) :=
    (Nat.pow_dvd_iff_le_padicValNat' (by norm_num) hn).mp (by simpa using hev)
  -- The complement of `{2ᵈ ∣ orderOf}` is the level set `{v₂(orderOf) ≤ d - 1}`.
  have hcompl_card : #{x : G | ¬ 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x}
      = 2 ^ (padicValNat 2 (Fintype.card G) - 1) * ordCompl[2] (Fintype.card G) := by
    rw [← card_padicValNat_orderOf_le Nat.prime_two (t := padicValNat 2 (Fintype.card G) - 1)
      (Nat.sub_le _ 1)]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Nat.pow_dvd_iff_le_padicValNat' (by norm_num) (orderOf_pos x).ne']
    omega
  have hsplit : #{x : G | 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x}
      + #{x : G | ¬ 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x} = Fintype.card G := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hcard_eq : Fintype.card G
      = 2 ^ padicValNat 2 (Fintype.card G) * ordCompl[2] (Fintype.card G) := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (Fintype.card G) 2]
    rw [hfac]
  have h2E : 2 ^ padicValNat 2 (Fintype.card G) * ordCompl[2] (Fintype.card G)
      = 2 * (2 ^ (padicValNat 2 (Fintype.card G) - 1) * ordCompl[2] (Fintype.card G)) := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd1]
  have hcard2 := hcard_eq.trans h2E
  omega

/-- In a finite cyclic group of even order `n`, at most half of the elements share any single
value `t` of the `2`-adic valuation of their order: `2 · #{x | v₂(orderOf x) = t} ≤ n`.  Combined
with `two_mul_card_two_pow_dvd_orderOf`, the maximum (exactly half) is attained at `t = v₂(n)`. -/
theorem two_mul_card_padicValNat_orderOf_le {G : Type*} [Group G] [IsCyclic G] [Fintype G]
    (hev : 2 ∣ Fintype.card G) (t : ℕ) :
    2 * #{x : G | padicValNat 2 (orderOf x) = t} ≤ Fintype.card G := by
  have hn : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  -- The order of any element divides `|G|`, so its valuation is at most `v₂(|G|)`.
  have hle_all : ∀ x : G, padicValNat 2 (orderOf x) ≤ padicValNat 2 (Fintype.card G) := fun x =>
    (Nat.pow_dvd_iff_le_padicValNat' (by norm_num) hn).mp
      (dvd_trans Nat.pow_padicValNat_dvd' orderOf_dvd_card)
  -- At the top level the valuation set coincides with `{2ᵈ ∣ orderOf}`.
  have htop_eq : #{x : G | padicValNat 2 (orderOf x) = padicValNat 2 (Fintype.card G)}
      = #{x : G | 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x} := by
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Nat.pow_dvd_iff_le_padicValNat' (by norm_num) (orderOf_pos x).ne']
    have := hle_all x
    omega
  have htop : 2 * #{x : G | padicValNat 2 (orderOf x) = padicValNat 2 (Fintype.card G)}
      = Fintype.card G := by rw [htop_eq]; exact two_mul_card_two_pow_dvd_orderOf hev
  by_cases h : t = padicValNat 2 (Fintype.card G)
  · rw [h]; omega
  · -- For `t ≠ d`, the level set is disjoint from the top one, hence a subset of its complement.
    have hle : #{x : G | padicValNat 2 (orderOf x) = t}
        ≤ #{x : G | ¬ 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x} := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [Nat.pow_dvd_iff_le_padicValNat' (by norm_num) (orderOf_pos x).ne']
      have := hle_all x
      omega
    have hsplit : #{x : G | 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x}
        + #{x : G | ¬ 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x} = Fintype.card G := by
      rw [← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not _
    have hA : 2 * #{x : G | 2 ^ padicValNat 2 (Fintype.card G) ∣ orderOf x} = Fintype.card G :=
      two_mul_card_two_pow_dvd_orderOf hev
    omega

end IsCyclic
