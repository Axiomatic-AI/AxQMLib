/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.GroupTheory.SpecificGroups.Cyclic.OrderValuationPi
public import ToMathlib.GroupTheory.SpecificGroups.Cyclic.OrderValuationPiInvolution
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Algebra.Group.Pi.Units

/-!
# The order-finding reduction: most units modulo an odd `N` are good for factoring

For an odd modulus `N > 1`, this file bounds — as an exact cardinality inequality over the unit
group `(ZMod N)ˣ` — the fraction of units `x` that are **good** for the reduction of factoring to
order-finding: those whose multiplicative order `r = orderOf x` is even and satisfy
`x ^ (r / 2) ≠ -1`.  Writing `m := N.primeFactors.card` for the number of distinct prime factors,

`(2 ^ (m-1) - 1) * φ(N) ≤ 2 ^ (m-1) * #{x : (ZMod N)ˣ | Even (orderOf x) ∧ x ^ (orderOf x/2) ≠ -1}`,

i.e. at least a `1 - 1/2^{m-1}` fraction of the units are good.  This is the assembled statement of
Nielsen & Chuang's *Theorem 5.3* / *Theorem A4.13* — with the corrected bound `1 - 1/2^{m-1}`.

## The erratum

Nielsen & Chuang print the bound as `1 - 1/2^m` (their eq. (5.60) / (A4.32)).  This is an
**erratum**: the printed `1/2^m` is false — for `N = 21` (`m = 2`) exactly half the units are
bad, so the good fraction is `1/2 = 1 - 1/2^{m-1}`, not `≥ 3/4 = 1 - 1/2^m`.  N&C's own proof of
Theorem A4.13 reduces a bad unit to the event that all `m` per-prime `2`-adic order valuations
`dⱼ = v₂(rⱼ)` coincide, then bounds that event by `1/2^m` "from Lemma A4.12".  That final step is
the slip: `p(all dⱼ equal) = ∑_D ∏ⱼ p(dⱼ = D)`, and bounding `m - 1` of the factors by Lemma
A4.12's `≤ 1/2` while summing the remaining one to `1` gives `1/2^{m-1}` — the `m`-th factor of
`1/2` that the printed `1/2^m` assumes is simply not there.  The corrected and tight bound
`1 - 1/2^{m-1}` is what is proved here; the printed `1 - 1/2^m` is refuted separately via the
`N = 21` counterexample.

## Main results

* `ZMod.orderFinding_good_units_card_ge` : the corrected cardinality bound displayed above.
* `ZMod.card_good_units_twentyOne` : for `N = 21` exactly `6` of the `12` units are good — the
  witness that the corrected bound `1 - 1/2^{m-1}` is *tight* (here `6/12 = 1/2 = 1 - 1/2^{m-1}`).
* `ZMod.not_orderFinding_good_units_printed_bound` : the refutation — the printed bound `1 - 1/2^m`
  fails, since at `N = 21` it would demand at least `9` good units while there are only `6`.

## Implementation notes

The proof transports the abstract product-of-cyclic-groups machinery to `(ZMod N)ˣ` through the
Chinese remainder theorem.  For odd `N > 1`, `ZMod.equivPi` gives a ring isomorphism
`ZMod N ≃+* Π p ∈ N.primeFactors, ZMod (p ^ α_p)` (with `α_p = N.factorization p`); passing to
units (`Units.mapEquiv`) and distributing units over the product (`MulEquiv.piUnits`) yields a
multiplicative equivalence `e : (ZMod N)ˣ ≃* Π p, (ZMod (p ^ α_p))ˣ`.  Each factor is a finite
cyclic group (`ZMod.isCyclic_units_of_prime_pow`, valid since every `p` is an odd prime) of even
order (`Nat.totient_even`).  Because `e` is multiplicative it preserves `orderOf`
(`orderOf_injective`) and, being induced by a ring isomorphism, carries the unit `-1` to the tuple
of `-1`'s; hence a unit is bad iff its image is bad in the product.  The bad tuples are then
characterised (`IsCyclic.not_even_orderOf_or_pow_orderOf_div_two_eq_iff`) as those whose components
share one `2`-adic order valuation, and counted
(`IsCyclic.two_pow_mul_card_forall_padicValNat_orderOf_eq_le`).  The product of the factor
cardinalities equals `φ(N)` (`Fintype.card_pi` through `e`), and complementation turns the
bad-count bound into the good-count bound.
-/

@[expose] public section

open Finset

namespace ZMod

/-- **Corrected Nielsen & Chuang Theorem 5.3 (= Theorem A4.13), as a cardinality bound.**

Let `N` be odd with `N > 1` and `m := N.primeFactors.card` its number of distinct prime factors.
The units `x` of `ZMod N` that are *good* for the order-finding reduction — those with `orderOf x`
even and `x ^ (orderOf x / 2) ≠ -1` — make up at least a `1 - 1/2^{m-1}` fraction of `(ZMod N)ˣ`:

`(2 ^ (m - 1) - 1) * φ(N) ≤ 2 ^ (m - 1) * #{good units}`.

Interpreting the uniform choice of a random unit, the probability of drawing a good unit is
`#{good}/φ(N) ≥ 1 - 1/2^{m-1}`.  (Nielsen & Chuang print `1 - 1/2^m`; that bound is an erratum,
false already at `N = 21`.) -/
theorem orderFinding_good_units_card_ge {N : ℕ} [NeZero N] (hN : Odd N) (hN1 : 1 < N) :
    (2 ^ (N.primeFactors.card - 1) - 1) * N.totient ≤
      2 ^ (N.primeFactors.card - 1) *
        #{x : (ZMod N)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1} := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  -- Per-prime arithmetic facts: each `p ∈ N.primeFactors` is an odd prime with `α_p ≥ 1`.
  have hp : ∀ p : N.primeFactors, Nat.Prime (p : ℕ) := fun p =>
    Nat.prime_of_mem_primeFactors p.2
  have hdvd : ∀ p : N.primeFactors, (p : ℕ) ∣ N := fun p => Nat.dvd_of_mem_primeFactors p.2
  have hp2 : ∀ p : N.primeFactors, (p : ℕ) ≠ 2 := by
    intro p h
    have hd := hdvd p
    rw [h] at hd
    rw [Nat.odd_iff] at hN
    omega
  have hα : ∀ p : N.primeFactors, 1 ≤ N.factorization (p : ℕ) := by
    intro p
    rw [← Nat.Prime.pow_dvd_iff_le_factorization (hp p) hN0]
    simpa using hdvd p
  have h2lt : ∀ p : N.primeFactors, 2 < (p : ℕ) ^ N.factorization (p : ℕ) := by
    intro p
    have hp3 : 3 ≤ (p : ℕ) := by have := (hp p).two_le; have := hp2 p; omega
    calc 2 < 3 := by norm_num
      _ ≤ (p : ℕ) := hp3
      _ ≤ (p : ℕ) ^ N.factorization (p : ℕ) := Nat.le_self_pow (by have := hα p; omega) _
  -- Factor-group instances: finite, cyclic, of even order.
  have hNZfac : ∀ p : N.primeFactors, NeZero ((p : ℕ) ^ N.factorization (p : ℕ)) := fun p =>
    ⟨pow_ne_zero _ (hp p).ne_zero⟩
  have hFin : ∀ p : N.primeFactors, Fintype (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ :=
    fun p => inferInstance
  have hCyc : ∀ p : N.primeFactors, IsCyclic (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ :=
    fun p => ZMod.isCyclic_units_of_prime_pow (p : ℕ) (hp p) (hp2 p) _
  have : Nonempty N.primeFactors :=
    Finset.nonempty_coe_sort.mpr (Nat.nonempty_primeFactors.mpr hN1)
  have hev : ∀ p : N.primeFactors,
      2 ∣ Fintype.card (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ := by
    intro p
    rw [ZMod.card_units_eq_totient]
    exact (Nat.totient_even (h2lt p)).two_dvd
  -- `-1` is a nontrivial involution in each factor.
  set neg : (p : N.primeFactors) → (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ :=
    fun p => (-1 : (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ) with hnegdef
  have hneg2 : ∀ p, neg p ^ 2 = 1 := fun p => by rw [hnegdef, neg_one_sq]
  have hneg1 : ∀ p, neg p ≠ 1 := by
    intro p h
    have : Fact (2 < (p : ℕ) ^ N.factorization (p : ℕ)) := ⟨h2lt p⟩
    exact ZMod.neg_one_ne_one (n := (p : ℕ) ^ N.factorization (p : ℕ)) (congrArg Units.val h)
  -- The CRT multiplicative equivalence `(ZMod N)ˣ ≃* Π p, (ZMod (p ^ α_p))ˣ`.
  set F : ZMod N ≃+* ((p : N.primeFactors) → ZMod ((p : ℕ) ^ N.factorization (p : ℕ))) :=
    ZMod.equivPi N hN0 with hF
  set e : (ZMod N)ˣ ≃*
      ((p : N.primeFactors) → (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ) :=
    (Units.mapEquiv F.toMulEquiv).trans MulEquiv.piUnits with he
  -- The underlying map of `e`, componentwise, is `F` on the underlying ring element.
  have he_val : ∀ (u : (ZMod N)ˣ) (p : N.primeFactors),
      ((e u p : (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ) :
          ZMod ((p : ℕ) ^ N.factorization (p : ℕ))) = F (u : ZMod N) p := by
    intro u p
    rw [he]
    simp only [MulEquiv.trans_apply, MulEquiv.val_piUnits_apply, Units.coe_mapEquiv,
      RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv]
  -- `e` carries `-1` to the tuple of `-1`'s (it comes from a ring isomorphism).
  have he_neg : e (-1) = neg := by
    funext p
    apply Units.ext
    rw [he_val, hnegdef]
    push_cast
    rw [map_neg, map_one]
    rfl
  -- `e` preserves `orderOf`.
  have hord : ∀ x : (ZMod N)ˣ, orderOf (e x) = orderOf x := fun x =>
    orderOf_injective e.toMonoidHom e.injective x
  -- A unit is bad iff its image in the product is bad.
  have hbad_iff : ∀ x : (ZMod N)ˣ,
      (¬ Even (orderOf x) ∨ x ^ (orderOf x / 2) = -1)
        ↔ (¬ Even (orderOf (e x)) ∨ (e x) ^ (orderOf (e x) / 2) = neg) := by
    intro x
    rw [hord x]
    have hpow : (e x) ^ (orderOf x / 2) = e (x ^ (orderOf x / 2)) := (map_pow e x _).symm
    have hdisj2 : (e x) ^ (orderOf x / 2) = neg ↔ x ^ (orderOf x / 2) = -1 := by
      rw [hpow, ← he_neg]; exact e.apply_eq_iff_eq
    exact or_congr Iff.rfl hdisj2.symm
  -- Count transport: bad units of `(ZMod N)ˣ` ↔ tuples sharing one `2`-adic order valuation.
  have hbad_card :
      #{x : (ZMod N)ˣ | ¬ Even (orderOf x) ∨ x ^ (orderOf x / 2) = -1} =
        #{f : (p : N.primeFactors) → (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ |
          ∀ i j, padicValNat 2 (orderOf (f i)) = padicValNat 2 (orderOf (f j))} := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
    exact (hbad_iff x).trans
      (IsCyclic.not_even_orderOf_or_pow_orderOf_div_two_eq_iff hev neg hneg2 hneg1 (e x))
  -- Counting bound (Lemma A4.12 fan-out) with the factor-cardinality product equal to `φ(N)`.
  have hPR2 := IsCyclic.two_pow_mul_card_forall_padicValNat_orderOf_eq_le
    (ι := N.primeFactors) (G := fun p => (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ) hev
  rw [Fintype.card_coe] at hPR2
  have hprodT :
      ∏ p : N.primeFactors, Fintype.card (ZMod ((p : ℕ) ^ N.factorization (p : ℕ)))ˣ
        = N.totient := by
    rw [← Fintype.card_pi, Fintype.card_congr e.symm.toEquiv, ZMod.card_units_eq_totient]
  rw [hprodT] at hPR2
  -- The bad-count bound: `2^(m-1) * #bad ≤ φ(N)`.
  have hBound : 2 ^ (N.primeFactors.card - 1) *
      #{x : (ZMod N)ˣ | ¬ Even (orderOf x) ∨ x ^ (orderOf x / 2) = -1} ≤ N.totient := by
    rw [hbad_card]; exact hPR2
  -- Good and bad units partition `(ZMod N)ˣ`.
  have hApart :
      #{x : (ZMod N)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1} +
        #{x : (ZMod N)ˣ | ¬ Even (orderOf x) ∨ x ^ (orderOf x / 2) = -1} = N.totient := by
    have hfilter :
        Finset.univ.filter
            (fun x : (ZMod N)ˣ => ¬ Even (orderOf x) ∨ x ^ (orderOf x / 2) = -1) =
          Finset.univ.filter (fun x => ¬ (Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1)) :=
      Finset.filter_congr fun x _ => by tauto
    rw [hfilter, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      ZMod.card_units_eq_totient]
  -- Final arithmetic: complement the bad-count bound.
  set c := 2 ^ (N.primeFactors.card - 1) with hc
  have hc1 : 1 ≤ c := Nat.one_le_two_pow
  have e1 : (c - 1) * N.totient + N.totient = c * N.totient := by
    conv_rhs => rw [← Nat.sub_add_cancel hc1]
    rw [add_mul, one_mul]
  have e2 : c * #{x : (ZMod N)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1} +
      c * #{x : (ZMod N)ˣ | ¬ Even (orderOf x) ∨ x ^ (orderOf x / 2) = -1} = c * N.totient := by
    rw [← Nat.mul_add, hApart]
  omega

/-!
### The erratum: refuting the printed bound `1 - 1/2^m`

Nielsen & Chuang state the bound as `1 - 1/2^m` (eq. (5.60) / (A4.32)); the corrected and tight
bound proved above is `1 - 1/2^{m-1}`.  We now certify that the printed bound is genuinely false,
via the smallest counterexample `N = 21 = 3 · 7`.  There `m = 2`, `φ(21) = 12`, and exactly `6`
units are good — so the good fraction is `1/2`, not the `≥ 3/4` the printed bound would require.

The multiplicative order over `(ZMod 21)ˣ` is `noncomputable`, so the good units cannot be counted
by `decide` directly.  The group has exponent `6` (every unit satisfies `x ^ 6 = 1`), so on it the
order is recovered by the computable surrogate `ordAux21` below; rewriting `orderOf` to `ordAux21`
makes the good-unit predicate decidable, and the count is then evaluated by `decide`.
-/

/-- A computable stand-in for `orderOf` on `(ZMod 21)ˣ`, which has exponent `6`: it returns the
least divisor of `6` annihilating `x`.  On this group it agrees with `orderOf`
(`orderOf_eq_ordAux21`), which lets the otherwise-`noncomputable` good-unit count be decided. -/
private def ordAux21 (x : (ZMod 21)ˣ) : ℕ :=
  if x = 1 then 1 else if x ^ 2 = 1 then 2 else if x ^ 3 = 1 then 3 else 6

/-- On `(ZMod 21)ˣ` (a group of exponent `6`) the computable surrogate `ordAux21` agrees with the
genuine multiplicative order `orderOf`.  Proved for any `x` with `x ^ 6 = 1`. -/
private theorem orderOf_eq_ordAux21 (x : (ZMod 21)ˣ) (hx6 : x ^ 6 = 1) :
    orderOf x = ordAux21 x := by
  have hdvd : orderOf x ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hx6
  have hpos : 0 < orderOf x := orderOf_pos x
  have hle : orderOf x ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  unfold ordAux21
  split_ifs with h1 h2 h3
  · subst h1; simp
  · have hn1 : orderOf x ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ (orderOf_dvd_iff_pow_eq_one.mpr h2) with h | h
    · exact absurd h hn1
    · exact h
  · have hn1 : orderOf x ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_iff_pow_eq_one.mpr h3) with h | h
    · exact absurd h hn1
    · exact h
  · have hn1 : orderOf x ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
    have hn2 : orderOf x ≠ 2 := fun h => h2 (by rw [← h]; exact pow_orderOf_eq_one x)
    have hn3 : orderOf x ≠ 3 := fun h => h3 (by rw [← h]; exact pow_orderOf_eq_one x)
    have hn4 : orderOf x ≠ 4 := fun h => by rw [h] at hdvd; norm_num at hdvd
    have hn5 : orderOf x ≠ 5 := fun h => by rw [h] at hdvd; norm_num at hdvd
    omega

set_option maxHeartbeats 400000 in
-- The `decide` calls below enumerate the 12-element unit group `(ZMod 21)ˣ`, which exceeds the
-- default heartbeat budget.
/-- **Tightness of the corrected bound at `N = 21`.** Exactly `6` of the `12` units of `ZMod 21`
are good for the order-finding reduction (order even and `x ^ (orderOf x / 2) ≠ -1`).  Since
`6 / 12 = 1/2 = 1 - 1/2^{m-1}` with `m = 2`, the corrected bound of
`ZMod.orderFinding_good_units_card_ge` is attained — and, a fortiori, the printed bound
`1 - 1/2^m = 3/4` is violated. -/
theorem card_good_units_twentyOne :
    #{x : (ZMod 21)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1} = 6 := by
  have h6 : ∀ x : (ZMod 21)ˣ, x ^ 6 = 1 := by decide
  have key : #{x : (ZMod 21)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1}
           = #{x : (ZMod 21)ˣ | Even (ordAux21 x) ∧ x ^ (ordAux21 x / 2) ≠ -1} := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro x _
    rw [orderOf_eq_ordAux21 x (h6 x)]
  rw [key]; decide

/-- **Nielsen & Chuang's Theorem 5.3 is false as printed.** The book states the good-unit fraction
is `≥ 1 - 1/2^m` (their eq. (5.60) / (A4.32)), which as a cardinality bound reads
`(2^m - 1) * φ(N) ≤ 2^m * #{good units}` for every odd `N > 1` with `m` distinct prime factors.
This universal statement is refuted by `N = 21`: there `m = 2`, `φ(21) = 12`, and there are only
`6` good units (`card_good_units_twentyOne`), whereas the printed bound would force at least `9`.
The corrected bound `1 - 1/2^{m-1}` (`ZMod.orderFinding_good_units_card_ge`) holds and is tight. -/
theorem not_orderFinding_good_units_printed_bound :
    ¬ ∀ (N : ℕ) [NeZero N], Odd N → 1 < N →
      (2 ^ N.primeFactors.card - 1) * N.totient ≤
        2 ^ N.primeFactors.card *
          #{x : (ZMod N)ˣ | Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1} := by
  intro h
  have h21 := h 21 (by decide) (by norm_num)
  have htot : (21 : ℕ).totient = 12 := by decide
  have hm : 2 ≤ (21 : ℕ).primeFactors.card := by
    have h3 : (3 : ℕ) ∈ (21 : ℕ).primeFactors := by
      rw [Nat.mem_primeFactors]; exact ⟨by decide, by norm_num, by norm_num⟩
    have h7 : (7 : ℕ) ∈ (21 : ℕ).primeFactors := by
      rw [Nat.mem_primeFactors]; exact ⟨by decide, by norm_num, by norm_num⟩
    have hsub : ({3, 7} : Finset ℕ) ⊆ (21 : ℕ).primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h3
      · exact h7
    calc (2 : ℕ) = ({3, 7} : Finset ℕ).card := by decide
      _ ≤ _ := Finset.card_le_card hsub
  rw [card_good_units_twentyOne, htot] at h21
  have hk : 4 ≤ 2 ^ (21 : ℕ).primeFactors.card :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (21 : ℕ).primeFactors.card := Nat.pow_le_pow_right (by norm_num) hm
  omega

end ZMod
