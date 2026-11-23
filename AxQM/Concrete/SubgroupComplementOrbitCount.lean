/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupSolvableMaximalCount
import Mathlib.GroupTheory.Complement
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The orbit-counting factorization of the complement count

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5 — Ettinger–Høyer–Knill piece
ii.)* The chief-series recursion `SubgroupSolvableMaximalCount.lean` reduced the maximal-subgroup
count of a finite solvable `G` to a **linear** `2·|G|`, *conditional* on the sharp per-chief-factor
complement bound `#{complements of an abelian minimal normal N in H} ≤ |H|`. That residual is the
cardinality of the 1-cocycles `|Z¹(H ⧸ N, N)| = |B¹|·|H¹|`, and it factors into two pieces of very
different character:

* an **elementary geometric factor** `|B¹| = |N : C_N(M)| ≤ |N|` — the size of the `N`-conjugation
  orbit of a single complement, bounded by `|N|` with no cohomology; and
* a **cohomological factor** `|H¹(H ⧸ N, N)|` — the number of `N`-conjugacy **classes** of
  complements, the genuine Aschbacher–Guralnick quantity.

This file discharges the geometric factor and isolates the cohomological one. `N` acts on the
complements of a normal subgroup `N` by conjugation (`complementsConjAction`; conjugation preserves
being a complement since it fixes the normal `N` and preserves cardinality and disjointness — the
`isComplement'_iff_card_mul_and_disjoint` characterisation), each orbit has size `≤ |N|`
(orbit–stabiliser), so summing over the classes gives

`#{complements of N in H} ≤ |N| · #{N-conjugacy classes of complements}`
(`card_isComplement'_le_card_mul_card_orbits`).

Consequently the per-factor bound `#{complements} ≤ |H|` follows from the strictly cohomological
`#{complement classes} ≤ |H : N|` (`card_isComplement'_le_of_card_orbits_le_index`), and feeding
this into the assembled chief-series recursion reduces the whole solvable maximal count to that
cohomological hypothesis (`card_isCoatom_le_two_mul_card_of_isSolvable_of_orbitBound`). The
remaining question is `|H¹(H ⧸ N, N)| ≤ |H : N|` — the **named** first-cohomology bound of
the Wall / Aschbacher–Guralnick theory — with the elementary geometric factor removed; the note
`Aschbacher–Guralnick` bounds `|H¹| < |N|` (giving `#{complements} < |N|²`), so whether the sharper
`≤ |H : N|` form holds is the exact cohomological question that remains.

The general orbit-counting bound `card_le_card_mul_card_orbitRel_quotient` (a finite set acted on by
a finite group has cardinality at most the group order times the number of orbits) is proved here as
a reusable lemma via an injection `X ↪ A × (X ⧸ orbitRel)`.
-/

open Subgroup MulAction Pointwise

namespace AxQM.Concrete

universe u

variable {H : Type*} [Group H]

/-- **Orbit-counting bound.** A finite set `X` acted on by a finite group `A` has cardinality at
most `|A|` times the number of orbits. The proof is the injection `X ↪ A × (X ⧸ orbitRel A X)`
sending `x` to `(a, ⟦x⟧)` where `a • (⟦x⟧).out = x` (which exists because the chosen orbit
representative lies in the orbit of `x`); `x` is recovered from the pair, so the map is
injective. -/
theorem card_le_card_mul_card_orbitRel_quotient (A X : Type*) [Group A] [MulAction A X]
    [Finite A] [Finite X] :
    Nat.card X ≤ Nat.card A * Nat.card (MulAction.orbitRel.Quotient A X) := by
  classical
  let : Setoid X := orbitRel A X
  have key : ∀ x : X, ∃ a : A, a • (Quotient.out (Quotient.mk' x)) = x := by
    intro x
    have h0 : Quotient.out (Quotient.mk' x) ≈ x := Quotient.mk_out x
    have hrel : x ∈ orbit A (Quotient.out (Quotient.mk' x)) := Setoid.symm h0
    rwa [MulAction.mem_orbit_iff] at hrel
  set f : X → A × (MulAction.orbitRel.Quotient A X) :=
    fun x => ((key x).choose, Quotient.mk' x) with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (key x).choose = (key y).choose := congrArg Prod.fst hxy
    have h2 : (Quotient.mk' x : MulAction.orbitRel.Quotient A X) = Quotient.mk' y :=
      congrArg Prod.snd hxy
    have hx := (key x).choose_spec
    have hy := (key y).choose_spec
    rw [← hx, ← hy, h1, h2]
  calc Nat.card X ≤ Nat.card (A × (MulAction.orbitRel.Quotient A X)) :=
        Nat.card_le_card_of_injective f hinj
    _ = Nat.card A * Nat.card (MulAction.orbitRel.Quotient A X) := Nat.card_prod _ _

/-- Conjugating by any element of `H` sends complements of a normal subgroup `N` to complements of
`N`: conjugation fixes `N` (as it is normal) and preserves both the order product and disjointness
in the `isComplement'_iff_card_mul_and_disjoint` characterisation. -/
theorem isComplement'_conjAct_smul [Finite H] {N : Subgroup H} [N.Normal] {K : Subgroup H}
    (hK : N.IsComplement' K) (g : ConjAct H) : N.IsComplement' (g • K) := by
  rw [Subgroup.isComplement'_iff_card_mul_and_disjoint] at hK ⊢
  obtain ⟨hcard, hdisj⟩ := hK
  refine ⟨?_, ?_⟩
  · have hK' : Nat.card ↥(g • K) = Nat.card ↥K :=
      (Nat.card_congr (Subgroup.equivSMul g K)).symm
    rw [hK']; exact hcard
  · have hN : g • N = N := Subgroup.Normal.conjAct ‹_› g
    rw [← hN, disjoint_iff, ← Subgroup.smul_inf, disjoint_iff.mp hdisj, Subgroup.smul_bot]

/-- The conjugation action of a normal subgroup `N` on the complements of `N` in `H`: an element
`n : N` sends a complement `K` to its conjugate `n K n⁻¹`, again a complement by
`isComplement'_conjAct_smul`. The orbits are the `N`-conjugacy classes of complements. -/
instance complementsConjAction [Finite H] (N : Subgroup H) [N.Normal] :
    MulAction ↥N {K : Subgroup H // N.IsComplement' K} where
  smul n K := ⟨ConjAct.toConjAct (n : H) • K.1, isComplement'_conjAct_smul K.2 _⟩
  one_smul K := by
    apply Subtype.ext
    change ConjAct.toConjAct ((1 : ↥N) : H) • K.1 = K.1
    simp
  mul_smul n m K := by
    apply Subtype.ext
    change ConjAct.toConjAct (((n * m : ↥N) : H)) • K.1
      = ConjAct.toConjAct ((n : H)) • ConjAct.toConjAct ((m : H)) • K.1
    rw [Subgroup.coe_mul, map_mul, mul_smul]

/-- **The orbit-counting factorization of the complement count.** For a normal subgroup `N` of a
finite group `H`, the number of complements of `N` is at most `|N|` times the number of
`N`-conjugacy classes of complements. This discharges the elementary geometric factor `|B¹| ≤ |N|`
of `#{complements} = |Z¹| = |B¹|·|H¹|`, leaving the cohomological factor `|H¹|` (the number of
classes) as the residual. -/
theorem card_isComplement'_le_card_mul_card_orbits [Finite H] (N : Subgroup H) [N.Normal] :
    Nat.card {K : Subgroup H // N.IsComplement' K}
      ≤ Nat.card ↥N *
        Nat.card (MulAction.orbitRel.Quotient ↥N {K : Subgroup H // N.IsComplement' K}) :=
  card_le_card_mul_card_orbitRel_quotient ↥N {K : Subgroup H // N.IsComplement' K}

/-- From the cohomological complement-class bound `#{N-conjugacy classes of complements} ≤ |H : N|`
follows the sharp per-factor bound `#{complements of N} ≤ |H|`, via the orbit-counting
factorization and Lagrange's `|N|·|H : N| = |H|`. -/
theorem card_isComplement'_le_of_card_orbits_le_index [Finite H] (N : Subgroup H) [N.Normal]
    (horb : Nat.card (MulAction.orbitRel.Quotient ↥N {K : Subgroup H // N.IsComplement' K})
      ≤ N.index) :
    Nat.card {K : Subgroup H // N.IsComplement' K} ≤ Nat.card H := by
  calc Nat.card {K : Subgroup H // N.IsComplement' K}
      ≤ Nat.card ↥N *
          Nat.card (MulAction.orbitRel.Quotient ↥N {K : Subgroup H // N.IsComplement' K}) :=
        card_isComplement'_le_card_mul_card_orbits N
    _ ≤ Nat.card ↥N * N.index := by gcongr
    _ = Nat.card H := Subgroup.card_mul_index N

/-- **The solvable maximal-subgroup count on the cohomological complement-class hypothesis.**
Restating `card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound` (`#{maximals} ≤ 2|G|`
for finite solvable `G`) on the strictly cohomological per-chief-factor hypothesis
`#{N-conjugacy classes of complements} ≤ |H : N|` — the named first-cohomology (Wall /
Aschbacher–Guralnick) bound `|H¹(H ⧸ N, N)| ≤ |H : N|` — with the elementary geometric factor `|N|`
already discharged by `card_isComplement'_le_of_card_orbits_le_index`. -/
theorem card_isCoatom_le_two_mul_card_of_isSolvable_of_orbitBound
    (horb : ∀ (H : Type u) [Group H] [Finite H] (N : Subgroup H) [N.Normal],
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      (∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N) →
      Nat.card (MulAction.orbitRel.Quotient ↥N {K : Subgroup H // N.IsComplement' K}) ≤ N.index) :
    ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card {M : Subgroup G // IsCoatom M} ≤ 2 * Nat.card G := by
  apply card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound
  intro H _ _ N hN hab hmin
  have := hN
  exact card_isComplement'_le_of_card_orbits_le_index N (horb H N hab hmin)

end AxQM.Concrete
