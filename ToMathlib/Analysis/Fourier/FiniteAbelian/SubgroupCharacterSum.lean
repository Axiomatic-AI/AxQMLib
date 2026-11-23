/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Character sums over subgroups and their factorization over products

Let `A` be a finite additive abelian group and `ψ : AddChar A R` a character valued in an integral
domain `R` of characteristic zero (e.g. `ℂ`). This file studies the sum of `ψ` over a subgroup
`K ≤ A` and, when `A = ∏ᵢ Aᵢ` is a finite product with `K = ∏ᵢ Kᵢ` a product of subgroups, its
factorization across the factors.

## Main statements

* `AddChar.sum_subgroup_eq_natCard_iff` — the sum of a character over a subgroup attains its maximal
  value `|K|` iff the character is **trivial on `K`**:
  `∑_{h ∈ K} ψ h = |K| ↔ ∀ h ∈ K, ψ h = 1`.
  (Otherwise the sum vanishes, by orthogonality of characters.)
* `AddChar.pi` — the **product character** `(∏ᵢ ψᵢ)(g) = ∏ᵢ ψᵢ (gᵢ)` on `∏ᵢ Aᵢ`.
* `AddChar.pi_eq_one_on_pi_iff` — the product character is **trivial on `∏ᵢ Kᵢ`** iff each factor
  `ψᵢ` is trivial on `Kᵢ`: `(∀ g ∈ ∏ᵢ Kᵢ, ∏ᵢ ψᵢ gᵢ = 1) ↔ ∀ i, ∀ h ∈ Kᵢ, ψᵢ h = 1`.
* `AddChar.sum_pi_subgroup_prod` — the character sum over `∏ᵢ Kᵢ` **factorizes** as a product of the
  per-factor sums: `∑_{h ∈ ∏ᵢ Kᵢ} ∏ᵢ ψᵢ hᵢ = ∏ᵢ (∑_{h ∈ Kᵢ} ψᵢ h)`.
* `AddChar.sum_pi_subgroup_eq_natCard_iff` — the **re-expression of the maximal-sum condition**: the
  global sum over `∏ᵢ Kᵢ` attains `|∏ᵢ Kᵢ|` iff *each* per-factor sum attains `|Kᵢ|`:
  `(∑_{h ∈ ∏ᵢ Kᵢ} ∏ᵢ ψᵢ hᵢ = |∏ᵢ Kᵢ|) ↔ ∀ i, (∑_{h ∈ Kᵢ} ψᵢ h = |Kᵢ|)`.

## Application: Nielsen & Chuang, Exercise 5.26 (the Abelian hidden subgroup problem)

In the Abelian HSP algorithm (Nielsen & Chuang, §5.4.3) the quantum Fourier transform of a function
constant on cosets of a hidden subgroup `K ≤ G` produces a state whose amplitude at the character
index `ℓ` is governed by the character sum `∑_{h ∈ K} e^{-2πi ℓ·h/|G|}`. This equals `|K|` — the
condition **(5.77)** for `ℓ` to be a possible measurement outcome — exactly when the character
`χ_ℓ : h ↦ e^{-2πi ℓ·h/|G|}` is trivial on `K` (`sum_subgroup_eq_natCard_iff`); i.e. the measurement
samples uniformly from the *annihilator* of `K`.

Writing `G = ℤ_{p₁} × ⋯ × ℤ_{p_M}` as a product of cyclic groups of prime-power order (the
structure theorem), the character factorizes as `χ_ℓ(g) = ∏ᵢ e^{-2πi ℓᵢ·gᵢ/pᵢ}` — this is
**(5.78)**, captured abstractly by `AddChar.pi` / `AddChar.pi_apply` (every character of a finite
abelian group has this form). The exercise's premise "this also decomposes `K`" is that `K = ∏ᵢ Kᵢ`
for `Kᵢ ≤ ℤ_{pᵢ}` (the primary decomposition). Then:

* `sum_pi_subgroup_prod` **re-expresses (5.77)** as a product `∏ᵢ (∑_{hᵢ ∈ Kᵢ} e^{-2πi ℓᵢ·hᵢ/pᵢ})`;
* `sum_pi_subgroup_eq_natCard_iff` shows this equals `|K|` iff *each* factor equals `|Kᵢ|`, and
  `pi_eq_one_on_pi_iff` shows that per-factor condition is exactly `ℓᵢ` annihilating `Kᵢ`.

Hence **determining the component `ℓᵢ`** (a solution of the per-factor condition) yields a
constraint on — a sample from the dual of — the cyclic subgroup `K_{pᵢ} = Kᵢ`, i.e. Exercise 5.26.

The results are stated for an arbitrary finite index `ι` and arbitrary finite abelian factors `Aᵢ`
with an arbitrary character-valued domain `R`; this is strictly more general than (so faithful to)
the concrete `∏ᵢ ℤ_{pᵢ}` / `e^{-2πi·/·}` instance, since a character of `ℤ_{pᵢ}` *is* such a phase.
-/

@[expose] public section

open scoped BigOperators

namespace AddChar

section Subgroup

variable {A R : Type*} [AddCommGroup A] [CommRing R] [IsDomain R] [CharZero R]

/-- **The character sum over a subgroup is maximal iff the character is trivial on it.** For a
character `ψ : AddChar A R` valued in a characteristic-zero integral domain and a finite subgroup
`K ≤ A`, the sum `∑_{h ∈ K} ψ h` equals the order `|K|` iff `ψ` restricts to the trivial character
on `K`; otherwise the sum vanishes (orthogonality of characters). This is Nielsen & Chuang eq.
(5.77): the character index `ℓ` survives (`∑_{h ∈ K} e^{-2πi ℓ·h/|G|} = |K|`) exactly when
`h ↦ e^{-2πi ℓ·h/|G|}` is trivial on the hidden subgroup `K`. -/
theorem sum_subgroup_eq_natCard_iff [Fintype A] (K : AddSubgroup A) [DecidablePred (· ∈ K)]
    (ψ : AddChar A R) :
    ∑ h : K, ψ (h : A) = Fintype.card K ↔ ∀ h ∈ K, ψ h = 1 := by
  have key : ∑ h : K, ψ (h : A) = ∑ h : K, (ψ.compAddMonoidHom K.subtype) h :=
    Finset.sum_congr rfl fun h _ => (ψ.compAddMonoidHom_apply K.subtype h).symm
  rw [key]
  by_cases htriv : ψ.compAddMonoidHom K.subtype = 1
  · rw [sum_eq_card_of_eq_one htriv]
    refine iff_of_true rfl fun h hh => ?_
    have h1 := (eq_one_iff.mp htriv) ⟨h, hh⟩
    rwa [compAddMonoidHom_apply] at h1
  · rw [sum_eq_zero_of_ne_one htriv]
    have hcard : (Fintype.card K : R) ≠ 0 := by
      have hpos : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨⟨0, K.zero_mem⟩⟩
      exact_mod_cast hpos.ne'
    refine iff_of_false (fun h0 => hcard h0.symm) fun hall => htriv ?_
    exact eq_one_iff.mpr fun x => hall (x : A) x.2

end Subgroup

section Pi

variable {ι : Type*} [Fintype ι]
  {A : ι → Type*} [∀ i, AddCommGroup (A i)]

section CommMonoid

variable {R : Type*} [CommMonoid R]

/-- **The product of a family of additive characters** `(∏ᵢ ψᵢ)(g) = ∏ᵢ ψᵢ (gᵢ)`, a character of
the product group `∏ᵢ Aᵢ`. This is the abstract form of Nielsen & Chuang eq. (5.78): the character
`e^{-2πi ℓ·g/|G|}` of `G = ∏ᵢ ℤ_{pᵢ}` factorizes as `∏ᵢ e^{-2πi ℓᵢ·gᵢ/pᵢ}`. -/
def pi (ψ : ∀ i, AddChar (A i) R) : AddChar (∀ i, A i) R where
  toFun f := ∏ i, ψ i (f i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' f g := by
    simp only [Pi.add_apply, map_add_eq_mul]
    rw [Finset.prod_mul_distrib]

/-- The product character evaluates as the product of the factor characters:
`(∏ᵢ ψᵢ)(f) = ∏ᵢ ψᵢ (fᵢ)`. -/
@[simp]
theorem pi_apply (ψ : ∀ i, AddChar (A i) R) (f : ∀ i, A i) : pi ψ f = ∏ i, ψ i (f i) := rfl

instance instDecidablePredMemPiUniv (K : ∀ i, AddSubgroup (A i)) [∀ i, DecidablePred (· ∈ K i)] :
    DecidablePred (· ∈ AddSubgroup.pi (Set.univ : Set ι) K) := fun f =>
  decidable_of_iff (∀ i, f i ∈ K i) (by simp [AddSubgroup.mem_pi])

/-- **The product character is trivial on `∏ᵢ Kᵢ` iff each factor is trivial on `Kᵢ`.** This is the
factorization of the annihilator condition: for `K = ∏ᵢ Kᵢ ≤ ∏ᵢ Aᵢ`,
`(∀ g ∈ ∏ᵢ Kᵢ, ∏ᵢ ψᵢ gᵢ = 1) ↔ ∀ i, ∀ h ∈ Kᵢ, ψᵢ h = 1`. In Nielsen & Chuang Exercise 5.26 this
says the surviving index `ℓ` annihilates `K` iff each component `ℓᵢ` annihilates the cyclic factor
`Kᵢ = K_{pᵢ}` — so determining `ℓᵢ` samples from (the dual of) `K_{pᵢ}`. -/
theorem pi_eq_one_on_pi_iff (K : ∀ i, AddSubgroup (A i)) (ψ : ∀ i, AddChar (A i) R) :
    (∀ f ∈ AddSubgroup.pi (Set.univ) K, pi ψ f = 1) ↔ ∀ i, ∀ h ∈ K i, ψ i h = 1 := by
  classical
  constructor
  · intro H i h hh
    have hmem : Pi.single i h ∈ AddSubgroup.pi (Set.univ : Set ι) K := by
      rw [AddSubgroup.mem_pi]
      intro j _
      by_cases hj : j = i
      · subst hj; rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hj]; exact (K j).zero_mem
    have hval := H _ hmem
    rw [pi_apply, Finset.prod_eq_single i
        (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero_eq_one])
        (fun hi => absurd (Finset.mem_univ i) hi)] at hval
    rwa [Pi.single_eq_same] at hval
  · intro H f hf
    rw [pi_apply, AddSubgroup.mem_pi] at *
    exact Finset.prod_eq_one fun i _ => H i (f i) (hf i (Set.mem_univ i))

end CommMonoid

variable [DecidableEq ι] [∀ i, Fintype (A i)]

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- **The character sum over a product subgroup factorizes** as the product of the per-factor sums:
`∑_{h ∈ ∏ᵢ Kᵢ} ∏ᵢ ψᵢ hᵢ = ∏ᵢ (∑_{h ∈ Kᵢ} ψᵢ h)`. This is the literal re-expression of Nielsen &
Chuang eq. (5.77) under the factorization (5.78): the single character sum over the decomposed
hidden subgroup `K = ∏ᵢ K_{pᵢ}` becomes a product of independent sums over the cyclic factors. -/
theorem sum_pi_subgroup_prod (K : ∀ i, AddSubgroup (A i)) [∀ i, DecidablePred (· ∈ K i)]
    (ψ : ∀ i, AddChar (A i) R) :
    ∑ h : ↥(AddSubgroup.pi (Set.univ) K), ∏ i, ψ i ((h : ∀ i, A i) i)
      = ∏ i, ∑ h : ↥(K i), ψ i (h : A i) := by
  let e : ↥(AddSubgroup.pi (Set.univ : Set ι) K) ≃ (∀ i, ↥(K i)) :=
    (Equiv.subtypeEquivRight (q := fun f => ∀ i, f i ∈ K i)
      fun f => by rw [AddSubgroup.mem_pi]; simp).trans
      (Equiv.subtypePiEquivPi (p := fun i x => x ∈ K i))
  rw [Fintype.sum_equiv e (fun h => ∏ i, ψ i ((h : ∀ i, A i) i))
      (fun k => ∏ i, ψ i ((k i : A i))) (fun _ => rfl),
    Finset.prod_univ_sum (fun i => (Finset.univ : Finset ↥(K i))) (fun i h => ψ i (h : A i)),
    Fintype.piFinset_univ]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- **Re-expression of the maximal-sum condition (5.77) over the product decomposition.** The global
character sum over the decomposed hidden subgroup `K = ∏ᵢ Kᵢ` attains its maximum `|K|` **iff each
per-factor sum attains `|Kᵢ|`**:
`(∑_{h ∈ ∏ᵢ Kᵢ} ∏ᵢ ψᵢ hᵢ = |∏ᵢ Kᵢ|) ↔ ∀ i, (∑_{h ∈ Kᵢ} ψᵢ h = |Kᵢ|)`.

This is the content of Nielsen & Chuang Exercise 5.26: the condition (5.77) on the character index
`ℓ` decouples into `M` independent conditions, one per cyclic factor `K_{pᵢ}`, so **determining each
component `ℓᵢ`** (via phase-estimation of that factor) is equivalent to solving (5.77) globally —
and by `pi_eq_one_on_pi_iff` each per-factor condition is exactly `ℓᵢ` annihilating `K_{pᵢ}`. -/
theorem sum_pi_subgroup_eq_natCard_iff (K : ∀ i, AddSubgroup (A i)) [∀ i, DecidablePred (· ∈ K i)]
    (ψ : ∀ i, AddChar (A i) R) :
    (∑ h : ↥(AddSubgroup.pi (Set.univ) K), ∏ i, ψ i ((h : ∀ i, A i) i)
        = Fintype.card ↥(AddSubgroup.pi (Set.univ) K))
      ↔ ∀ i, ∑ h : ↥(K i), ψ i (h : A i) = Fintype.card ↥(K i) := by
  have hrw : (∑ h : ↥(AddSubgroup.pi (Set.univ) K), ∏ i, ψ i ((h : ∀ i, A i) i))
      = ∑ h : ↥(AddSubgroup.pi (Set.univ) K), pi ψ (h : ∀ i, A i) :=
    Finset.sum_congr rfl fun h _ => (pi_apply ψ _).symm
  rw [hrw, sum_subgroup_eq_natCard_iff (AddSubgroup.pi (Set.univ) K) (pi ψ),
    pi_eq_one_on_pi_iff]
  refine forall_congr' fun i => ?_
  exact (sum_subgroup_eq_natCard_iff (K i) (ψ i)).symm

end CommRing

end Pi

section ZMod

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} [∀ i, NeZero (n i)]

/-- **The Abelian-HSP character sum factorizes (Nielsen & Chuang eqs. (5.77)–(5.78)).** Over the
literal group `G = ∏ᵢ ℤ_{nᵢ}` of the exercise, with the standard root-of-unity characters
`ZMod.stdAddChar (ℓᵢ · hᵢ) = e^{2πi ℓᵢ hᵢ / nᵢ}` (Nielsen & Chuang uses the conjugate phase
`e^{-2πi ℓᵢ hᵢ / nᵢ}`, i.e. the character indexed by `-ℓᵢ`, immaterial to what follows), the single
character sum of (5.77) over the decomposed hidden subgroup `K = ∏ᵢ K_{pᵢ}` **re-expresses as the
product** of the per-factor sums — this is (5.77) rewritten via the phase factorization (5.78). -/
theorem sum_pi_subgroup_zmod_prod (K : ∀ i, AddSubgroup (ZMod (n i)))
    [∀ i, DecidablePred (· ∈ K i)] (ℓ : ∀ i, ZMod (n i)) :
    ∑ h : ↥(AddSubgroup.pi (Set.univ) K),
        ∏ i, ZMod.stdAddChar (ℓ i * (h : ∀ i, ZMod (n i)) i)
      = ∏ i, ∑ h : ↥(K i), ZMod.stdAddChar (ℓ i * (h : ZMod (n i))) := by
  simpa only [AddChar.mulShift_apply]
    using sum_pi_subgroup_prod K fun i => ZMod.stdAddChar.mulShift (ℓ i)

/-- **Re-expression of (5.77) over `G = ∏ᵢ ℤ_{nᵢ}` (Nielsen & Chuang, Exercise 5.26).** With the
standard characters `ZMod.stdAddChar (ℓᵢ · hᵢ) = e^{2πi ℓᵢ hᵢ / nᵢ}`, the (5.77) condition — that
the character sum over the decomposed hidden subgroup `K = ∏ᵢ K_{pᵢ}` attains its maximum `|K|` —
holds **iff each per-factor sum attains `|K_{pᵢ}|`**. So determining each component `ℓᵢ` (via the
phase-estimation of that cyclic factor) is equivalent to solving (5.77) globally, which is exactly
the exercise's assertion that determining `ℓᵢ` lets one sample from the cyclic subgroup `K_{pᵢ}`. -/
theorem sum_pi_subgroup_zmod_eq_natCard_iff (K : ∀ i, AddSubgroup (ZMod (n i)))
    [∀ i, DecidablePred (· ∈ K i)] (ℓ : ∀ i, ZMod (n i)) :
    (∑ h : ↥(AddSubgroup.pi (Set.univ) K),
          ∏ i, ZMod.stdAddChar (ℓ i * (h : ∀ i, ZMod (n i)) i)
        = Fintype.card ↥(AddSubgroup.pi (Set.univ) K))
      ↔ ∀ i, ∑ h : ↥(K i), ZMod.stdAddChar (ℓ i * (h : ZMod (n i)))
          = Fintype.card ↥(K i) := by
  simpa only [AddChar.mulShift_apply]
    using sum_pi_subgroup_eq_natCard_iff K fun i => ZMod.stdAddChar.mulShift (ℓ i)

end ZMod

end AddChar
