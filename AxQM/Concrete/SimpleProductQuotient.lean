/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Concrete: a simple quotient of a finite product of simple groups is a factor

This file supplies the **structural crux** behind the *aggregation* step of the Ettinger–Høyer–Knill
maximal-subgroup low-index sum `∑_{M ⋖ K} (|M|/|K|)^s` for Nielsen & Chuang, Problem 5.5 (the
non-Abelian hidden subgroup problem): a simple quotient of a *finite product of simple groups* is
isomorphic to one of the factors, and — equivalently — every simple quotient of `∏ᵢ Qᵢ` (each `Qᵢ`
simple) is one of the `Qᵢ`.

## Why the identification bound needs this

`Concrete/SubgroupMaximalSum.lean` reduced the collision tail to the maximal-subgroup sum
`∑_{M ⋖ K} [K:M]^{-s}`. A normal maximal `M ⋖ K` has *simple* quotient `K/M`; the **abelian**
(prime-index) part is discharged in `Concrete/SubgroupPrimeIndexNormalCount.lean`, and the *per
quotient-type* count of the **nonabelian-simple** normal maximals — for a fixed nonabelian simple
`Q`, `#{M ⋖ K : K/M ≅ Q} ≤ |Q|^{log₂|K|}` — is `Concrete/SubgroupFixedQuotientCount.lean`
(`card_relIndex_kernel_surjective_hom_le`). What remains to bound
`∑_{M ⋖ K,\ K/M\ \text{nonab.\ simple}} [K:M]^{-s}` is the **aggregation over quotient types**:

`∑_{Q\ \text{type}} \#\{M : K/M ≅ Q\}·|Q|^{-s} ≤ ∑_{Q\ \text{type}} |Q|^{\log_2|K|-s}`.

Because a nonabelian simple group has order `|Q| ≥ 60`, each term `|Q|^{\log_2|K|-s}` is tiny at
N&C's sample exponent (`s = 2\log_2|G|+1`), so this sum is `≤ 1/|G|` **provided the number of
distinct nonabelian-simple quotient types is `≤ \log_2|K|`**. That sharp type-count is essential: a
crude bound on the number of types by the number of subgroups (`≤ |K|^{\log_2|K|+1}`,
`Concrete.card_subgroup_le`) reintroduces a `(\log_2|K|)^2` term in the exponent and blows the bound
back up to the quadratic regime. The linear count needs `\#\text{types} ≤ \log_2|K|`, which comes
from `∏ᵢ |Qᵢ| ≤ |K|` for pairwise non-isomorphic quotient types `Qᵢ` — and *that* rests on the fact
proved here: a nonabelian simple `K/M` cannot be a (simple) quotient of a product of the *other*
types, since a simple quotient of a product of simple groups is one of the factors.

## What is proved

The `j`-th factor inclusion `Q j →* ∀ i, Q i` is Mathlib's `MonoidHom.mulSingle Q j` (it sends `a`
to `Pi.mulSingle j a`); this file only adds the fact Mathlib lacks:

* `mulSingle_range_normal` — the range of `MonoidHom.mulSingle Q j` is a **normal** subgroup of the
  product (conjugation acts coordinatewise, fixing the off-`j` coordinates and conjugating the
  `j`-th entry, so it maps the factor to itself).
* `exists_mulEquiv_of_surjective_pi` — for a finite product `∀ i, Q i` of simple groups and a
  **surjective** homomorphism `f : (∀ i, Q i) →* R` onto a simple group `R`, some factor is
  isomorphic to `R`: `∃ j, Nonempty (Q j ≃* R)`. The proof is **commutator-free**: the factor
  inclusions generate the product (`Subgroup.pi_mem_of_mulSingle_mem`), so `f` cannot kill all of
  them (else `R` would be trivial); a factor `Q j` it does not kill maps to a *normal* subgroup of
  `R` (`Subgroup.Normal.map`, `f` surjective) that is nontrivial, hence all of `R` (`R` simple), and
  the restriction `Q j →* R` has nontrivial kernel-quotient — being simple, `Q j` forces the kernel
  to be trivial, so the restriction is a bijection.
* `exists_mulEquiv_quotient_of_pi` — the quotient form: for a normal subgroup `M` of a finite
  product of simple groups with `(∀ i, Q i) ⧸ M` simple (e.g. `M` a maximal normal subgroup),
  `∃ j, Nonempty (Q j ≃* (∀ i, Q i) ⧸ M)`. Immediate from the previous theorem applied to the
  quotient map `QuotientGroup.mk' M`.

The remaining step for the aggregation — the surjectivity of the diagonal `K →* ∏ᵢ (K ⧸ Nᵢ)` for
pairwise non-isomorphic simple quotients, giving `∏ᵢ [K:Nᵢ] = [K : ⨅ᵢ Nᵢ] ≤ |K|` and hence
`\#\text{types} ≤ \log_2|K|`, then the sum bound itself — is proved separately (the type count in
`Concrete/PairwiseSimpleQuotientCount.lean`); it consumes
`exists_mulEquiv_quotient_of_pi` here at each induction step.
-/

namespace AxQM.Concrete

variable {ι : Type*} {Q : ι → Type*} [∀ i, Group (Q i)]

/-- **The range of the `j`-th factor inclusion is a normal subgroup of the product.** The `j`-th
factor inclusion is Mathlib's `MonoidHom.mulSingle Q j`, sending `a` to the tuple `Pi.mulSingle j a`
(value `a` in coordinate `j` and `1` elsewhere). Conjugating such a tuple acts coordinatewise, so it
fixes the `1`'s off `j` and conjugates the `j`-th entry — the result is again supported at `j`.
(Mathlib has `Subgroup.prod_normal` for a binary product, but not this factor-of-a-`Pi` form.) -/
lemma mulSingle_range_normal [DecidableEq ι] (j : ι) :
    ((MonoidHom.mulSingle Q j).range).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ g
    refine ⟨g j * a * (g j)⁻¹, ?_⟩
    funext i
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [Pi.mulSingle_eq_of_ne h]

/-- **A simple group that is a surjective image of a finite product of simple groups is isomorphic
to one of the factors.** For a finite product `∀ i, Q i` of simple groups `Q i` and a surjective
homomorphism `f` onto a simple group `R`, some factor `Q j` satisfies `Q j ≃* R`.

Proof (commutator-free). The factor inclusions `MonoidHom.mulSingle Q j` generate the product
(`Subgroup.pi_mem_of_mulSingle_mem`), so `f` cannot vanish on every `Pi.mulSingle j a` — otherwise
`f` would be trivial and `R` a single point, contradicting `R` nontrivial (part of `IsSimpleGroup`).
Pick a factor `Q j` and `a₀` with `f (Pi.mulSingle j a₀) ≠ 1`, and set
`fⱼ := f ∘ MonoidHom.mulSingle Q j`. Its kernel is a normal subgroup of the simple group `Q j`, and
it is not everything (`fⱼ a₀ ≠ 1`), so it is trivial: `fⱼ` is injective. Its range is
`Subgroup.map f (MonoidHom.mulSingle Q j).range`, the image of a *normal* subgroup
(`mulSingle_range_normal`) under the surjection `f`, hence normal in `R` (`Subgroup.Normal.map`); it
is nontrivial, and `R` is simple, so the range is all of `R`: `fⱼ` is surjective. A bijective
homomorphism is an isomorphism. -/
theorem exists_mulEquiv_of_surjective_pi [Finite ι] [∀ i, IsSimpleGroup (Q i)]
    {R : Type*} [Group R] [IsSimpleGroup R] (f : (∀ i, Q i) →* R) (hf : Function.Surjective f) :
    ∃ j, Nonempty (Q j ≃* R) := by
  classical
  -- Some factor is not killed by `f` (else `f` is trivial and `R` a single point).
  have hne : ∃ (j : ι) (a : Q j), f (Pi.mulSingle j a) ≠ 1 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    have hker : ∀ x : ∀ i, Q i, x ∈ f.ker := fun x =>
      Subgroup.pi_mem_of_mulSingle_mem x (fun i => MonoidHom.mem_ker.mpr (h i (x i)))
    have hall : ∀ y : R, y = 1 := fun y => by
      obtain ⟨x, rfl⟩ := hf y
      exact MonoidHom.mem_ker.mp (hker x)
    obtain ⟨a, b, hab⟩ := exists_pair_ne R
    exact hab ((hall a).trans (hall b).symm)
  obtain ⟨j, a₀, ha₀⟩ := hne
  refine ⟨j, ⟨?_⟩⟩
  set fⱼ := f.comp (MonoidHom.mulSingle Q j) with hfⱼ
  have hfⱼa₀ : fⱼ a₀ ≠ 1 := ha₀
  -- `fⱼ` is injective: its kernel is a proper normal subgroup of the simple group `Q j`.
  have hkerbot : fⱼ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fⱼ.ker with h | h
    · exact h
    · exfalso; apply hfⱼa₀
      have : a₀ ∈ fⱼ.ker := by rw [h]; exact Subgroup.mem_top a₀
      exact MonoidHom.mem_ker.mp this
  have hinj : Function.Injective fⱼ := (MonoidHom.ker_eq_bot_iff fⱼ).mp hkerbot
  -- `fⱼ` is surjective: its range is a nontrivial normal subgroup of the simple group `R`.
  have hrange : fⱼ.range = Subgroup.map f (MonoidHom.mulSingle Q j).range := by
    rw [hfⱼ, MonoidHom.range_comp]
  have hnorm : fⱼ.range.Normal := by
    rw [hrange]; exact (mulSingle_range_normal j).map f hf
  have hsurj : Function.Surjective fⱼ := by
    rw [← MonoidHom.range_eq_top]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fⱼ.range with h | h
    · exfalso; apply hfⱼa₀
      have : fⱼ a₀ ∈ fⱼ.range := ⟨a₀, rfl⟩
      rw [h] at this; exact Subgroup.mem_bot.mp this
    · exact h
  exact MulEquiv.ofBijective fⱼ ⟨hinj, hsurj⟩

/-- **A simple quotient of a finite product of simple groups is isomorphic to one of the factors.**
For a normal subgroup `M` of a finite product `∀ i, Q i` of simple groups with the quotient
`(∀ i, Q i) ⧸ M` itself simple (e.g. `M` a maximal normal subgroup), some factor `Q j` satisfies
`Q j ≃* (∀ i, Q i) ⧸ M`. Immediate from `exists_mulEquiv_of_surjective_pi` applied to the surjective
quotient map `QuotientGroup.mk' M`. -/
theorem exists_mulEquiv_quotient_of_pi [Finite ι] [∀ i, IsSimpleGroup (Q i)]
    (M : Subgroup (∀ i, Q i)) [M.Normal] [IsSimpleGroup ((∀ i, Q i) ⧸ M)] :
    ∃ j, Nonempty (Q j ≃* (∀ i, Q i) ⧸ M) :=
  exists_mulEquiv_of_surjective_pi (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)

end AxQM.Concrete
