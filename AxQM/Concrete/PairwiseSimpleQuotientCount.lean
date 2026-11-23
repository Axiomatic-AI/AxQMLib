/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SimpleProductQuotient
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Concrete: normal subgroups with pairwise non-isomorphic simple quotients

This file supplies the **diagonal-surjectivity / product-of-indices** step of the *aggregation over
quotient types* behind the Ettinger–Høyer–Knill maximal-subgroup low-index sum `∑_{M ⋖ K}
(|M|/|K|)^s` for Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## Why the identification bound needs this

`Concrete/SubgroupFixedQuotientCount.lean` counts, per fixed nonabelian-simple quotient type `Q`,
the normal maximals `M ⋖ K` with `K/M ≅ Q` (`card_relIndex_kernel_surjective_hom_le`). Bounding the
residual sum `∑_{M ⋖ K,\ K/M\ \text{nonab.\ simple}} [K:M]^{-s}` by aggregating those per-type
counts
needs the **number of distinct nonabelian-simple quotient types of `K` to be `≤ log₂|K|`** — the
sharp count (a crude type-count by the number of subgroups reintroduces a `(log₂|K|)²` term and
returns to the quadratic sample regime).

That sharp type-count is exactly the corollary `card_le_log_of_pairwise_noniso_simpleQuotient`
below:
pick one normal subgroup `N i` per quotient type, so the `G ⧸ N i` are simple and pairwise
non-isomorphic; then `∏ᵢ [G : N i] ≤ |G|` (`prod_index_le_card_of_pairwise_noniso_simpleQuotient`),
and since each simple quotient has order `≥ 2` this forces `2^{#types} ≤ |G|`, i.e.
`#types ≤ log₂|G|`.

## What is proved

The mathematical heart is that the **diagonal** `G →* ∏ᵢ (G ⧸ N i)` is *surjective* when the
quotients `G ⧸ N i` are simple and pairwise non-isomorphic. It is proved by induction on the index
finset: at the step
adding `N j`, the intersection `M = ⋂_{i∈s} N i` (the kernel of the diagonal over `s`) cannot be
contained in `N j` — else `G ⧸ N j` would be a simple quotient of `∏_{i∈s} (G ⧸ N i)`, hence
isomorphic to one of the factors (`Concrete.exists_mulEquiv_of_surjective_pi`,
`Concrete/SimpleProductQuotient.lean`), contradicting pairwise non-isomorphism — so `M` and `N j`
are
**comaximal** (`M ⊔ N j = ⊤`), and two comaximal normal subgroups have a jointly surjective pair of
quotient maps (`surjective_prod_of_sup_ker_eq_top`). Counting the surjection's finite codomain gives
the product-of-indices bound, and comparing with `2^{#s}` gives the count bound:

* `surjective_prod_of_sup_ker_eq_top` — for `f : G →* A`, `h : G →* B` surjective with
  `ker f ⊔ ker h = ⊤`, the pair `(f, h) : G →* A × B` is surjective (the two-factor Chinese
  remainder
  surjectivity: `h` restricted to `ker f` is already onto, since `h (ker f) = h (ker f ⊔ ker h) =
  ⊤`).
* `sup_ker_eq_top_of_not_le` — a normal subgroup `M` not contained in the kernel of a surjection
onto
  a *simple* group `B` is comaximal with that kernel (`M ⊔ ker f = ⊤`): the image `f(M)` is a
  nontrivial normal subgroup of the simple `B`, hence `⊤`, whence `comap f ⊤ = M ⊔ ker f = ⊤`.
* `diagPiQuot` / `diagPiQuot_surjective` — the diagonal `G →* ∏_{i∈s} (G ⧸ N i)` and its
surjectivity
  for pairwise non-isomorphic simple quotients.
* `prod_index_le_card_of_pairwise_noniso_simpleQuotient` — `∏_{i∈s} [G : N i] ≤ |G|`.
* `card_le_log_of_pairwise_noniso_simpleQuotient` — `#s ≤ log₂|G|`.
-/

namespace AxQM.Concrete

variable {G : Type*} [Group G]

/-- **Two comaximal normal subgroups have jointly surjective quotient maps.** For surjective
homomorphisms `f : G →* A`, `h : G →* B` whose kernels are comaximal (`ker f ⊔ ker h = ⊤`), the pair
`(f, h) : G →* A × B` is surjective. The point is that `h` restricted to `ker f` is *already* onto
`B`: `h (ker f) = h (ker f) ⊔ h (ker h) = h (ker f ⊔ ker h) = h ⊤ = ⊤` (as `h (ker h) = ⊥`). So to
hit `(a, b)` we pick any `x` with `f x = a` and correct by an element of `ker f` mapping under `h`
to
`h(x)⁻¹ b`. This is the two-factor Chinese remainder theorem for groups. -/
theorem surjective_prod_of_sup_ker_eq_top {A B : Type*} [Group A] [Group B]
    (f : G →* A) (h : G →* B) (hf : Function.Surjective f) (hh : Function.Surjective h)
    (hsup : f.ker ⊔ h.ker = ⊤) : Function.Surjective (f.prod h) := by
  have hmap : Subgroup.map h f.ker = ⊤ := by
    have h1 : Subgroup.map h (f.ker ⊔ h.ker)
        = Subgroup.map h f.ker ⊔ Subgroup.map h h.ker := Subgroup.map_sup _ _ _
    rw [hsup, Subgroup.map_top_of_surjective h hh, (Subgroup.map_eq_bot_iff h.ker).mpr le_rfl,
      sup_bot_eq] at h1
    exact h1.symm
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ := hf a
  have hmem : h x⁻¹ * b ∈ Subgroup.map h f.ker := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
  have ha : f (x * k) = f x := by rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]
  have hb : h (x * k) = b := by rw [map_mul, hkeq, map_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  exact ⟨x * k, by rw [MonoidHom.prod_apply, ha, hb]⟩

/-- **A normal subgroup not below the kernel of a surjection onto a simple group is comaximal with
it.** If `f : G →* B` is surjective, `B` is simple, and the normal subgroup `M` is not contained in
`ker f`, then `M ⊔ ker f = ⊤`. Indeed the image `f(M)` is a normal subgroup of the simple group `B`
(the image of a normal subgroup under a surjection is normal), and it is not `⊥` (that would force
`M ≤ ker f`), so it is `⊤`; then `⊤ = comap f ⊤ = comap f (f(M)) = M ⊔ ker f`. Applied with
`f = QuotientGroup.mk' N` and `B = G ⧸ N` (`N` a maximal-normal subgroup, `G ⧸ N` simple), this says
a normal subgroup not contained in `N` is comaximal with it. -/
theorem sup_ker_eq_top_of_not_le {B : Type*} [Group B] [IsSimpleGroup B]
    (f : G →* B) (hf : Function.Surjective f) {M : Subgroup G} [M.Normal]
    (hM : ¬ M ≤ f.ker) : M ⊔ f.ker = ⊤ := by
  have hnorm : (Subgroup.map f M).Normal := ‹M.Normal›.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.map f M) with h | h
  · exact absurd ((Subgroup.map_eq_bot_iff M).mp h) hM
  · have hcomap : Subgroup.comap f (Subgroup.map f M) = ⊤ := by rw [h]; exact Subgroup.comap_top f
    rwa [Subgroup.comap_map_eq] at hcomap

variable {ι : Type*}

/-- **The diagonal homomorphism into a finite product of quotient groups.** For a finset `s` of
indices, `diagPiQuot N s` sends `g` to the tuple `(g mod N i)_{i ∈ s}` in `∏_{i ∈ s} (G ⧸ N i)`. It
is `MonoidHom.pi` of the quotient maps. -/
def diagPiQuot (N : ι → Subgroup G) [∀ i, (N i).Normal] (s : Finset ι) :
    G →* (∀ i : {x // x ∈ s}, G ⧸ N (i : ι)) :=
  MonoidHom.pi fun i => QuotientGroup.mk' (N (i : ι))

@[simp] theorem diagPiQuot_apply (N : ι → Subgroup G) [∀ i, (N i).Normal] (s : Finset ι) (g : G)
    (i : {x // x ∈ s}) : diagPiQuot N s g i = (QuotientGroup.mk g : G ⧸ N (i : ι)) := by
  rw [diagPiQuot, MonoidHom.pi_apply, QuotientGroup.mk'_apply]

/-- **The diagonal into a finite product of pairwise non-isomorphic simple quotients is
surjective.**
For a finset `s` and normal subgroups `N i` with `G ⧸ N i` simple and pairwise non-isomorphic over
`s`, the diagonal `G →* ∏_{i ∈ s} (G ⧸ N i)` is surjective.

Proof by `Finset.induction`. At the step adding a new index `j`, write `f = diagPiQuot N s` (the
diagonal over the smaller finset, surjective by the induction hypothesis) and consider its kernel
`ker f = ⋂_{i∈s} N i`. If `ker f ≤ N j`, then the quotient map `G ↠ G ⧸ N j` factors through `f`,
giving a *surjection* `(∏_{i∈s} G ⧸ N i) ↠ G ⧸ N j`; as a simple quotient of a product of simple
groups, `G ⧸ N j` is then isomorphic to one of the factors `G ⧸ N i` (`i ∈ s`)
(`exists_mulEquiv_of_surjective_pi`), contradicting pairwise non-isomorphism (`j ∉ s`). So
`ker f ⊄ N j`, hence `ker f ⊔ N j = ⊤` (`sup_ker_eq_top_of_not_le`), and the pair
`(f, mk' (N j)) : G →* (∏_{i∈s} G ⧸ N i) × (G ⧸ N j)` is surjective
(`surjective_prod_of_sup_ker_eq_top`), which is exactly surjectivity of the diagonal over
`insert j s`. -/
theorem diagPiQuot_surjective (N : ι → Subgroup G) [∀ i, (N i).Normal] (s : Finset ι)
    (hsimple : ∀ i ∈ s, IsSimpleGroup (G ⧸ N i))
    (hnoniso : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → IsEmpty (G ⧸ N i ≃* G ⧸ N k)) :
    Function.Surjective (diagPiQuot N s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have : Subsingleton (∀ i : {x // x ∈ (∅ : Finset ι)}, G ⧸ N (i : ι)) :=
        ⟨fun a b => funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
      exact fun t => ⟨1, Subsingleton.elim _ _⟩
  | @insert j s hjs ih =>
      have hsimple_s : ∀ i ∈ s, IsSimpleGroup (G ⧸ N i) :=
        fun i hi => hsimple i (Finset.mem_insert_of_mem hi)
      have hnoniso_s : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → IsEmpty (G ⧸ N i ≃* G ⧸ N k) :=
        fun i hi k hk => hnoniso i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk)
      have ihs : Function.Surjective (diagPiQuot N s) := ih hsimple_s hnoniso_s
      have hSj : IsSimpleGroup (G ⧸ N j) := hsimple j (Finset.mem_insert_self j s)
      have : ∀ i : {x // x ∈ s}, IsSimpleGroup (G ⧸ N (i : ι)) := fun i => hsimple_s (i : ι) i.2
      -- The diagonal's kernel is not contained in `N j` (else `G ⧸ N j` is a factor). Phrased via
      -- `(mk' (N j)).ker` so the comaximality lemma applies without unfolding the diagonal's
      -- kernel by `isDefEq`.
      have hnotle : ¬ (diagPiQuot N s).ker ≤ (QuotientGroup.mk' (N j)).ker := by
        intro hle'
        set e := QuotientGroup.quotientKerEquivOfSurjective (diagPiQuot N s) ihs
        have hlift : Function.Surjective
            (QuotientGroup.lift (diagPiQuot N s).ker (QuotientGroup.mk' (N j)) hle') :=
          QuotientGroup.lift_surjective_of_surjective (diagPiQuot N s).ker
            (QuotientGroup.mk' (N j)) (QuotientGroup.mk'_surjective (N j)) hle'
        set ψ : (∀ i : {x // x ∈ s}, G ⧸ N (i : ι)) →* G ⧸ N j :=
          (QuotientGroup.lift (diagPiQuot N s).ker (QuotientGroup.mk' (N j)) hle').comp
            e.symm.toMonoidHom
        have hψ : Function.Surjective ψ := hlift.comp e.symm.surjective
        obtain ⟨i, ⟨φ⟩⟩ := exists_mulEquiv_of_surjective_pi
          (Q := fun i : {x // x ∈ s} => G ⧸ N (i : ι)) (R := G ⧸ N j) ψ hψ
        exact (hnoniso (i : ι) (Finset.mem_insert_of_mem i.2) j (Finset.mem_insert_self j s)
          (fun heq => hjs (heq ▸ i.2))).false φ
      -- Comaximality gives joint surjectivity of the pair, i.e. the diagonal over `insert j s`.
      have hcomax : (diagPiQuot N s).ker ⊔ (QuotientGroup.mk' (N j)).ker = ⊤ :=
        sup_ker_eq_top_of_not_le (QuotientGroup.mk' (N j)) (QuotientGroup.mk'_surjective _) hnotle
      have hpair : Function.Surjective ((diagPiQuot N s).prod (QuotientGroup.mk' (N j))) :=
        surjective_prod_of_sup_ker_eq_top _ _ ihs (QuotientGroup.mk'_surjective _) hcomax
      intro t
      obtain ⟨g, hg⟩ := hpair
        (fun i : {x // x ∈ s} => t ⟨(i : ι), Finset.mem_insert_of_mem i.2⟩,
         t ⟨j, Finset.mem_insert_self j s⟩)
      rw [MonoidHom.prod_apply, Prod.mk.injEq] at hg
      obtain ⟨hg1, hg2⟩ := hg
      refine ⟨g, funext fun i => ?_⟩
      obtain ⟨iv, hiv⟩ := i
      rw [diagPiQuot_apply]
      rcases eq_or_ne iv j with h | h
      · subst h
        rw [QuotientGroup.mk'_apply] at hg2
        exact hg2
      · have hivs : iv ∈ s := (Finset.mem_insert.mp hiv).resolve_left h
        have hval := congrFun hg1 ⟨iv, hivs⟩
        rw [diagPiQuot_apply] at hval
        exact hval

/-- **Product-of-indices bound for pairwise non-isomorphic simple quotients.** If the normal
subgroups `N i` (`i ∈ s`) have simple, pairwise non-isomorphic quotients, then
`∏_{i ∈ s} [G : N i] ≤ |G|`. This is the numerical content of the diagonal surjectivity: a
surjection
from `G` onto the product `∏_{i ∈ s} (G ⧸ N i)` forces the product's cardinality `∏_{i∈s} [G : N i]`
to be at most `|G|`. -/
theorem prod_index_le_card_of_pairwise_noniso_simpleQuotient [Finite G] (N : ι → Subgroup G)
    [∀ i, (N i).Normal] (s : Finset ι) (hsimple : ∀ i ∈ s, IsSimpleGroup (G ⧸ N i))
    (hnoniso : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → IsEmpty (G ⧸ N i ≃* G ⧸ N k)) :
    ∏ i ∈ s, (N i).index ≤ Nat.card G := by
  have hsurj := diagPiQuot_surjective N s hsimple hnoniso
  calc ∏ i ∈ s, (N i).index
      = ∏ i : {x // x ∈ s}, (N (i : ι)).index := (Finset.prod_coe_sort s _).symm
    _ = ∏ i : {x // x ∈ s}, Nat.card (G ⧸ N (i : ι)) := by simp_rw [Subgroup.index_eq_card]
    _ = Nat.card (∀ i : {x // x ∈ s}, G ⧸ N (i : ι)) := Nat.card_pi.symm
    _ ≤ Nat.card G := Nat.card_le_card_of_surjective _ hsurj

/-- **A set of normal subgroups with pairwise non-isomorphic simple quotients has cardinality at
most
`log₂|G|`.** Each simple quotient has order `≥ 2`, so `2^{#s} ≤ ∏_{i ∈ s} [G : N i] ≤ |G|`
(`prod_index_le_card_of_pairwise_noniso_simpleQuotient`), whence `#s ≤ log₂|G|`. Choosing one `N i`
per nonabelian-simple quotient *type* of `G` (so the quotients are pairwise non-isomorphic), this
bounds the number of distinct such quotient types by `log₂|G|` — the sharp type-count the
Ettinger–Høyer–Knill aggregation over quotient types needs. -/
theorem card_le_log_of_pairwise_noniso_simpleQuotient [Finite G] (N : ι → Subgroup G)
    [∀ i, (N i).Normal] (s : Finset ι) (hsimple : ∀ i ∈ s, IsSimpleGroup (G ⧸ N i))
    (hnoniso : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → IsEmpty (G ⧸ N i ≃* G ⧸ N k)) :
    s.card ≤ Nat.log 2 (Nat.card G) := by
  have hprod := prod_index_le_card_of_pairwise_noniso_simpleQuotient N s hsimple hnoniso
  have h2 : 2 ^ s.card ≤ ∏ i ∈ s, (N i).index := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod fun i hi => ?_
    have := hsimple i hi
    rw [Subgroup.index_eq_card]
    exact Finite.one_lt_card
  have hcardG : Nat.card G ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, ‹Finite G›⟩
  exact (Nat.le_log_iff_pow_le one_lt_two hcardG).mpr (h2.trans hprod)

end AxQM.Concrete
