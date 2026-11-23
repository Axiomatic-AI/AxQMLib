/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroup
import ToMathlib.GroupTheory.Subgroup.Centralizer

/-!
# Concrete: normalizer and centralizer of a Pauli subgroup (Nielsen & Chuang, Exercises 10.43–10.44)

This file formalises Nielsen & Chuang **Exercise 10.43** (p. 465) and **Exercise 10.44** (p. 466),

Show S subset N(S) for any subgroup S of Gn.

where, in the notation of N&C §10.5.5, `N(S)` — the **normalizer** of `S` — "is defined to consist
of all elements `E` of `Gₙ` such that `E g E† ∈ S` for all `g ∈ S`", and `Z(S)` — the
**centralizer** of `S` — is "the set of `E ∈ Gₙ` such that `Eg = gE` for all `g ∈ S`". Everything
here is stated for the abstract Pauli group `PauliGroup n`, its subgroups, and raw matrices.
These are the statements of N&C Exercises 10.43 and 10.44
(`AxQM/NC/Ch10/Exercise10_43.lean` and `AxQM/NC/Ch10/Exercise10_44.lean`).

## Modelling `N(S)` and the rôle of the dagger

`Gₙ` is modelled abstractly as the group `PauliGroup n`, faithfully represented on matrices by
`PauliGroup.toMat`. The fact linking N&C's dagger definition to plain group theory is that **the
adjoint of a Pauli-group element is its inverse**: `(toMat E)ᴴ = toMat E⁻¹` (`PauliGroup.toMat_inv`;
every `toMat E` is unitary). Hence conjugation by the dagger is conjugation by the group inverse —
`toMat (E g E⁻¹) = (toMat E)(toMat g)(toMat E)ᴴ` (`PauliGroup.toMat_conjugate`) — so N&C's condition
"`E g E† ∈ S` for all `g ∈ S`" is exactly membership of `E` in the group-theoretic normalizer
`N(S) = Subgroup.normalizer S`. This is the same identification the stabilizer-code development
already uses (`Concrete/StabilizerErrorCorrection.lean`, `codeProjector_satisfiesKL`), where
`N(S) := Subgroup.normalizer ↑S`; the two lemmas `mem_normalizer_conjTranspose` /
`mem_stabilizer_conjTranspose` below record that this really is N&C's dagger normalizer, so the
group-theoretic statement is a faithful — not merely convenient — reading of the exercise.

## Modelling `Z(S)` and why `-I ∉ S` forces `N(S) = Z(S)`

The centralizer is modelled by the library's `Z(S) := Subgroup.centralizer ↑S`, whose membership
`Subgroup.mem_centralizer_iff` is exactly N&C's condition "`g E = E g` for all `g ∈ S`". One
inclusion, `Z(S) ⊆ N(S)`, holds for every subgroup (`Subgroup.centralizer_le_normalizer`): a
commuting `E` a fortiori normalizes. The reverse inclusion is where `-I ∉ S` enters, and it rests on
the Pauli **commute-or-anticommute dichotomy**: any two Pauli-group elements either commute or
their operators anticommute (`PauliGroup.toMat_anticomm_of_ne_mul_comm`). Lifted to the group
(`PauliGroup.commute_or_conjugate_eq_negOne_mul`), this says that for any `E, g` either `E g = g E`
or `E g E⁻¹ = (-I) g`. Now take `E ∈ N(S)` and `g ∈ S`. If they did not commute, then
`E g E⁻¹ = (-I) g ∈ S` (normalizer), so `-I = ((-I) g) g⁻¹ ∈ S` by closure — contradicting `-I ∉ S`.
Hence `E` commutes with every `g ∈ S`, i.e. `E ∈ Z(S)`, giving `N(S) ⊆ Z(S)` and therefore equality.

## What is proved

* `PauliGroup.toMat_conjugate` — the dagger/inverse bridge:
  `toMat (g a g⁻¹) = (toMat g)(toMat a)(toMat g)ᴴ`.
* `stabilizer_le_normalizer` — **Exercise 10.43** (group form): `S ≤ N(S)`, i.e. every subgroup of
  `Gₙ` lies in its normalizer.
* `mem_normalizer_conjTranspose` — the library's `N(S) = Subgroup.normalizer S` *is* N&C's dagger
  normalizer: for `E ∈ N(S)` and `g ∈ S`, the operator `E g E† = (toMat E)(toMat g)(toMat E)ᴴ`
  equals `toMat h` for some `h ∈ S`.
* `mem_stabilizer_conjTranspose` — **Exercise 10.43** (N&C's literal dagger form): for `E ∈ S` and
  `g ∈ S`, `E g E† ∈ S`, i.e. `(toMat E)(toMat g)(toMat E)ᴴ = toMat h` for some `h ∈ S`.
* `PauliGroup.toMat_negOne` — the operator of `-I` is `-1`: `toMat (negOne n) = -1`.
* `PauliGroup.commute_or_conjugate_eq_negOne_mul` — the group-level commute-or-negate dichotomy:
  `E g = g E ∨ E g E⁻¹ = (-I) g`, the engine of Exercise 10.44.
* `normalizer_eq_centralizer_of_negOne_notMem` — **Exercise 10.44**: for `S ≤ Gₙ` with `-I ∉ S`,
  `N(S) = Z(S)` (`Subgroup.normalizer ↑S = Subgroup.centralizer ↑S`).
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Conjugation is dagger-conjugation.** For Pauli-group elements the adjoint is the inverse
(`PauliGroup.toMat_inv`), so the operator of the group conjugate `g a g⁻¹` is the matrix conjugation
of `toMat a` by the *unitary* `toMat g`: `toMat (g a g⁻¹) = (toMat g)(toMat a)(toMat g)ᴴ`. This is
the bridge identifying N&C's dagger normalizer with the group-theoretic normalizer. -/
theorem PauliGroup.toMat_conjugate (g a : PauliGroup n) :
    (g * a * g⁻¹).toMat = g.toMat * a.toMat * g.toMat.conjTranspose := by
  rw [PauliGroup.toMat_mul, PauliGroup.toMat_mul, PauliGroup.toMat_inv]

/-- **Exercise 10.43** (group form). Every subgroup `S` of the Pauli group `Gₙ` is contained in its
normalizer `N(S) = Subgroup.normalizer S`. This is the exercise in the library's
`Subgroup.normalizer` reading of `N(S)` (used throughout the stabilizer-code development); the two
`*_conjTranspose` lemmas record that it coincides with N&C's dagger normalizer. -/
theorem stabilizer_le_normalizer (S : Subgroup (PauliGroup n)) :
    S ≤ Subgroup.normalizer (S : Set (PauliGroup n)) :=
  Subgroup.le_normalizer

/-- The library's normalizer `N(S) = Subgroup.normalizer S` is N&C's **dagger** normalizer: an
element `E ∈ N(S)` sends each `g ∈ S` to `E g E† ∈ S` under conjugation. Concretely
`(toMat E)(toMat g)(toMat E)ᴴ = toMat h` for some `h ∈ S`, using `E g E⁻¹ ∈ S` (normalizer
membership) and `toMat (E g E⁻¹) = (toMat E)(toMat g)(toMat E)ᴴ` (`PauliGroup.toMat_conjugate`). -/
theorem mem_normalizer_conjTranspose {S : Subgroup (PauliGroup n)} {E : PauliGroup n}
    (hE : E ∈ Subgroup.normalizer (S : Set (PauliGroup n))) {g : PauliGroup n} (hg : g ∈ S) :
    ∃ h ∈ S, E.toMat * g.toMat * E.toMat.conjTranspose = h.toMat := by
  refine ⟨E * g * E⁻¹, (Subgroup.mem_normalizer_iff.mp hE g).mp hg, ?_⟩
  rw [PauliGroup.toMat_conjugate]

/-- **Exercise 10.43** (N&C's literal form). For a subgroup `S` of `Gₙ`, every `E ∈ S` normalizes
`S` in N&C's sense: `E g E† ∈ S` for all `g ∈ S`. At the matrix level,
`(toMat E)(toMat g)(toMat E)ᴴ = toMat h` for some `h ∈ S`. This is `S ⊆ N(S)` with `N(S)` read as
N&C's dagger normalizer, obtained by feeding `stabilizer_le_normalizer` into
`mem_normalizer_conjTranspose`. -/
theorem mem_stabilizer_conjTranspose {S : Subgroup (PauliGroup n)} {E : PauliGroup n} (hE : E ∈ S)
    {g : PauliGroup n} (hg : g ∈ S) :
    ∃ h ∈ S, E.toMat * g.toMat * E.toMat.conjTranspose = h.toMat :=
  mem_normalizer_conjTranspose (stabilizer_le_normalizer S hE) hg

/-! ### Exercise 10.44: `N(S) = Z(S)` for a subgroup with `-I ∉ S` -/

/-- **The operator of `-I` is `-1`.** The Pauli-group element `negOne n = (2, 0)` represents
`i² • P₀ = (-1) • I = -I` in the matrix ring. This is the `toMat`-interface form of the bundled
`PauliGroup.pauliRep_negOne` (`⇑pauliRep` is definitionally `toMat`). -/
theorem PauliGroup.toMat_negOne : (PauliGroup.negOne n).toMat = -1 :=
  PauliGroup.pauliRep_negOne

/-- **Commute-or-negate dichotomy for Pauli-group conjugation.** For any two Pauli-group elements
`E, g`, either they commute (`E g = g E`) or conjugation by `E` negates `g`: `E g E⁻¹ = (-I) g`.
Pauli operators either commute or anticommute (`PauliGroup.toMat_anticomm_of_ne_mul_comm`); in the
anticommuting case the dagger-conjugation bridge `toMat_conjugate` gives
`(toMat E)(toMat g)(toMat E)ᴴ = -(toMat g)`, using unitarity of `toMat E`
(`toMat_mul_conjTranspose`) and the operator of `-I` (`toMat_negOne`); faithfulness
(`toMat_injective`) lifts the identity back to the group. This is the engine behind `N(S) = Z(S)`
for `-I ∉ S`. -/
theorem PauliGroup.commute_or_conjugate_eq_negOne_mul (E g : PauliGroup n) :
    E * g = g * E ∨ E * g * E⁻¹ = PauliGroup.negOne n * g := by
  by_cases h : E * g = g * E
  · exact Or.inl h
  refine Or.inr (PauliGroup.toMat_injective ?_)
  rw [PauliGroup.toMat_conjugate, PauliGroup.toMat_mul, PauliGroup.toMat_negOne,
    PauliGroup.toMat_anticomm_of_ne_mul_comm E g h, neg_mul, mul_assoc,
    PauliGroup.toMat_mul_conjTranspose, mul_one, neg_one_mul]

/-- **Exercise 10.44.** For any subgroup `S` of the Pauli group `Gₙ` with `-I ∉ S`, the normalizer
and the centralizer coincide: `N(S) = Z(S)`, i.e.
`Subgroup.normalizer ↑S = Subgroup.centralizer ↑S`.

The inclusion `Z(S) ≤ N(S)` is general (`Subgroup.centralizer_le_normalizer`). For `N(S) ≤ Z(S)`,
take `E ∈ N(S)` and `g ∈ S`; by the commute-or-negate dichotomy
(`PauliGroup.commute_or_conjugate_eq_negOne_mul`) either `E g = g E` (done), or `E g E⁻¹ = (-I) g`,
which lies in `S` because `E ∈ N(S)` — but then `-I = ((-I) g) g⁻¹ ∈ S` by closure, contradicting
`-I ∉ S`. Combined with the dagger characterization of `N(S)` from Exercise 10.43
(`mem_normalizer_conjTranspose`) and `Subgroup.mem_centralizer_iff` (which is N&C's `Eg = gE`
condition on `Z(S)`), this is a faithful reading of N&C's `N(S) = Z(S)`. -/
theorem normalizer_eq_centralizer_of_negOne_notMem {S : Subgroup (PauliGroup n)}
    (hS : PauliGroup.negOne n ∉ S) :
    Subgroup.normalizer (S : Set (PauliGroup n))
      = Subgroup.centralizer (S : Set (PauliGroup n)) := by
  refine le_antisymm ?_ (Subgroup.centralizer_le_normalizer (S : Set (PauliGroup n)))
  intro E hE
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rcases PauliGroup.commute_or_conjugate_eq_negOne_mul E g with hc | hconj
  · exact hc.symm
  · exfalso
    have hmem : E * g * E⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hE g).mp hg
    rw [hconj] at hmem
    exact hS (by simpa using S.mul_mem hmem (S.inv_mem hg))

/-- **Anticommuting with an element of `S` puts you outside `N(S)`** (for a genuine stabilizer,
`-I ∉ S`). If some `g ∈ S` fails to commute with `p` (`g * p ≠ p * g`), then `p ∉ N(S)`: since
`N(S) = Z(S)` (`normalizer_eq_centralizer_of_negOne_notMem`, Exercise 10.44), membership in `N(S)`
would force `p` to commute with every element of `S`, `g` included. A convenient packaging of the
`N(S) = Z(S)` collapse for detecting non-normalizing elements by a single anticommutation. -/
theorem notMem_normalizer_of_mem_of_ne_comm {S : Subgroup (PauliGroup n)}
    (hS : PauliGroup.negOne n ∉ S) {g p : PauliGroup n} (hg : g ∈ S) (hne : g * p ≠ p * g) :
    p ∉ Subgroup.normalizer S := by
  rw [normalizer_eq_centralizer_of_negOne_notMem hS]
  intro hp
  rw [Subgroup.mem_centralizer_iff] at hp
  exact hne (hp g hg)

end AxQM.Concrete
