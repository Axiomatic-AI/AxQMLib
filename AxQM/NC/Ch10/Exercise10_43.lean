/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliSubgroupNormalizer

/-!
# Nielsen & Chuang, Exercise 10.43 — a subgroup lies in its normalizer, `S ⊆ N(S)`

*(N&C §10.5.5, p. 465.)*

Show S subset N(S) for any subgroup S of Gn.

## What the exercise asks

In N&C's setup (p. 465) the **normalizer** `N(S)` of a subgroup `S ≤ Gₙ` "is defined to consist of
all elements `E` of `Gₙ` such that `E g E† ∈ S` for all `g ∈ S`". The exercise asks for the
containment `S ⊆ N(S)`: every element of `S` normalizes `S`. This underlies the very next exercise
(`N(S) = Z(S)` for `-I ∉ S`, Ex 10.44) and Theorem 10.8's error-correction condition `E†E ∉ N(S)−S`.

The content is the general group-theoretic fact that a subgroup lies in its normalizer, specialised
to `Gₙ`, together with the one physical wrinkle that makes N&C's *dagger* definition of `N(S)`
coincide with the group normalizer: for a Pauli-group element the adjoint **is** the inverse
(`(toMat E)ᴴ = toMat E⁻¹`, every `toMat E` is unitary), so `E g E† = E g E⁻¹` and N&C's condition
`E g E† ∈ S` is exactly `E g E⁻¹ ∈ S`, i.e. `E ∈ Subgroup.normalizer S`. For `E ∈ S` this holds by
closure of the subgroup under products and inverses. The core fact is the Mathlib lemma
`Subgroup.le_normalizer`, but N&C's instance is about `Gₙ` and its dagger.

## Declarations

All in `AxQM/Concrete/PauliSubgroupNormalizer.lean`, namespace `AxQM.Concrete`:

* `stabilizer_le_normalizer` — **the exercise** (group form): `S ≤ Subgroup.normalizer ↑S` for any
  `S : Subgroup (PauliGroup n)`. This is `S ⊆ N(S)` in the library's
  `N(S) := Subgroup.normalizer ↑S` reading — the same reading the stabilizer-code development uses
  (`AxQM/Concrete/StabilizerErrorCorrection.lean`).
* `mem_stabilizer_conjTranspose` — **the exercise** (N&C's literal dagger form): for `E ∈ S` and
  `g ∈ S`, `(toMat E)(toMat g)(toMat E)ᴴ = toMat h` for some `h ∈ S`, i.e. `E g E† ∈ S`.

Supporting the identification of the two readings:

* `PauliGroup.toMat_conjugate` — `toMat (E g E⁻¹) = (toMat E)(toMat g)(toMat E)ᴴ`: group conjugation
  is dagger-conjugation, since `(toMat E)ᴴ = toMat E⁻¹` (`PauliGroup.toMat_inv`).
* `mem_normalizer_conjTranspose` — every `E ∈ Subgroup.normalizer ↑S` satisfies N&C's `E g E† ∈ S`
  for `g ∈ S`, so `Subgroup.normalizer ↑S` really is N&C's dagger normalizer `N(S)`.

## Faithfulness

* **Exact statement.** `S` ranges over arbitrary subgroups of `Gₙ` (`Subgroup (PauliGroup n)`, no
  `-I ∉ S` or independence assumption), matching "any subgroup `S` of `Gₙ`" verbatim.
* **Not a weakening.** `N(S)` is not silently replaced by the abstract group normalizer:
  `mem_normalizer_conjTranspose` / `mem_stabilizer_conjTranspose` prove that the
  `Subgroup.normalizer` used here is exactly N&C's set of `E` with `E g E† ∈ S` for all `g ∈ S`
  (via `PauliGroup.toMat_inv`, adjoint = inverse), so the group-theoretic `S ≤ N(S)` is a faithful
  reading of the exercise, not a convenient substitute.
-/
