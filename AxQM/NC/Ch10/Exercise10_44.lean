/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliSubgroupNormalizer

/-!
# Nielsen & Chuang, Exercise 10.44 — the normalizer equals the centralizer, `N(S) = Z(S)`

*(N&C §10.5.5, p. 466.)*

Show N(S)=Z(S) for any subgroup S of Gn not containing -I.

## What the exercise asks

In N&C's setup (p. 465–466), for a subgroup `S ≤ Gₙ`:

* the **normalizer** `N(S)` "is defined to consist of all elements `E` of `Gₙ` such that
  `E g E† ∈ S` for all `g ∈ S`", and
* the **centralizer** `Z(S)` is "the set of `E ∈ Gₙ` such that `Eg = gE` for all `g ∈ S`".

Always `Z(S) ⊆ N(S)`. The exercise is the reverse inclusion `N(S) ⊆ Z(S)` under the standing
stabilizer hypothesis `-I ∉ S`, giving `N(S) = Z(S)`. This is exactly the distinction that matters
for Theorem 10.8's error-correction condition `E†E ∉ N(S) − S`: under `-I ∉ S`, "commutes with all
of `S`" and "normalizes `S`" are the same set of operators.

The physical content is the Pauli **commute-or-anticommute dichotomy**. For `E ∈ N(S)` and `g ∈ S`,
either `E g = g E` (so `E ∈ Z(S)`), or `E` and `g` anticommute and `E g E† = -g`; but `E g E† ∈ S`
and `g ∈ S` would then force `-I = (-g) g⁻¹ ∈ S`, contradicting `-I ∉ S`. So the anticommuting case
never occurs and `N(S) = Z(S)`.

## Declarations

All in `AxQM/Concrete/PauliSubgroupNormalizer.lean` (co-located with Exercise 10.43),
namespace `AxQM.Concrete`:

* `normalizer_eq_centralizer_of_negOne_notMem` — **the exercise**: for `S : Subgroup (PauliGroup n)`
  with `PauliGroup.negOne n ∉ S`,
  `Subgroup.normalizer ↑S = Subgroup.centralizer ↑S`, i.e. `N(S) = Z(S)`.

Supporting declarations:

* `PauliGroup.commute_or_conjugate_eq_negOne_mul` — the group-level commute-or-negate dichotomy:
  for any `E, g : PauliGroup n`, `E * g = g * E ∨ E * g * E⁻¹ = negOne n * g`. The engine of the
  exercise, lifting the operator dichotomy `PauliGroup.toMat_anticomm_of_ne_mul_comm` to the group.
* `PauliGroup.toMat_negOne` — the operator of `-I` is `-1`: `(negOne n).toMat = -1`.

## Faithfulness

* **Exact statement.** `S` ranges over arbitrary subgroups of `Gₙ` (`Subgroup (PauliGroup n)`), with
  the single hypothesis `-I ∉ S` (`PauliGroup.negOne n ∉ S`), matching "any subgroup `S` of `Gₙ` not
  containing `-I`" verbatim.
* **Both defining conditions are the N&C ones.** `Z(S) := Subgroup.centralizer ↑S` has membership
  `Subgroup.mem_centralizer_iff`, exactly N&C's "`Eg = gE` for all `g ∈ S`"; and
  `N(S) := Subgroup.normalizer ↑S` is N&C's dagger normalizer via Exercise 10.43's
  `mem_normalizer_conjTranspose` (`E g E† ∈ S` for all `g ∈ S`). So the subgroup equality is a
  faithful reading of `N(S) = Z(S)`, not a convenient group-theoretic substitute.
* **Not a weakening.** The `-I ∉ S` hypothesis is load-bearing (it is precisely what excludes the
  anticommuting case); it is not dropped, and no extra hypothesis (independence, commutativity of
  generators) is smuggled in.
-/
