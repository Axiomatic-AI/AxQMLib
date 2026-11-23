/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroupNegOne

/-!
# Nielsen & Chuang, Exercise 10.30 — `-I ∉ S` implies `±iI ∉ S`

*(N&C §10.5.1, p. 455.)*

Show that -I not in S implies +-iI not in S.

## What the exercise asks, and what is proved

In the stabilizer formalism (N&C §10.5.1), `S` is a subgroup of the `n`-qubit Pauli group `Gₙ`. A
necessary condition for `S` to stabilize a non-trivial vector space `V_S` is `-I ∉ S`; this exercise
records the companion phase-only exclusions that `-I ∉ S` forces. The Pauli group contains the four
phase-only elements `{I, iI, -I, -iI}` (the fourth roots of unity times the identity), and each of
`iI` and `-iI` squares to `-I`:

* `(iI)² = i²I = -I`,
* `(-iI)² = (-i)²I = -I`.

Since a subgroup is closed under products, if `iI ∈ S` or `-iI ∈ S` then `-I ∈ S`, contradicting the
hypothesis. Hence `-I ∉ S` implies `iI ∉ S` and `-iI ∉ S`.

The formalisation is in `AxQM/Concrete/PauliGroupNegOne.lean`, the file that develops the
structure of a Pauli subgroup with `-I ∉ S` (N&C Exercises 10.30/10.35). The group `Gₙ` is modelled
by `AxQM.Concrete.PauliGroup`, whose elements are a phase in `ZMod 4` and a Pauli-string index.

## Declarations

All in `AxQM/Concrete/PauliGroupNegOne.lean`, namespace
`AxQM.Concrete.PauliGroup`, for the `n`-qubit Pauli group `PauliGroup n`:

* `imOne`, `negImOne` — the phase-only elements `iI := (1, 0)` and `-iI := (3, 0)`.
* `pauliRep_imOne`, `pauliRep_negImOne` — faithfulness of the names: `imOne`/`negImOne` really
  represent the operators `i·I` and `-i·I` (`pauliRep (imOne n) = Complex.I • 1`, and likewise
  `-Complex.I • 1`), mirroring `pauliRep_negOne : pauliRep (negOne n) = -1`.
* `imOne_mul_self`, `negImOne_mul_self` — the crux `(iI)² = -I` and `(-iI)² = -I`, i.e.
  `imOne * imOne = negOne` and `negImOne * negImOne = negOne`.
* `imOne_notMem_of_negOne_notMem` — Exercise 10.30, the `iI` half: for `S` a subgroup with
  `negOne n ∉ S`, `imOne n ∉ S`.
* `negImOne_notMem_of_negOne_notMem` — Exercise 10.30, the `-iI` half: `negImOne n ∉ S`.

Together the two `notMem` theorems are N&C's `±iI ∉ S`.

## Faithfulness

* **The exact statement, in full generality.** N&C's `S` is an arbitrary subgroup of `Gₙ`; the two
  theorems quantify over an arbitrary `S : Subgroup (PauliGroup n)` with the sole hypothesis
  `-I ∉ S` (`negOne n ∉ S`), and conclude exactly `iI ∉ S` and `-iI ∉ S`. No dimension is
  specialised and no extra hypothesis is added.
* **Not a weakening.** The proof uses only subgroup closure (`Subgroup.mul_mem`) and the group's
  phase arithmetic, exactly the argument in the text; `pauliRep_imOne`/`pauliRep_negImOne` pin the
  named elements to the operators `iI`/`-iI` so the statement genuinely concerns the book's objects.
-/
