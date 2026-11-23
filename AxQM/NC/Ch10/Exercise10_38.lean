/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGenerators

/-!
# Nielsen & Chuang, Exercise 10.38 — a two-qubit unitary is fixed up to a global phase by its
conjugation of `Z₁, Z₂, X₁, X₂`

*(N&C §10.5.1, p. 461.)*

If two-qubit unitaries U,V conjugate Z1,Z2,X1,X2 identically then U=V.

## What the exercise asks, and what is proved

N&C motivate the exercise with the swap circuit (Figure 10.8): a circuit is shown to *implement* the
swap by checking how it conjugates the four two-qubit generators `Z₁, Z₂, X₁, X₂`. The exercise
abstracts this: agreement on those four generators pins the unitary down. The four generators are

* `X₁ = X ⊗ I`, `X₂ = I ⊗ X` — Pauli `X` on the first, resp. second, qubit;
* `Z₁ = Z ⊗ I`, `Z₂ = I ⊗ Z` — Pauli `Z` on the first, resp. second, qubit,

and they suffice because the `16` two-qubit Pauli strings are all products of them up to phase
(`Y = i X Z`), so a unitary conjugating each generator identically conjugates *every* Pauli string
identically, hence agrees with the other unitary on a spanning set of operators.

**A fidelity point.** Taken literally, "`U = V`" is *false*: conjugation ignores a global phase
(`U` and `c • U` with `‖c‖ = 1` act identically), so `U` can only be pinned down up to a unit
scalar. This is precisely the "up to a global phase" that N&C itself states one line later in
Theorem 10.6 (p. 461). The faithful theorem therefore concludes `U = c • V` with `‖c‖ = 1`, and the
companion result records that this phase genuinely cannot be removed.

## Declarations

All in `AxQM/Concrete/PauliNormalizerGenerators.lean`, namespace `AxQM.Concrete`:

* `unitary_eq_smul_of_conj_twoQubitGenerators` — **the exercise itself.** If unitaries `U, V` on two
  qubits conjugate `X₁ = pauliString (xGenPauli 0)`, `X₂ = pauliString (xGenPauli 1)`,
  `Z₁ = pauliString (zGenPauli 0)`, `Z₂ = pauliString (zGenPauli 1)` identically, then
  `∃ c, ‖c‖ = 1 ∧ U = c • V`. It is the `n = 2` instance of the multi-qubit generator-determinacy
  lemma below.
* `exists_ne_unitary_conj_twoQubitGenerators_eq` — **the global phase is necessary.** There exist
  distinct two-qubit unitaries (`1` and `-1`) conjugating all four generators identically, so the
  conclusion cannot be strengthened to the literal `U = V`.

The substantive proof is the shared development of N&C Theorem 10.6 / Exercise
10.40 (all in `AxQM/Concrete/`):

* `unitary_eq_smul_of_conj_generators` — the general `n`-qubit result: a unitary is determined up to
  a global phase by how it conjugates the `2n` generators `Xᵢ, Zᵢ`.
* `unitary_eq_smul_of_conj_pauliString_eq` — agreement on *all* Pauli strings forces equality up to
  a phase; `exists_smul_one_of_commute_pauliString` (the Pauli commutant is the scalars, via
  `Matrix.center_eq_scalar_image`) is its engine.
* `pauliString_peel_wire`, `pauliString_yGenPauli_eq_smul_mul` — express any Pauli string through
  the `X`/`Z` generators (`Y = i X Z`, wire-by-wire peeling).

## Faithfulness

* **Exact hypotheses.** The four conjugation hypotheses are stated for the exact two-qubit
  generators `Z₁, Z₂, X₁, X₂` (as `pauliString (xGenPauli i)` / `(zGenPauli i)`, `i ∈ {0, 1}` = the
  two wires), matching the exercise verbatim; no extra assumption is added.
* **Not a weakening.** `U, V` range over genuine unitaries; the conclusion `U = c • V` (`‖c‖ = 1`)
  is the strongest *true* form of N&C's "`U = V`" (see the fidelity point above), and
  `exists_ne_unitary_conj_twoQubitGenerators_eq` proves it cannot be strengthened further. The
  result is a specialisation of the strictly more general theorem
  (`unitary_eq_smul_of_conj_generators`, all `n`), not a special-cased reproof.
-/
