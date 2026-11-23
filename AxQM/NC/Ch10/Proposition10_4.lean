/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerGeneratorFlip

/-!
# Nielsen & Chuang, Proposition 10.4 — flipping a single stabilizer generator

*(N&C §10.5.1, p. 458.)*

For independent commuting S with -I not in S, exists g in Gn with g gi g-dag=-gi, g gj g-dag=gj
(j!=i).

## Context

This "innocuous looking" proposition is the workhorse behind the stabilizer-code dimension count:
Proposition 10.5 uses it to show that each independent generator halves the dimension of the
stabilized subspace `V_S`, so `V_S` is `2^k`-dimensional for `n - k` generators. N&C's proof passes
to the **check matrix** `G` (rows `r(gⱼ)` are the `(x | z)` symplectic representation): the rows are
linearly independent by Proposition 10.3, so the system `G Λ x = eᵢ` (with `Λ = [[0, I], [I, 0]]`)
has a solution `x`; taking `g` with `r(g) = xᵀ` makes `g` anticommute with `gᵢ` and commute with
every other `gⱼ`, and conjugation by `g` then flips `gᵢ` and fixes the rest.

## Content

The mathematics is `n`-qubit Pauli-string matrices (`Concrete.pauliString`, indexed by
`Fin n → Fin 4`), their commutation/conjugation algebra, and the binary symplectic form on check
rows over `ZMod 2`. Compare Exercise 10.33 (`AxQM/Concrete/PauliStringCommutation.lean`) and the
Proposition 10.3 check-row infrastructure (`AxQM/Concrete/CheckMatrix.lean`).

## Faithfulness

The formalisation works with **phase-free** Pauli strings, which are automatically Hermitian
involutions. This is faithful to N&C on two counts, both spelled out in the source file's module
docstring:

* N&C's hypothesis `-I ∉ S` forces every element of `S` — in particular every generator — to
  square to `I` and hence to be a Hermitian involution (Exercises 10.34/10.35). That per-generator
  involution property is all the proof uses, and phase-free Pauli strings have it unconditionally,
  so no `-I ∉ S` hypothesis is carried. (This does not claim phase-free generators avoid `-I` as a
  group — e.g. `(P_X P_Z)² = -I` — which the proof never needs.)
* N&C's hypothesis "independent generators" is, by Proposition 10.3, **equivalent** (in the
  `-I ∉ S` world) to "the check-matrix rows are `ZMod 2`-linearly independent" — precisely the form
  the proof consumes at its first step. The theorem is stated over that equivalent (not weaker)
  hypothesis. The conjugation `g gⱼ g†` is written with the Hermitian adjoint `star (pauliString p)`
  so the conclusion is literally N&C's `g gⱼ g† = ±gⱼ`.

## Formalisation

The formalisation is in `AxQM/Concrete/StabilizerGeneratorFlip.lean` (namespace
`AxQM.Concrete`). It uses the Exercise 10.33 / Proposition 10.3 results `pauliString_mul_comm_sign`,
`pauliString_mul_self`, `pauliAnticommCount`, `checkRow` and `pauliBit`.

* `exists_pauliString_conj_flip` — **Proposition 10.4 itself**: for phase-free generators
  `g : Fin l → (Fin n → Fin 4)` with `ZMod 2`-linearly independent check rows and a fixed `i`, there
  is a Pauli string `p` with `P_p P_{gᵢ} P_p† = -P_{gᵢ}` and `P_p P_{gⱼ} P_p† = P_{gⱼ}` for `j ≠ i`.
* `pauliString_conj`, `pauliString_conj_of_even`, `pauliString_conj_of_odd` — **the conjugation
  mechanism**: conjugating `P_h` by `P_p` multiplies it by the commutation sign
  `(-1)^{pauliAnticommCount p h}`, fixing `P_h` when they commute (even) and flipping it when they
  anticommute (odd).
* `checkSymplectic`, `checkSymplectic_apply`, `checkSymplectic_checkRow`,
  `checkSymplectic_nondegenerate` — the binary symplectic form `r(g) Λ r(g')ᵀ` on check rows as a
  nondegenerate `ZMod 2`-bilinear form, identified with `(pauliAnticommCount g h : ZMod 2)`; its
  nondegeneracy is the "`G Λ x = eᵢ` is solvable" step.
* `bitToPauli`, `pauliBit_bitToPauli`, `checkRow_surjective` — surjectivity of the check-row map,
  realizing the solution vector as an actual Pauli string.

See the module docstring of `AxQM/Concrete/StabilizerGeneratorFlip.lean` for the full rationale.
-/
