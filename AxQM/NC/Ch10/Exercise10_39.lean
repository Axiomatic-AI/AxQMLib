/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringBasisChange

/-!
# Nielsen & Chuang, Exercise 10.39 (Phase-gate conjugation of the Pauli matrices)

Verify phase gate conjugation SXS-dag=Y, SZS-dag=Z.

For the single-qubit **phase gate** `S = !![1, 0; 0, i]` (Nielsen & Chuang, eq. 10.90), equation
(10.91) records the action of `S` by conjugation on the Pauli matrices:

> `S X S† = Y`;   `S Z S† = Z`.  (eq. 10.91)

Each identity is an equality of concrete `2 × 2` complex matrices: the phase-gate matrix
`sMatrix = diag(1, i)` conjugating a Pauli matrix `pauliX` / `pauliZ`.

## The formalisation

The two identities of eq. (10.91) live in `AxQM/Concrete/PauliStringBasisChange.lean`,
built on the phase-gate matrix `sMatrix` (`Concrete/AxisAngleGateValues.lean`) and the Pauli
matrices (`Concrete/Pauli.lean`):

* `AxQM.Concrete.sMatrix_conj_pauliX` — `S X S† = Y` (the first identity of eq. 10.91).
* `AxQM.Concrete.sMatrix_conj_pauliZ` — `S Z S† = Z` (the second identity of eq. 10.91).

The remaining entry of the phase-gate tableau — the conjugate of `Y`, which N&C does not spell out
but which completes the action on `{X, Y, Z}` — is recorded alongside them:

* `AxQM.Concrete.sMatrix_conj_pauliY` — `S Y S† = -X`.

Together the three exhibit `S`-conjugation as the quarter-turn about the `ẑ` Bloch axis that sends
`x̂ ↦ ŷ ↦ -x̂` and fixes `ẑ`. The adjoint used is `S† = diag(1, -i)` (`sMatrix_conjTranspose`);
each identity is proved by a direct `2 × 2` entrywise computation (`fin_cases` on both indices,
`Matrix.mul_apply` + `Fin.sum_univ_two`, `Matrix.conjTranspose_apply`).

## Why this matters in Chapter 10

Eq. (10.91) is the single-qubit fact that makes the phase gate a member of the normalizer `N(Gₙ)`
of the Pauli group (N&C §10.5.3): `S` maps `Gₙ` into `Gₙ` under conjugation. Together with the
Hadamard tableau (`hadamardC_mul_pauli{X,Y,Z}_mul_hadamardC`, Exercise 4.13) and CNOT conjugation
(Exercises 10.36–10.37), it underlies the claim that `H`, `S`, and CNOT generate the whole
normalizer (Exercise 10.40 / Theorem 10.6). Independently, `sMatrix_conj_pauliX` is reused as the
core of the `Y` basis-change identity `(SH) Z (SH)† = Y` in the Hamiltonian-simulation reduction of
Exercise 4.51.
-/
