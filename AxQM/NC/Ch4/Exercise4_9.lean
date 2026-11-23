/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecomposition

/-!
# Nielsen & Chuang, Exercise 4.9 (any single-qubit unitary has the matrix form 4.12)

Explain why any single-qubit unitary may be written in the form (4.12).

Here (4.12) is the explicit `2 × 2` matrix appearing in the proof of Theorem 4.1:

`U = ⎡ e^{i(α − β/2 − δ/2)} cos(γ/2)   −e^{i(α − β/2 + δ/2)} sin(γ/2) ⎤`
`    ⎣ e^{i(α + β/2 − δ/2)} sin(γ/2)    e^{i(α + β/2 + δ/2)} cos(γ/2) ⎦`

for some real `α, β, γ, δ`. N&C obtains it as the intermediate step of Theorem 4.1: *"Since `U` is
unitary, the rows and columns of `U` are orthonormal, from which it follows that there exist real
numbers `α, β, γ` and `δ` such that [(4.12)]"*, and eq. (4.11) `U = e^{iα} R_z(β) R_y(γ) R_z(δ)`
then follows immediately by multiplying out the rotation matrices.

The statement is a fact of `2 × 2` complex linear algebra: an arbitrary
`U ∈ Matrix.unitaryGroup (Fin 2) ℂ` (N&C's definition of a single-qubit gate) equals an explicit
matrix of scalars.

## The formalisation

The explicit form (4.12) lives in `AxQM/Concrete/RotationDecomposition.lean`, alongside the
Z–Y decomposition it restates:

* `AxQM.Concrete.zyMatrixForm` — the entry-explicit matrix of eq. (4.12): the diagonal
  entries `e^{i(α ∓ β/2 ∓ δ/2)} cos(γ/2)` and off-diagonal `∓ e^{i(α ∓ β/2 ± δ/2)} sin(γ/2)`, with
  the global phase `e^{iα}` folded in.
* `AxQM.Concrete.zyMatrixForm_eq_smul_rotZ_mul_rotY_mul_rotZ` — the bridge to Theorem 4.1's
  product form: `zyMatrixForm α β γ δ = e^{iα} • (R_z(β) R_y(γ) R_z(δ))`, folding the global phase
  into each entry of the closed form `rotZ_mul_rotY_mul_rotZ`.
* `AxQM.Concrete.exists_zyMatrixForm` — **Exercise 4.9 itself**: for
  `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` there exist real `α, β, γ, δ` with `U = zyMatrixForm α β γ δ`.

The statement is for all of `U(2)` (no determinant or dimension is fixed), matching N&C's
generality. The proof reuses `exists_zy_decomposition` (Theorem 4.1) — the substance of the
exercise, that unitarity forces the entries into this shape, is discharged there — and the bridge
`zyMatrixForm_eq_smul_rotZ_mul_rotY_mul_rotZ` merely folds the global phase into each entry, giving
the entrywise matrix (4.12). This mirrors N&C's own logical order in reverse: they derive (4.12)
first and read off (4.11); the mechanised development proves (4.11) directly and expands it back
to (4.12).
-/
