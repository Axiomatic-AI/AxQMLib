/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecompositionXY

/-!
# Nielsen & Chuang, Exercise 4.10 (X–Y decomposition of a single-qubit unitary)

Give an X-Y decomposition analogous to Theorem 4.1 using R_x instead of R_z.

Theorem 4.1 is the Z–Y decomposition `U = e^{iα} R_z(β) R_y(γ) R_z(δ)` (eq. 4.11). The analogous
X–Y decomposition, obtained by replacing `R_z` with `R_x`, is: every single-qubit unitary `U`
factors as

`U = e^{iα} R_x(β) R_y(γ) R_x(δ)`

for some real numbers `α, β, γ, δ`.

As with Theorem 4.1, the statement is a pure fact of `2 × 2` complex linear algebra — an
arbitrary `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` (N&C's definition of a single-qubit gate) factors as
a phase times a product of the rotations `R_x`, `R_y`.

## The formalisation

The formalisation is in `AxQM/Concrete/RotationDecompositionXY.lean`, using the
Z–Y decomposition (`AxQM/Concrete/RotationDecomposition.lean`, Theorem 4.1) and the Hadamard matrix
(`AxQM/Concrete/Hadamard.lean`):

* `AxQM.Concrete.hadamardC_mul_rotZ_mul_hadamardC` — `H R_z(θ) H = R_x(θ)` (Hadamard
  conjugation exchanges the `x̂`/`ẑ` axes).
* `AxQM.Concrete.hadamardC_mul_rotY_mul_hadamardC` — `H R_y(θ) H = R_y(-θ)` (Hadamard
  conjugation flips the `ŷ` axis).
* `AxQM.Concrete.exists_xy_decomposition` — **Exercise 4.10 itself**: for
  `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` there exist real `α, β, γ, δ` with
  `U = e^{iα} • (R_x(β) R_y(γ) R_x(δ))`.

The statement is for all of `U(2)` (no determinant or dimension is fixed), matching N&C's
generality. The proof reduces to Theorem 4.1 rather than repeating its entrywise angle extraction:
the Hadamard gate `H` is an involution exchanging the `x̂`/`ẑ` axes and flipping `ŷ`, so `H U H` is
again unitary and its Z–Y decomposition `H U H = e^{iα} R_z(β) R_y(γ) R_z(δ)`, conjugated back by
`H` and pushed through each factor, becomes `U = e^{iα} R_x(β) R_y(-γ) R_x(δ)` — the X–Y
decomposition with middle angle `-γ`.
-/
