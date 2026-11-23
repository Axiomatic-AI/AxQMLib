/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ABCDecomposition

/-!
# Nielsen & Chuang, Corollary 4.2 — the ABC decomposition of a single-qubit unitary

*(N&C p. 176.)*

For single-qubit unitary U there exist A,B,C with ABC=I and U=e^{i a}AXBXC.

The statement is a pure `2 × 2` complex-matrix fact about single-qubit unitaries (membership in
`Matrix.unitaryGroup (Fin 2) ℂ`), the Pauli matrix `pauliX`, and the rotation operators
`rotY`/`rotZ`.

The formalisation is in `AxQM/Concrete/ABCDecomposition.lean`:

* `AxQM.Concrete.exists_abc_decomposition` — **Corollary 4.2**: for
  `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` there exist a real phase `α` and unitary matrices `A, B, C`
  with `A B C = 1` and `U = e^{iα} • (A X B X C)` (`X = pauliX`).

Supporting lemmas in the same file:

* `AxQM.Concrete.rotY_mul_rotY` / `rotZ_mul_rotZ` — the coordinate one-parameter group law
  `R_a(x) R_a(y) = R_a(x+y)`, and `rotY_zero` / `rotZ_zero` — `R_a(0) = I`.

## How the proof goes (N&C eq. 4.14–4.17)

The Z–Y decomposition (Theorem 4.1, `exists_zy_decomposition`) gives
`U = e^{iα} R_z(β) R_y(γ) R_z(δ)`. Taking N&C's witnesses `A = R_z(β) R_y(γ/2)`,
`B = R_y(-γ/2) R_z(-(δ+β)/2)`, `C = R_z((δ-β)/2)`:

* `A B C = I` because the inner `R_y` collapse (`R_y(γ/2) R_y(-γ/2) = I`) and the `R_z` telescope
  to `R_z(β) R_z(-β) = I` (eq. 4.14).
* Since `X² = I`, conjugating `B` by the two `X` gates and using Exercise 4.7's
  `X R_a(θ) X = R_a(-θ)` gives `X B X = R_y(γ/2) R_z((δ+β)/2)` (eq. 4.15), whence
  `A X B X C = R_z(β) R_y(γ) R_z(δ)` (eq. 4.16–4.17) and `U = e^{iα} A X B X C`.

This construction is the reason Corollary 4.2 is the "key" to controlled operations (N&C §4.3): a
controlled-`U` gate applies `A`, `B`, `C` unconditionally with the two `X` gates conditioned on the
control qubit, so no controlled rotations are needed.
-/
