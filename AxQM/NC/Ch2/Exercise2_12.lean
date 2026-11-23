/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.NonDiagonalizableMatrixExample

/-!
# Nielsen & Chuang, Exercise 2.12

Prove the matrix [[1,0],[1,1]] is not diagonalizable.

N&C (p. 68) define an operator to be diagonalizable when it admits a *diagonal
representation* with an **orthonormal** eigenbasis. The formalisation refutes the
strictly stronger property of being similar to a diagonal matrix at all (no
invertible `P` and diagonal `diagonal d` with `M = P * diagonal d * P⁻¹`); since
an orthonormal eigenbasis is in particular an eigenbasis, this refutes N&C's
notion a fortiori. See the module docstring of the file below for the full
discussion and the nilpotency argument.

The formalisation is in
`AxQM/Concrete/NonDiagonalizableMatrixExample.lean`:

* `AxQM.Concrete.shearMatrix` — the matrix `!![1, 0; 1, 1]` of N&C
  (2.31), a complex `2 × 2` shear (unipotent) matrix.
* `AxQM.Concrete.shearMatrix_ne_one` — `shearMatrix ≠ 1`.
* `AxQM.Concrete.shearMatrix_sub_one_sq` — `(shearMatrix - 1) ^ 2 = 0`,
  the nonzero nilpotency driving the argument.
* `AxQM.Concrete.shearMatrix_not_diagonalizable` — the exercise's claim:
  `shearMatrix` is not similar to any diagonal matrix.
-/
