/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DensityMatrixRealDimension

/-!
# Nielsen & Chuang, Exercise 4.46

Show describing an n-qubit density matrix requires 4^n-1 independent real numbers.

This exercise is a **linear-algebra parameter count**.

## The counting argument

A density matrix on `ℂ^d` (`d = 2ⁿ` for `n` qubits) is a `d × d` Hermitian matrix that is also
positive semidefinite with unit trace. The Hermitian matrices form a real vector space of dimension
`d²`; unit trace is a single real linear constraint (Hermitian matrices have real trace), leaving
`d² − 1` free real parameters; and positive semidefiniteness — an open inequality condition — does
not lower the count. With `d = 2ⁿ` this is `d² − 1 = 4ⁿ − 1`.

## Where it is formalised

`AxQM/Concrete/DensityMatrixRealDimension.lean`:

* `AxQM.Concrete.finrank_tracelessSelfAdjoint_matrix_two_pow` — **the exercise**: the
  traceless Hermitian `2ⁿ × 2ⁿ` matrices (the parameter space of `n`-qubit density matrices) have
  real dimension `4ⁿ − 1`.
* `AxQM.Concrete.finrank_selfAdjoint_matrix` — the real dimension of the Hermitian
  `d × d` matrices is `d²` (the general Hermitian parameter count; `4ⁿ` for `n` qubits, via
  `finrank_selfAdjoint_matrix_two_pow`).
* `AxQM.Concrete.finrank_tracelessSelfAdjoint_matrix` — the general-`d` traceless count
  `d² − 1`, from which the qubit case specialises.
* `AxQM.Concrete.realTraceOnSelfAdjoint` / `tracelessSelfAdjoint` — the real trace
  functional on the Hermitian matrices (`realTraceOnSelfAdjoint_surjective`) and its kernel, the
  traceless Hermitian "generalized Bloch vector" space cut out by the unit-trace constraint.
-/
