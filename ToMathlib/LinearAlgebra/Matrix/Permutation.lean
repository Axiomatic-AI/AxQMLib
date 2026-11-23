/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Additional API for permutation matrices

* `Matrix.permMatrix_eq_of_ite`: `σ.permMatrix R` is the `0`/`1` indicator matrix of `σ i = j`.
-/

public section

open Equiv

namespace Matrix

variable {n R : Type*} [DecidableEq n] (σ : Perm n)

/-- The permutation matrix `permMatrix R σ` is the `0`/`1` matrix whose `(i, j)` entry is `1`
exactly when `σ i = j`: it is `Matrix.of` applied to that indicator. -/
theorem permMatrix_eq_of_ite [Zero R] [One R] :
    (Matrix.of fun i j => if σ i = j then (1 : R) else 0) = σ.permMatrix R := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

end Matrix
