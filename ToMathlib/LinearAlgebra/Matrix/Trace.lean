/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# `Matrix.trace` unfolds to a sum over the diagonal
-/

@[expose] public section

namespace Matrix

variable {n : Type*} {R : Type*} [Fintype n] [AddCommMonoid R]

theorem trace_apply (A : Matrix n n R) : trace A = ∑ i, diag A i := rfl

end Matrix
