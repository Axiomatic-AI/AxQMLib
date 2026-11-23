/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Additional API for the matrix exponential

* `Matrix.exp_smul_conj_of_conj_eq`: conjugating `P` to `Q` by a pair of mutually inverse
  matrices conjugates `exp (t • P)` to `exp (t • Q)`.
-/

public section

open NormedSpace

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- If `V` and `W` are two-sided inverses (`V * W = 1`, `W * V = 1`) and `V` conjugates `P` to `Q`
(`V * P * W = Q`), then the exponential of the scaled operator `t • P` is the exponential of the
scaled `t • Q` conjugated the other way: `exp (t • P) = W * exp (t • Q) * V`. This packages
`Matrix.exp_units_conj` with an `t • ` scalar and an equational conjugation hypothesis, so a caller
holding a conjugation identity `V * P * W = Q` (e.g. a unitary/Clifford circuit conjugating one
operator to another) obtains the exponentiated form in a single step. -/
theorem exp_smul_conj_of_conj_eq (V W P Q : Matrix m m ℂ) (hVW : V * W = 1) (hWV : W * V = 1)
    (h : V * P * W = Q) (t : ℂ) : exp (t • P) = W * exp (t • Q) * V := by
  let v : (Matrix m m ℂ)ˣ := ⟨V, W, hVW, hWV⟩
  have hQ : exp (t • Q) = V * exp (t • P) * W := by
    rw [← h, ← Matrix.smul_mul, ← Matrix.mul_smul]
    exact Matrix.exp_units_conj v (t • P)
  rw [hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWV, Matrix.one_mul, Matrix.mul_assoc, hWV,
    Matrix.mul_one]

end Matrix
