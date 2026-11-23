/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Complex.Circle

/-!
# Concrete: unit-modulus arithmetic for `e^{iφ}`

A single shared home for the `star (e^{iφ}) · e^{iφ} = 1` form of the unit-modulus fact — the shape
consumed when proving a *diagonal* matrix with `e^{iφ}` entries is unitary
(`Matrix.mem_unitaryGroup` reduces to `star · = 1` on each diagonal entry). Mathlib packages the
**norm** form
(`Complex.nnnorm_exp_ofReal_mul_I : ‖e^{iφ}‖₊ = 1`) but not this `star`-product form, so this file
provides it once here rather than re-deriving it per consumer.

It is used by `LinearOpticalElement` and the multiply-controlled single-qubit reductions of
Exercise 4.43.
-/

namespace AxQM.Concrete

/-- The phase `e^{iφ}` has unit modulus, in the `star`-product form used for diagonal unitarity:
`conj(e^{iφ}) · e^{iφ} = 1`. Proved via `Complex.exp_conj` (`conj (e^{iφ}) = e^{-iφ}`) and
`e^{-iφ} · e^{iφ} = e^{0} = 1`. -/
theorem star_exp_ofReal_mul_I_mul_self (φ : ℝ) :
    star (Complex.exp ((φ : ℂ) * Complex.I)) * Complex.exp ((φ : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add,
    show (φ : ℂ) * (-Complex.I) + (φ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]

end AxQM.Concrete
