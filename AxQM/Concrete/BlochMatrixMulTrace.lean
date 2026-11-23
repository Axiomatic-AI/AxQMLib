/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix

/-!
# Concrete: the trace of a product of two Bloch matrices

Pure matrix algebra. For real
three-vectors `r`, `s` the trace of the product of the two Bloch matrices
`blochMatrix r = ½(I + r·σ)` and `blochMatrix s = ½(I + s·σ)` is

`tr(blochMatrix r · blochMatrix s) = (1 + r⃗·s⃗)/2`,

the off-diagonal generalisation of `Concrete.blochMatrix_sq_trace` (the `r = s` case, giving
`(1 + ‖r⃗‖²)/2`). This is the concrete content of the Hilbert–Schmidt overlap of two
Bloch states `tr(ρ_r ρ_s) = (1 + r⃗·s⃗)/2`, and — for a pure state (`‖r⃗‖ = 1`) — of the squared
fidelity `⟨ψ_r| ρ_s |ψ_r⟩`, used in the depolarizing-channel fidelity of Nielsen & Chuang
Exercise 10.12.
-/

open Matrix

namespace AxQM.Concrete

/-- **The trace of a product of two Bloch matrices.** For real three-vectors `r`, `s`,
`tr(blochMatrix r · blochMatrix s) = (1 + r⃗·s⃗)/2`, where `r⃗·s⃗ = r₀s₀ + r₁s₁ + r₂s₂`.

Expanding `blochMatrix r · blochMatrix s = ¼(I + r·σ)(I + s·σ)`, the trace is `¼(tr I + tr(r·σ) +
tr(s·σ) + tr((r·σ)(s·σ))) = ¼(2 + 0 + 0 + 2 r⃗·s⃗) = (1 + r⃗·s⃗)/2`. Proved by the direct `2 × 2`
computation off the explicit entries (`blochMatrix_eq`), mirroring `blochMatrix_sq_trace` (the
diagonal `r = s` case). -/
theorem blochMatrix_mul_trace (r s : Fin 3 → ℝ) :
    (blochMatrix r * blochMatrix s).trace
      = (((1 + (r 0 * s 0 + r 1 * s 1 + r 2 * s 2)) / 2 : ℝ) : ℂ) := by
  rw [blochMatrix_eq, blochMatrix_eq, Matrix.mul_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow, Complex.I_re,
      Complex.I_im] <;>
    ring

end AxQM.Concrete
