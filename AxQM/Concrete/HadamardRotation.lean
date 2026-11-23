/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import AxQM.Concrete.Hadamard

/-!
# Concrete: the Hadamard matrix as a product of `R_x`, `R_z` rotations (Nielsen & Chuang, Ex. 4.4)

Nielsen & Chuang, Exercise 4.4 asks to express the Hadamard gate `H` as a product of `R_x` and `R_z`
rotations together with a global phase `e^{iϕ}`. The closed-form answer is

`H = e^{iπ/2} R_x(π/2) R_z(π/2) R_x(π/2)`.  (with `ϕ = π/2`, i.e. `e^{iϕ} = i`)

Building on the rotation matrices `rotX`, `rotZ` of `AxQM/Concrete/Rotation.lean` (N&C eqs. 4.4,
4.6) and the complex Hadamard matrix `hadamardC` of `AxQM/Concrete/Hadamard.lean` (eq. 2.85), this
file proves the above `2 × 2` matrix identity. The *physics* reading of Exercise 4.4 — that `H` and
the rotation product are the **same quantum operation** (the global phase being unobservable) — is
the statement in `AxQM/NC/Ch4/Exercise4_4.lean`, built on this identity and the gates of
`AxQM/Postulates/API/HadamardRotation.lean`.

## What is formalised

* `rotX_mul_rotZ_mul_rotX_pi_div_two` — the reusable computational core: the product
  `R_x(π/2) R_z(π/2) R_x(π/2)` in closed form,
  `(√2)⁻¹ • !![-i, -i; -i, i]` (` = -i H`).
* `hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX` — **Exercise 4.4 as a matrix identity**:
  `H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))`, obtained by multiplying the product core by the
  phase `e^{iπ/2} = i`.

## Design notes

* **The decomposition is verified, not asserted.** `rotX`/`rotZ` are consumed through their
  explicit-matrix forms `rotX_eq`/`rotZ_eq` (the closed forms of eqs. 4.4/4.6), and the product is
  computed entrywise, so the identity is a *theorem* about the rotation operators of `§4.2`, not a
  restatement.
* **The phase `ϕ = π/2`.** The product `R_x(π/2) R_z(π/2) R_x(π/2)` evaluates to `-i H`; multiplying
  by `e^{iπ/2} = i` recovers `H`. The exercise permits any correct `(ϕ, sequence)`; this is the
  standard `X`–`Z`–`X` sandwich (the reflection `H` exchanges the `x̂` and `ẑ` axes, so it is a
  rotation built symmetrically from `R_x` and `R_z`).
* **Entry arithmetic.** At `θ = π/2` the rotation entries are `cos(π/4) = sin(π/4) = (√2)⁻¹` and the
  `R_z` phases `e^{∓iπ/4} = (√2)⁻¹(1 ∓ i)`; each product entry then reduces to a Gaussian-integer
  multiple of `(√2)⁻¹` using `(√2)⁻¹·(√2)⁻¹ = 1/2` and `i² = -1`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The product `R_x(π/2) R_z(π/2) R_x(π/2)` in closed form: `(√2)⁻¹ • !![-i, -i; -i, i]`, i.e.
`-i H`. This is the reusable computational core of the Hadamard `X`–`Z`–`X` decomposition
(Nielsen & Chuang, Exercise 4.4), obtained from the explicit forms `rotX_eq`/`rotZ_eq` by an
entrywise computation. -/
theorem rotX_mul_rotZ_mul_rotX_pi_div_two :
    rotX (Real.pi / 2) * rotZ (Real.pi / 2) * rotX (Real.pi / 2)
      = (Real.sqrt 2 : ℂ)⁻¹ • !![-Complex.I, -Complex.I; -Complex.I, Complex.I] := by
  have hs : (Real.sqrt 2 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := Real.sqrt_div_self
  have hc : Real.cos (Real.pi / 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four, hs]
  have hsin : Real.sin (Real.pi / 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four, hs]
  have he1 : Complex.exp (-(((Real.pi / 2 : ℝ) : ℂ) / 2) * Complex.I)
      = (Real.sqrt 2 : ℂ)⁻¹ - (Real.sqrt 2 : ℂ)⁻¹ * Complex.I := by
    rw [show -(((Real.pi / 2 : ℝ) : ℂ) / 2) * Complex.I = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four, hs]
    push_cast; ring
  have he2 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) / 2 * Complex.I)
      = (Real.sqrt 2 : ℂ)⁻¹ + (Real.sqrt 2 : ℂ)⁻¹ * Complex.I := by
    rw [show ((Real.pi / 2 : ℝ) : ℂ) / 2 * Complex.I = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four, hs]
    push_cast; ring
  have hsqrt : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [rotX_eq, rotZ_eq]
  simp only [Matrix.mul_fin_two, hc, hsin, he1, he2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one,
      smul_eq_mul, Complex.ofReal_inv] <;>
    first
      | linear_combination (-2 * (Real.sqrt 2 : ℂ)⁻¹ * Complex.I) * hsqrt
      | linear_combination ((Real.sqrt 2 : ℂ)⁻¹ ^ 3 * (1 + Complex.I)) * Complex.I_sq
          + (-2 * (Real.sqrt 2 : ℂ)⁻¹ * Complex.I) * hsqrt
      | linear_combination ((Real.sqrt 2 : ℂ)⁻¹ ^ 3 * (1 - Complex.I)) * Complex.I_sq
          + (2 * (Real.sqrt 2 : ℂ)⁻¹ * Complex.I) * hsqrt

/-- **Nielsen & Chuang, Exercise 4.4 (matrix form).** The Hadamard matrix is the `X`–`Z`–`X`
rotation product up to the global phase `e^{iπ/2}`:
`H = e^{iπ/2} • (R_x(π/2) R_z(π/2) R_x(π/2))`.
Since `R_x(π/2) R_z(π/2) R_x(π/2) = -i H` (`rotX_mul_rotZ_mul_rotX_pi_div_two`) and
`e^{iπ/2} = i`, multiplying by the phase recovers `H`. -/
theorem hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX :
    hadamardC = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (rotX (Real.pi / 2) * rotZ (Real.pi / 2) * rotX (Real.pi / 2)) := by
  have hphase : Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) = Complex.I := by
    push_cast; exact Complex.exp_pi_div_two_mul_I
  rw [hphase, rotX_mul_rotZ_mul_rotX_pi_div_two]
  exact hadamardC_eq_I_smul_negIH

end AxQM.Concrete
