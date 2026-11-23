/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import AxQM.Concrete.Hadamard

/-!
# Concrete: the Hadamard matrix from `R_y` and `R_x` rotations (Nielsen & Chuang, Ex. 7.31)

Nielsen & Chuang, Exercise 7.31 (§7.6.3, ion-trap single-qubit operations, p. 319) asks to
*construct a Hadamard gate from `R_y` and `R_x` rotations*. In that section the available
single-qubit operations are the coordinate rotations `R_x(θ) = exp(−iθX/2)` and
`R_y(θ) = exp(−iθY/2)` (there written `exp(−iθS_x)`, `exp(−iθS_y)` with the spin operators
`S_x = X/2`, `S_y = Y/2`), and — by Theorem 4.1 — these generate every single-qubit operation up to
a global phase. The closed-form answer for the Hadamard is

`H = e^{iπ/2} R_x(π) R_y(π/2)`  (with global phase `e^{iπ/2} = i`).

Building on the rotation matrices `rotX`, `rotY` of `AxQM/Concrete/Rotation.lean` (N&C eqs.
4.4–4.5) and the complex Hadamard matrix `hadamardC` of `AxQM/Concrete/Hadamard.lean` (eq. 2.85),
this file proves the above `2 × 2` matrix identity. The statement of Exercise 7.31 is in
`AxQM/NC/Ch7/Exercise7_31.lean`. (This is the analogue of the `R_x`–`R_z` decomposition of
Exercise 4.4 in `AxQM/Concrete/HadamardRotation.lean`, which additionally has a state-evolution
statement in `AxQM/NC/Ch4/Exercise4_4.lean`.)

## What is formalised

* `rotX_pi_mul_rotY_pi_div_two` — the reusable computational core: the product `R_x(π) R_y(π/2)` in
  closed form, `(√2)⁻¹ • !![-i, -i; -i, i]` (` = -i H`).
* `hadamardC_eq_expPiDivTwo_smul_rotX_rotY` — **Exercise 7.31 as a matrix identity**:
  `H = e^{iπ/2} • (R_x(π) R_y(π/2))`, obtained by multiplying the product core by the phase
  `e^{iπ/2} = i`.

## Design notes

* **The decomposition is verified, not asserted.** `rotX`/`rotY` are consumed through their
  explicit-matrix forms `rotX_eq`/`rotY_eq` (the closed forms of eqs. 4.4/4.5), and the product is
  computed entrywise, so the identity is a *theorem* about the rotation operators of §4.2, not a
  restatement of the answer.
* **Why `R_x(π) R_y(π/2)` (and this order).** `R_y(π/2)` rotates `ẑ ↦ x̂` (the Hadamard sends `|0⟩`
  to `|+⟩`), and the following `R_x(π)` fixes the `x̂` axis while flipping the sign that turns the
  reflection into the Hadamard; the product evaluates to `-i H`. The order matters:
  `R_y(π/2) R_x(π)` is a *different* matrix, so the exercise's "from `R_y` and `R_x` rotations" is
  realised specifically as `R_x(π) R_y(π/2)`. Only one `R_x` and one `R_y` are needed.
* **The phase `ϕ = π/2`.** The product `R_x(π) R_y(π/2)` evaluates to `-i H`; multiplying by
  `e^{iπ/2} = i` recovers `H`. The exercise permits any correct `(ϕ, sequence)`; the global phase
  is physically unobservable.
* **Entry arithmetic.** At `θ = π` the `R_x` entries are `cos(π/2) = 0`, `sin(π/2) = 1` (so
  `R_x(π) = !![0, -i; -i, 0] = -iX`); at `θ = π/2` the `R_y` entries are
  `cos(π/4) = sin(π/4) = (√2)⁻¹`. Each product entry then reduces to a Gaussian-integer multiple of
  `(√2)⁻¹`, and the phase step uses `i² = -1` (`Complex.I_sq`).
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The product `R_x(π) R_y(π/2)` in closed form: `(√2)⁻¹ • !![-i, -i; -i, i]`, i.e. `-i H`. This is
the reusable computational core of the Hadamard `R_x`–`R_y` decomposition (Nielsen & Chuang,
Exercise 7.31), obtained from the explicit forms `rotX_eq`/`rotY_eq` (`R_x(π) = !![0, -i; -i, 0]`,
`R_y(π/2) = (√2)⁻¹ !![1, -1; 1, 1]`) by an entrywise computation. -/
theorem rotX_pi_mul_rotY_pi_div_two :
    rotX Real.pi * rotY (Real.pi / 2)
      = (Real.sqrt 2 : ℂ)⁻¹ • !![-Complex.I, -Complex.I; -Complex.I, Complex.I] := by
  have hcX : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have hsX : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have hcY : Real.cos (Real.pi / 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four, Real.sqrt_div_self]
  have hsY : Real.sin (Real.pi / 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four, Real.sqrt_div_self]
  rw [rotX_eq, rotY_eq]
  simp only [Matrix.mul_fin_two, hcX, hsX, hcY, hsY]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one,
      smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_zero, Complex.ofReal_one] <;>
    ring

/-- **Nielsen & Chuang, Exercise 7.31 (matrix form).** The Hadamard matrix is the `R_x`–`R_y`
rotation product up to the global phase `e^{iπ/2}`:
`H = e^{iπ/2} • (R_x(π) R_y(π/2))`.
Since `R_x(π) R_y(π/2) = -i H` (`rotX_pi_mul_rotY_pi_div_two`) and `e^{iπ/2} = i`, multiplying by
the phase recovers `H`. -/
theorem hadamardC_eq_expPiDivTwo_smul_rotX_rotY :
    hadamardC = Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
      (rotX Real.pi * rotY (Real.pi / 2)) := by
  have hphase : Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) = Complex.I := by
    push_cast; exact Complex.exp_pi_div_two_mul_I
  rw [hphase, rotX_pi_mul_rotY_pi_div_two]
  exact hadamardC_eq_I_smul_negIH

end AxQM.Concrete
