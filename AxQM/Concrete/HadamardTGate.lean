/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthGate
import AxQM.Concrete.RotationDecompositionXY

/-!
# Concrete: the π/8 (T) gate conjugated by Hadamard (Nielsen & Chuang, Exercise 4.14)

Nielsen & Chuang, Exercise 4.14 asks to show that, **up to a global phase**, `H T H = R_x(π/4)`,
where `T` is the π/8 gate (eq. 4.2) and `R_x` the `x̂`-axis rotation (eq. 4.4). This is pure
`2 × 2` complex-matrix mathematics about the Hadamard matrix `hadamardC`, the π/8-gate matrix
`tMatrix`, and the rotation operator `rotX`. The statement of Exercise 4.14 is
`hadamardC_mul_tMatrix_mul_hadamardC`, in `AxQM/NC/Ch4/Exercise4_14.lean`.

## What is formalised

* `hadamardC_mul_tMatrix_mul_hadamardC` — **Exercise 4.14 itself**:
  `H T H = e^{iπ/8} • R_x(π/4)`, i.e. `H T H` equals `R_x(π/4)` up to the unit-modulus global
  phase `e^{iπ/8}`.

## Design notes

* **The phase form `A = e^{iϕ} • B` is the file's idiom for "up to a global phase".** Following
  Exercise 4.3 (`Concrete.tMatrix_eq_expPiDivEight_smul_rotZ`, `T = e^{iπ/8} • R_z(π/4)`) and
  Exercise 4.4 (`Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotZ_rotX`), the "up to a global
  phase" relation is captured by an **exact** matrix identity with an explicit unit-modulus scalar
  `e^{iπ/8}` — not a weakened statement. The scalar `e^{iπ/8}` has modulus `1`, so it is a genuine
  global phase (physically unobservable); its exact value is the same `e^{iπ/8}` that already
  relates `T` to `R_z(π/4)`.
* **Reduction to two existing facts, no new entrywise computation.** The proof composes
  `tMatrix_eq_expPiDivEight_smul_rotZ` (Exercise 4.3: `T = e^{iπ/8} • R_z(π/4)`, from
  `Concrete/PiEighthGate.lean`) with `hadamardC_mul_rotZ_mul_hadamardC` (`H R_z(θ) H = R_x(θ)`,
  the Hadamard-conjugation lemma of `Concrete/RotationDecompositionXY.lean`, Exercise 4.10):
  `H T H = H (e^{iπ/8} R_z(π/4)) H = e^{iπ/8} (H R_z(π/4) H) = e^{iπ/8} R_x(π/4)`.
  Pulling the global-phase scalar out of the conjugation (`Matrix.mul_smul` / `Matrix.smul_mul`) is
  all that is needed. This mirrors N&C's own argument — `T = R_z(π/4)` up to phase, and `H` maps
  `R_z(θ)` to `R_x(θ)` because it exchanges the `x̂` and `ẑ` axes (`H Z H = X`).
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.14.** Up to a global phase, the π/8 (T) gate conjugated by the
Hadamard gate is the `x̂`-rotation by `π/4`:
`H T H = e^{iπ/8} • R_x(π/4)`.
The scalar `e^{iπ/8}` has modulus `1`, so it is an (unobservable) global phase. This composes
`tMatrix_eq_expPiDivEight_smul_rotZ` (`T = e^{iπ/8} • R_z(π/4)`, Exercise 4.3) with
`hadamardC_mul_rotZ_mul_hadamardC` (`H R_z(θ) H = R_x(θ)`, Exercise 4.10): pulling the phase out of
the Hadamard conjugation, `H T H = e^{iπ/8} (H R_z(π/4) H) = e^{iπ/8} R_x(π/4)`. -/
theorem hadamardC_mul_tMatrix_mul_hadamardC :
    hadamardC * tMatrix * hadamardC
      = Complex.exp ((Real.pi / 8 : ℝ) * Complex.I) • rotX (Real.pi / 4) := by
  rw [tMatrix_eq_expPiDivEight_smul_rotZ, Matrix.mul_smul, Matrix.smul_mul,
    hadamardC_mul_rotZ_mul_hadamardC]

end AxQM.Concrete
