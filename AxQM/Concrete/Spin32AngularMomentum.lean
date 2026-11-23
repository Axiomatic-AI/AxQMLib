/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import ToMathlib.Data.Real.Sqrt
import ToMathlib.Algebra.BigOperators.Fin

/-!
# Concrete: the spin-3/2 angular-momentum operators (Nielsen & Chuang, Exercise 7.28, part 1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.28 (p. 315) — the
"hyperfine states" exercise — introduces, for a **spin-3/2** particle (nuclear spin `I = 3/2`),
the three angular-momentum operators as explicit `4 × 4` matrices (equations (7.106)–(7.108)):

`i_x = ½·!![0,√3,0,0; √3,0,2,0; 0,2,0,√3; 0,0,√3,0]`,
`i_y = ½·!![0,i√3,0,0; -i√3,0,2i,0; 0,-2i,0,i√3; 0,0,-i√3,0]`,
`i_z = ½·!![-3,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,3]`,

and asks (part 1) to **show that `i_x, i_y, i_z` satisfy the `SU(2)` commutation rules**, i.e. the
`su(2)` Lie-algebra relations `[i_a, i_b] = i ε_{abc} i_c`.

## Contents

* `sqrt3`, `sqrt3_mul_self`, `sqrt3_sq` — the constant `√3 : ℂ` and its defining identities
  `√3·√3 = 3`, `(√3)² = 3` (the `√3`-analogue of `Concrete.invSqrt2`, reused by the hyperfine
  development in `Concrete.HyperfineAngularMomentum`).
* `spin32Ix`, `spin32Iy`, `spin32Iz` — the three operators as `4 × 4` matrices, transcribed
  verbatim from (7.106)–(7.108).
* `spin32_comm_ix_iy`, `spin32_comm_iy_iz`, `spin32_comm_iz_ix` — the three cyclic `SU(2)`
  commutation relations `[i_x, i_y] = i·i_z`, `[i_y, i_z] = i·i_x`, `[i_z, i_x] = i·i_y`. (The
  remaining three relations are their antisymmetric partners.) This is **part 1 of the exercise.**

## The basis-ordering convention

The `4 × 4` representation orders the spin-3/2 basis by **increasing** magnetic quantum number
`m_I = (-3/2, -1/2, 1/2, 3/2)`, so that `i_z = ½·diag(-3, -1, 1, 3)` reproduces (7.108): the
`a`-th basis vector (`a : Fin 4`) has `m_I = a - 3/2`. With this ordering the raising/lowering
structure gives the off-diagonal entries `√3, 2, √3` of `i_x` and `i_y` from
`√(j(j+1) - m(m±1))` with `j = 3/2`.

This parallels `Concrete.Pauli` and
`Concrete.TwoQubitAngularMomentum` (the two spin-½ analogue, Exercise 7.26). Each operator is a
`Matrix (Fin 4) (Fin 4) ℂ` written as `½ • !![…]` exactly as N&C prints it, matrix multiplication
is `Matrix.mul`, and each commutation relation is proved by reducing to an entrywise computation
(`ext`, `fin_cases`, `simp`), using `sqrt3_sq` to collapse `(√3)² = 3` and `Complex.I_sq` for
`i² = -1`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-! ### The constant `√3` -/

/-- The real square root `√3`, as a complex number. This is the amplitude appearing in the
spin-3/2 operators (Nielsen & Chuang (7.106)–(7.108)) and in the hyperfine `|F, m_F⟩` states; it
is the `√3`-analogue of `Concrete.invSqrt2`. -/
noncomputable def sqrt3 : ℂ := (Real.sqrt 3 : ℂ)

/-- `√3 · √3 = 3`. -/
theorem sqrt3_mul_self : sqrt3 * sqrt3 = 3 := by
  rw [sqrt3, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `(√3)² = 3`, the squared form of `sqrt3_mul_self` (the form `ring_nf` produces). -/
theorem sqrt3_sq : sqrt3 ^ 2 = 3 := by rw [sq, sqrt3_mul_self]

/-- `√3` is real, hence fixed by complex conjugation. -/
theorem sqrt3_star : star sqrt3 = sqrt3 := by simp [sqrt3]

/-! ### The spin-3/2 angular-momentum operators -/

/-- The spin-3/2 angular-momentum `x`-operator `i_x` as a `4 × 4` matrix
(Nielsen & Chuang (7.106)): `i_x = ½·!![0,√3,0,0; √3,0,2,0; 0,2,0,√3; 0,0,√3,0]`. -/
noncomputable def spin32Ix : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![0, sqrt3, 0, 0; sqrt3, 0, 2, 0; 0, 2, 0, sqrt3; 0, 0, sqrt3, 0]

/-- The spin-3/2 angular-momentum `y`-operator `i_y` as a `4 × 4` matrix
(Nielsen & Chuang (7.107)): `i_y = ½·!![0,i√3,0,0; -i√3,0,2i,0; 0,-2i,0,i√3; 0,0,-i√3,0]`. -/
noncomputable def spin32Iy : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![0, sqrt3 * I, 0, 0; -(sqrt3 * I), 0, 2 * I, 0;
                 0, -(2 * I), 0, sqrt3 * I; 0, 0, -(sqrt3 * I), 0]

/-- The spin-3/2 angular-momentum `z`-operator `i_z` as a `4 × 4` matrix
(Nielsen & Chuang (7.108)): the diagonal matrix `i_z = ½·diag(-3, -1, 1, 3)`, so the basis is
ordered by increasing `m_I = (-3/2, -1/2, 1/2, 3/2)`. -/
noncomputable def spin32Iz : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![-3, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 3]

/-! ### The `SU(2)` commutation relations (part 1 of the exercise) -/

/-- `[i_x, i_y] = i·i_z`: the first cyclic `SU(2)` commutation relation for the spin-3/2 operators
(Nielsen & Chuang, Exercise 7.28, part 1). -/
theorem spin32_comm_ix_iy :
    spin32Ix * spin32Iy - spin32Iy * spin32Ix = I • spin32Iz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin32Ix, spin32Iy, spin32Iz, Matrix.sub_apply, Matrix.smul_apply] <;>
    ring_nf <;> simp only [sqrt3_sq] <;> ring

/-- `[i_y, i_z] = i·i_x`: the second cyclic `SU(2)` commutation relation for the spin-3/2
operators (Nielsen & Chuang, Exercise 7.28, part 1). -/
theorem spin32_comm_iy_iz :
    spin32Iy * spin32Iz - spin32Iz * spin32Iy = I • spin32Ix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin32Ix, spin32Iy, spin32Iz, Matrix.sub_apply, Matrix.smul_apply] <;> ring_nf

/-- `[i_z, i_x] = i·i_y`: the third cyclic `SU(2)` commutation relation for the spin-3/2 operators
(Nielsen & Chuang, Exercise 7.28, part 1). -/
theorem spin32_comm_iz_ix :
    spin32Iz * spin32Ix - spin32Ix * spin32Iz = I • spin32Iy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin32Ix, spin32Iy, spin32Iz, Matrix.sub_apply, Matrix.smul_apply] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

end AxQM.Concrete
