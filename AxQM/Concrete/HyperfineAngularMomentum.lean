/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Spin32AngularMomentum
import AxQM.Concrete.PauliKronecker

/-!
# Concrete: the hyperfine angular-momentum operators (Nielsen & Chuang, Exercise 7.28, part 2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.28 (p. 315) — the
"hyperfine states" exercise — couples a **nuclear spin `I = 3/2`** (the spin-3/2 operators
`i_x, i_y, i_z` of `Concrete.Spin32AngularMomentum`, on `ℂ⁴`) with an **electron spin
`S = 1/2`** (`ℂ²`) to form the total angular momentum `F = I + S` on `ℂ⁴ ⊗ ℂ² ≅ ℂ⁸`. Part 2
asks to

Matrix representations of the hyperfine total angular-momentum operators f_x, f_y, f_z and F².

This file provides **the operators and their explicit `8 × 8` matrices** — the first half of
part 2. The coupled basis `|F, m_F⟩` and the eigenvalue/diagonalization theorems are built on
top of these definitions in `Concrete.HyperfineCoupledBasis`.

## Contents

* `flattenFin8` — the reusable `Fin 4 × Fin 2 → Fin 8` re-indexing of a nuclear ⊗ electron
  tensor product to its flat `8 × 8` matrix, ordering the product index by
  `finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8`, `(a, b) ↦ 2 · a + b` (the `Fin 4`-analogue of
  `flattenFin4` from `Concrete.PauliKronecker`).
* `hyperfineFx`, `hyperfineFy`, `hyperfineFz` — the total angular-momentum operators
  `f_a = i_a ⊗ I + I ⊗ σ_a/2`, built from the spin-3/2 operators `spin32Ia` and the Pauli
  matrices by Kronecker product; `hyperfineFSq = f_x² + f_y² + f_z²`.
* `hyperfineFz_eq`, `hyperfineFx_eq`, `hyperfineFy_eq`, `hyperfineFSq_eq` — the explicit `8 × 8`
  matrices the exercise asks us to write out. In particular `f_z = diag(-1,-2,0,-1,1,0,2,1)` is
  diagonal, and `F²` is block-diagonal (each block indexed by a value of `m_F`), with the
  `2 × 2` blocks `!![3,√3; √3,5]`, `!![4,2; 2,4]`, `!![5,√3; √3,3]` on the `m_F = -1, 0, +1`
  subspaces — exactly the off-diagonal couplings the coupled basis diagonalizes.

## The basis-ordering convention

The combined basis is ordered by `flattenFin8`, `(a, b) ↦ 2·a + b`, where `a : Fin 4` indexes
the nuclear state (increasing `m_I = a - 3/2`, matching `spin32Iz = ½·diag(-3,-1,1,3)`) and
`b : Fin 2` the electron state. With the standard Pauli `Z = diag(1,-1)` we have `Z/2 =
diag(+½,-½)`, so `b = 0 ↦ m_S = +½` and `b = 1 ↦ m_S = -½`. The flat index `2·a + b` therefore
carries `m_F = m_I + m_S`, giving the diagonal `f_z = diag(-1,-2,0,-1,1,0,2,1)` computed in
`hyperfineFz_eq`.

Compare `Concrete.Pauli`,
`Concrete.PauliKronecker`, and `Concrete.TwoQubitAngularMomentum` (the two spin-½ analogue,
Exercise 7.26). Each operator is a `Matrix (Fin 8) (Fin 8) ℂ`, matrix multiplication is
`Matrix.mul`, and each matrix identity is proved by reducing to an entrywise computation
(`ext`, `fin_cases`, `simp`), using `sqrt3_sq`/`sqrt3_mul_self` to collapse `(√3)² = 3` and
`Complex.I_sq` for `i² = -1`.
-/

namespace AxQM.Concrete

open Matrix Complex
open scoped Kronecker

/-! ### Flattening a nuclear ⊗ electron tensor product to an `8 × 8` matrix -/

/-- Flatten a `Fin 4 × Fin 2`-indexed matrix (a nuclear ⊗ electron tensor product) to its
`8 × 8` matrix representation, ordering the product index by
`finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8`, `(a, b) ↦ 2 · a + b` — the `Fin 4`-analogue of
`flattenFin4`. -/
def flattenFin8 (M : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv M

/-! ### The hyperfine angular-momentum operators -/

/-- The hyperfine `x`-operator `f_x = i_x ⊗ I + I ⊗ X/2` on `ℂ⁴ ⊗ ℂ² ≅ ℂ⁸` (Nielsen & Chuang,
Exercise 7.28), with `i_x = spin32Ix` the spin-3/2 nuclear operator and `X/2` the electron
spin. -/
noncomputable def hyperfineFx : Matrix (Fin 8) (Fin 8) ℂ :=
  flattenFin8 (spin32Ix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ ((2⁻¹ : ℂ) • pauliX))

/-- The hyperfine `y`-operator `f_y = i_y ⊗ I + I ⊗ Y/2`. -/
noncomputable def hyperfineFy : Matrix (Fin 8) (Fin 8) ℂ :=
  flattenFin8 (spin32Iy ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ ((2⁻¹ : ℂ) • pauliY))

/-- The hyperfine `z`-operator `f_z = i_z ⊗ I + I ⊗ Z/2` (Nielsen & Chuang, Exercise 7.28). -/
noncomputable def hyperfineFz : Matrix (Fin 8) (Fin 8) ℂ :=
  flattenFin8 (spin32Iz ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ ((2⁻¹ : ℂ) • pauliZ))

/-- The total hyperfine angular-momentum-squared operator `F² = f_x² + f_y² + f_z²` (Nielsen &
Chuang, Exercise 7.28). -/
noncomputable def hyperfineFSq : Matrix (Fin 8) (Fin 8) ℂ :=
  hyperfineFx * hyperfineFx + hyperfineFy * hyperfineFy + hyperfineFz * hyperfineFz

/-! ### The explicit `8 × 8` matrices -/

/-- The explicit matrix of `f_z = i_z ⊗ I + I ⊗ Z/2`: the diagonal matrix
`diag(-1, -2, 0, -1, 1, 0, 2, 1)`, whose entries are the `m_F = m_I + m_S` values of the eight
product basis states. This is the first of the two matrices Nielsen & Chuang, Exercise 7.28
asks us to write out and diagonalize. -/
theorem hyperfineFz_eq :
    hyperfineFz =
      !![-1, 0, 0, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperfineFz, flattenFin8, spin32Iz, pauliZ, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.add_apply] <;>
    norm_num

/-- The explicit matrix of `f_x = i_x ⊗ I + I ⊗ X/2`. The nuclear `i_x` contributes the
`√3/2, 1/2` off-diagonals within each electron block; the electron `X/2` contributes the `1`s
coupling `m_S = +½ ↔ -½`. -/
theorem hyperfineFx_eq :
    hyperfineFx =
      !![0, 2⁻¹, sqrt3 * 2⁻¹, 0, 0, 0, 0, 0;
         2⁻¹, 0, 0, sqrt3 * 2⁻¹, 0, 0, 0, 0;
         sqrt3 * 2⁻¹, 0, 0, 2⁻¹, 1, 0, 0, 0;
         0, sqrt3 * 2⁻¹, 2⁻¹, 0, 0, 1, 0, 0;
         0, 0, 1, 0, 0, 2⁻¹, sqrt3 * 2⁻¹, 0;
         0, 0, 0, 1, 2⁻¹, 0, 0, sqrt3 * 2⁻¹;
         0, 0, 0, 0, sqrt3 * 2⁻¹, 0, 0, 2⁻¹;
         0, 0, 0, 0, 0, sqrt3 * 2⁻¹, 2⁻¹, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperfineFx, flattenFin8, spin32Ix, pauliX, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.add_apply] <;>
    ring

/-- The explicit matrix of `f_y = i_y ⊗ I + I ⊗ Y/2`. -/
theorem hyperfineFy_eq :
    hyperfineFy =
      !![0, -(I * 2⁻¹), sqrt3 * I * 2⁻¹, 0, 0, 0, 0, 0;
         I * 2⁻¹, 0, 0, sqrt3 * I * 2⁻¹, 0, 0, 0, 0;
         -(sqrt3 * I * 2⁻¹), 0, 0, -(I * 2⁻¹), I, 0, 0, 0;
         0, -(sqrt3 * I * 2⁻¹), I * 2⁻¹, 0, 0, I, 0, 0;
         0, 0, -I, 0, 0, -(I * 2⁻¹), sqrt3 * I * 2⁻¹, 0;
         0, 0, 0, -I, I * 2⁻¹, 0, 0, sqrt3 * I * 2⁻¹;
         0, 0, 0, 0, -(sqrt3 * I * 2⁻¹), 0, 0, -(I * 2⁻¹);
         0, 0, 0, 0, 0, -(sqrt3 * I * 2⁻¹), I * 2⁻¹, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperfineFy, flattenFin8, spin32Iy, pauliY, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.add_apply] <;>
    ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
-- The identity multiplies out three explicit `8 × 8` matrices entrywise (64 entries, each an
-- 8-term dot product), which exceeds the default heartbeat/recursion budget.
/-- The explicit matrix of `F² = f_x² + f_y² + f_z²`. It is block-diagonal in the product basis
(each block indexed by a value of `m_F`): the `m_F = ±2` states carry the diagonal entry `6`,
and the `m_F = -1, 0, +1` subspaces carry the `2 × 2` blocks `!![3,√3; √3,5]`, `!![4,2; 2,4]`,
`!![5,√3; √3,3]` respectively, each with eigenvalues `6 = 2·3` and `2 = 1·2` — i.e.
`F(F+1)` for `F = 2` and `F = 1`. This is the second matrix Nielsen & Chuang, Exercise 7.28
asks us to write out and diagonalize. -/
theorem hyperfineFSq_eq :
    hyperfineFSq =
      !![3, 0, 0, sqrt3, 0, 0, 0, 0; 0, 6, 0, 0, 0, 0, 0, 0; 0, 0, 4, 0, 0, 2, 0, 0;
         sqrt3, 0, 0, 5, 0, 0, 0, 0; 0, 0, 0, 0, 5, 0, 0, sqrt3; 0, 0, 2, 0, 0, 4, 0, 0;
         0, 0, 0, 0, 0, 0, 6, 0; 0, 0, 0, 0, sqrt3, 0, 0, 3] := by
  rw [hyperfineFSq, hyperfineFx_eq, hyperfineFy_eq, hyperfineFz_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply] <;>
    ring_nf <;>
    simp only [sqrt3_sq, Complex.I_sq] <;>
    ring

end AxQM.Concrete
