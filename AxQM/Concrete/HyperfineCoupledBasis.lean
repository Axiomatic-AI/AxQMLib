/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HyperfineAngularMomentum
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete: the coupled `|F, m_F⟩` hyperfine basis (Nielsen & Chuang, Exercise 7.28, part 2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.28 (p. 315) — the
"hyperfine states" exercise — couples a **nuclear spin `I = 3/2`** with an **electron spin
`S = 1/2`** into the total angular momentum `F = I + S` on `ℂ⁴ ⊗ ℂ² ≅ ℂ⁸`. Having written the
`8 × 8` matrices `f_x, f_y, f_z` and `F² = f_x² + f_y² + f_z²` (in
`Concrete.HyperfineAngularMomentum`), part 2 finishes by asking to

Simultaneous diagonalisation of f_z and F², giving the coupled basis |F, m_F⟩.

This file provides the eight coupled states and carries out that diagonalization: each state is
a simultaneous eigenvector of `f_z` (eigenvalue `m_F`) and `F²` (eigenvalue `F(F+1)`), and the
eight states form an orthonormal basis.

## The coupled states (Clebsch–Gordan for `3/2 ⊗ 1/2`)

The product basis `|m_I, m_S⟩` is the flat index `2·a + b` of `flattenFin8`, where `a : Fin 4`
carries `m_I = a − 3/2` and `b : Fin 2` carries `m_S = +½` (`b = 0`) or `m_S = −½` (`b = 1`).
Coupling `3/2 ⊗ 1/2` gives a `F = 2` quintet and a `F = 1` triplet; the Clebsch–Gordan
coefficients (with `j₁ = 3/2`, `2j₁ + 1 = 4`) use only the amplitudes `1`, `½`, `√3/2`, `1/√2`,
the stretched states `|2, ±2⟩` being the single product states `|±3/2, ±½⟩`. Concretely (in the
flat basis `e₀,…,e₇`):

* `|2,+2⟩ = e₆`, `|2,−2⟩ = e₁` (the extremal states);
* `|2,+1⟩ = (√3/2) e₄ + (½) e₇`, `|1,+1⟩ = −(½) e₄ + (√3/2) e₇` (the `m_F = +1` block);
* `|2, 0⟩ = (e₂ + e₅)/√2`, `|1, 0⟩ = (e₂ − e₅)/√2` (the `m_F = 0` block);
* `|2,−1⟩ = (½) e₀ + (√3/2) e₃`, `|1,−1⟩ = (√3/2) e₀ − (½) e₃` (the `m_F = −1` block).

Within each `m_F` block these are exactly the eigenvectors of the `2 × 2` `F²`-blocks
`!![3,√3; √3,5]`, `!![4,2; 2,4]`, `!![5,√3; √3,3]` of `hyperfineFSq_eq`, with eigenvalues
`6 = 2·3` (for `F = 2`) and `2 = 1·2` (for `F = 1`).

The file defines the eight states `hyperfineCoupledF2{p2,p1,z,n1,n2}`, `hyperfineCoupledF1{p1,z,n1}`
(as vectors `Fin 8 → ℂ`), proves `hyperfineFz_mulVec_*` (`f_z |F,m_F⟩ = m_F • |F,m_F⟩`) and
`hyperfineFSq_mulVec_*` (`F² |F,m_F⟩ = F(F+1) • |F,m_F⟩`, eigenvalue `6` for `F = 2`, `2` for
`F = 1`), and assembles the change-of-basis matrix `hyperfineCoupledBasis` (columns the eight
states, ordered `|2,−2⟩,…,|2,+2⟩,|1,−1⟩,|1,0⟩,|1,+1⟩`), shown unitary by
`hyperfineCoupledBasis_conjTranspose_mul_self` (`Uᴴ U = I`). Together these say `Uᴴ f_z U` and
`Uᴴ F² U` are `diag(−2,−1,0,1,2,−1,0,1)` and `diag(6,6,6,6,6,2,2,2)` — the simultaneous
diagonalization the exercise asks for.

This mirrors the two spin-½ analogue
`Concrete.TwoQubitAngularMomentum` (Exercise 7.26) for `3/2 ⊗ 1/2`. States are column vectors
`Fin 8 → ℂ`, a
matrix acts by `Matrix.mulVec` (`M *ᵥ v`), each eigenvalue equation is `M *ᵥ v = μ • v` with `μ`
explicit, and orthonormality is `Uᴴ U = I`; the `√3`/`1/√2` amplitudes reuse `sqrt3`
(`Concrete.Spin32AngularMomentum`) and `invSqrt2` (`Concrete.PauliEigenvectors`), and every fact
reduces to an entrywise computation using `sqrt3_mul_self` and `invSqrt2_mul_self`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-! ### The eight coupled `|F, m_F⟩` states -/

/-- The `F = 2`, `m_F = +2` hyperfine state `|2,+2⟩ = |m_I=+3/2, m_S=+½⟩ = e₆` (the stretched
state); Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2p2 : Fin 8 → ℂ := ![0, 0, 0, 0, 0, 0, 1, 0]

/-- The `F = 2`, `m_F = +1` hyperfine state `|2,+1⟩ = (√3/2)|+½,+½⟩ + (½)|+3/2,−½⟩ =
(√3/2) e₄ + (½) e₇`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2p1 : Fin 8 → ℂ :=
  ![0, 0, 0, 0, sqrt3 * 2⁻¹, 0, 0, 2⁻¹]

/-- The `F = 2`, `m_F = 0` hyperfine state `|2,0⟩ = (|−½,+½⟩ + |+½,−½⟩)/√2 = (e₂ + e₅)/√2`;
Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2z : Fin 8 → ℂ :=
  ![0, 0, invSqrt2, 0, 0, invSqrt2, 0, 0]

/-- The `F = 2`, `m_F = −1` hyperfine state `|2,−1⟩ = (½)|−3/2,+½⟩ + (√3/2)|−½,−½⟩ =
(½) e₀ + (√3/2) e₃`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2n1 : Fin 8 → ℂ :=
  ![2⁻¹, 0, 0, sqrt3 * 2⁻¹, 0, 0, 0, 0]

/-- The `F = 2`, `m_F = −2` hyperfine state `|2,−2⟩ = |m_I=−3/2, m_S=−½⟩ = e₁` (the stretched
state); Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF2n2 : Fin 8 → ℂ := ![0, 1, 0, 0, 0, 0, 0, 0]

/-- The `F = 1`, `m_F = +1` hyperfine state `|1,+1⟩ = −(½)|+½,+½⟩ + (√3/2)|+3/2,−½⟩ =
−(½) e₄ + (√3/2) e₇`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF1p1 : Fin 8 → ℂ :=
  ![0, 0, 0, 0, -2⁻¹, 0, 0, sqrt3 * 2⁻¹]

/-- The `F = 1`, `m_F = 0` hyperfine state `|1,0⟩ = (|−½,+½⟩ − |+½,−½⟩)/√2 = (e₂ − e₅)/√2`;
Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF1z : Fin 8 → ℂ :=
  ![0, 0, invSqrt2, 0, 0, -invSqrt2, 0, 0]

/-- The `F = 1`, `m_F = −1` hyperfine state `|1,−1⟩ = (√3/2)|−3/2,+½⟩ − (½)|−½,−½⟩ =
(√3/2) e₀ − (½) e₃`; Nielsen & Chuang, Exercise 7.28. -/
noncomputable def hyperfineCoupledF1n1 : Fin 8 → ℂ :=
  ![sqrt3 * 2⁻¹, 0, 0, -2⁻¹, 0, 0, 0, 0]

/-! ### `f_z` eigenvalues: each coupled state is an `f_z`-eigenstate with eigenvalue `m_F` -/

/-- `f_z |2,+2⟩ = 2 |2,+2⟩`. -/
theorem hyperfineFz_mulVec_coupledF2p2 :
    hyperfineFz *ᵥ hyperfineCoupledF2p2 = (2 : ℂ) • hyperfineCoupledF2p2 := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2p2, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `f_z |2,+1⟩ = 1 |2,+1⟩`. -/
theorem hyperfineFz_mulVec_coupledF2p1 :
    hyperfineFz *ᵥ hyperfineCoupledF2p1 = (1 : ℂ) • hyperfineCoupledF2p1 := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2p1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `f_z |2,0⟩ = 0`. -/
theorem hyperfineFz_mulVec_coupledF2z :
    hyperfineFz *ᵥ hyperfineCoupledF2z = (0 : ℂ) • hyperfineCoupledF2z := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2z, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `f_z |2,−1⟩ = −1 |2,−1⟩`. -/
theorem hyperfineFz_mulVec_coupledF2n1 :
    hyperfineFz *ᵥ hyperfineCoupledF2n1 = (-1 : ℂ) • hyperfineCoupledF2n1 := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2n1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `f_z |2,−2⟩ = −2 |2,−2⟩`. -/
theorem hyperfineFz_mulVec_coupledF2n2 :
    hyperfineFz *ᵥ hyperfineCoupledF2n2 = (-2 : ℂ) • hyperfineCoupledF2n2 := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2n2, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `f_z |1,+1⟩ = 1 |1,+1⟩`. -/
theorem hyperfineFz_mulVec_coupledF1p1 :
    hyperfineFz *ᵥ hyperfineCoupledF1p1 = (1 : ℂ) • hyperfineCoupledF1p1 := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF1p1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `f_z |1,0⟩ = 0`. -/
theorem hyperfineFz_mulVec_coupledF1z :
    hyperfineFz *ᵥ hyperfineCoupledF1z = (0 : ℂ) • hyperfineCoupledF1z := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF1z, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `f_z |1,−1⟩ = −1 |1,−1⟩`. -/
theorem hyperfineFz_mulVec_coupledF1n1 :
    hyperfineFz *ᵥ hyperfineCoupledF1n1 = (-1 : ℂ) • hyperfineCoupledF1n1 := by
  rw [hyperfineFz_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF1n1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-! ### `F²` eigenvalues: each coupled state is a `F²`-eigenstate with eigenvalue `F(F+1)` -/

/-- `F² |2,+2⟩ = 6 |2,+2⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2p2 :
    hyperfineFSq *ᵥ hyperfineCoupledF2p2 = (6 : ℂ) • hyperfineCoupledF2p2 := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2p2, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `F² |2,+1⟩ = 6 |2,+1⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2p1 :
    hyperfineFSq *ᵥ hyperfineCoupledF2p1 = (6 : ℂ) • hyperfineCoupledF2p1 := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;> simp [hyperfineCoupledF2p1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  all_goals ring_nf
  simp only [sqrt3_sq]
  ring

/-- `F² |2,0⟩ = 6 |2,0⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2z :
    hyperfineFSq *ᵥ hyperfineCoupledF2z = (6 : ℂ) • hyperfineCoupledF2z := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2z, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;> ring

/-- `F² |2,−1⟩ = 6 |2,−1⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2n1 :
    hyperfineFSq *ᵥ hyperfineCoupledF2n1 = (6 : ℂ) • hyperfineCoupledF2n1 := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;> simp [hyperfineCoupledF2n1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  all_goals ring_nf
  simp only [sqrt3_sq]
  ring

/-- `F² |2,−2⟩ = 6 |2,−2⟩`: `F = 2`, so `F(F+1) = 6`. -/
theorem hyperfineFSq_mulVec_coupledF2n2 :
    hyperfineFSq *ᵥ hyperfineCoupledF2n2 = (6 : ℂ) • hyperfineCoupledF2n2 := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF2n2, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- `F² |1,+1⟩ = 2 |1,+1⟩`: `F = 1`, so `F(F+1) = 2`. -/
theorem hyperfineFSq_mulVec_coupledF1p1 :
    hyperfineFSq *ᵥ hyperfineCoupledF1p1 = (2 : ℂ) • hyperfineCoupledF1p1 := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;> simp [hyperfineCoupledF1p1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  all_goals ring_nf
  simp only [sqrt3_sq]
  ring

/-- `F² |1,0⟩ = 2 |1,0⟩`: `F = 1`, so `F(F+1) = 2`. -/
theorem hyperfineFSq_mulVec_coupledF1z :
    hyperfineFSq *ᵥ hyperfineCoupledF1z = (2 : ℂ) • hyperfineCoupledF1z := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;>
    simp [hyperfineCoupledF1z, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;> ring

/-- `F² |1,−1⟩ = 2 |1,−1⟩`: `F = 1`, so `F(F+1) = 2`. -/
theorem hyperfineFSq_mulVec_coupledF1n1 :
    hyperfineFSq *ᵥ hyperfineCoupledF1n1 = (2 : ℂ) • hyperfineCoupledF1n1 := by
  rw [hyperfineFSq_eq]; ext i
  fin_cases i <;> simp [hyperfineCoupledF1n1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  all_goals ring_nf
  simp only [sqrt3_sq]
  ring

/-! ### The coupled basis is orthonormal -/

/-- The change-of-basis matrix `U` whose columns are the eight coupled `|F, m_F⟩` states, ordered
`|2,−2⟩, |2,−1⟩, |2,0⟩, |2,+1⟩, |2,+2⟩, |1,−1⟩, |1,0⟩, |1,+1⟩` (the `F = 2` quintet by increasing
`m_F`, then the `F = 1` triplet). -/
noncomputable def hyperfineCoupledBasis : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 2⁻¹, 0, 0, 0, sqrt3 * 2⁻¹, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, invSqrt2, 0, 0, 0, invSqrt2, 0;
     0, sqrt3 * 2⁻¹, 0, 0, 0, -2⁻¹, 0, 0;
     0, 0, 0, sqrt3 * 2⁻¹, 0, 0, 0, -2⁻¹;
     0, 0, invSqrt2, 0, 0, 0, -invSqrt2, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 2⁻¹, 0, 0, 0, sqrt3 * 2⁻¹]

/-- `√3` is real, hence fixed by the complex conjugation `starRingEnd`, the form in which the
conjugate-transpose entries of `hyperfineCoupledBasis` appear. -/
theorem sqrt3_conj : (starRingEnd ℂ) sqrt3 = sqrt3 := sqrt3_star

/-- `1/√2` is fixed by the complex conjugation `starRingEnd`. -/
theorem invSqrt2_conj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := invSqrt2_star

set_option maxRecDepth 4000 in
/-- The coupled basis is **orthonormal**: `Uᴴ U = I`. Hence the eight states `|F, m_F⟩` form an
orthonormal basis of `ℂ⁸`, so writing `f_z` and `F²` "in that basis" is meaningful; combined with
the eigenvalue equations above, `Uᴴ f_z U` and `Uᴴ F² U` are the diagonal matrices
`diag(−2,−1,0,1,2,−1,0,1)` and `diag(6,6,6,6,6,2,2,2)` — the simultaneous diagonalization of
`f_z` and `F²` (Nielsen & Chuang, Exercise 7.28). -/
theorem hyperfineCoupledBasis_conjTranspose_mul_self :
    hyperfineCoupledBasisᴴ * hyperfineCoupledBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperfineCoupledBasis, Matrix.mul_apply, Fin.sum_univ_eight,
      Matrix.conjTranspose_apply, invSqrt2_conj, sqrt3_conj, invSqrt2_mul_self, map_ofNat] <;>
    ring_nf <;> simp only [sqrt3_sq] <;> norm_num

end AxQM.Concrete
