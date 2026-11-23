/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.PauliEigenvectors
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the §1.2 single-qubit pure state and its Bloch vector (N&C, Exercise 2.72(4))

This file records, at the matrix level, the
**§1.2 Bloch-sphere parametrization of a single-qubit pure state** and its agreement with the
mixed-state Bloch representation `Concrete.blochMatrix` (eq. 2.175) of
`AxQM/Concrete/BlochMatrix.lean`.

Nielsen & Chuang §1.2, eq. (1.4) writes a single-qubit pure state, up to global phase, as

`|ψ(θ,φ)⟩ = cos(θ/2) |0⟩ + e^{iφ} sin(θ/2) |1⟩`,

the point `(θ, φ)` lying on the Bloch sphere with Cartesian coordinates
`r⃗ = (sin θ cos φ, sin θ sin φ, cos θ)`. Exercise 2.72(4) asks to show that for pure states this
Bloch vector **coincides** with the mixed-state Bloch vector of part (1): the density matrix
`|ψ(θ,φ)⟩⟨ψ(θ,φ)|` equals `½(I + r⃗·σ⃗)` for that `r⃗`.

## Contents

* `blochKet θ φ` — the column vector `cos(θ/2) |0⟩ + e^{iφ} sin(θ/2) |1⟩` of `ℂ²` (§1.2 eq. 1.4).
* `blochSphereVector θ φ` — the §1.2 Cartesian Bloch vector `(sin θ cos φ, sin θ sin φ, cos θ)`.
* `blochSphereVector_normSq` — it is a **unit vector**, `r₀² + r₁² + r₂² = 1` (so a pure state lies
  on the *surface* of the Bloch ball, matching Exercise 2.72(3)).
* `outerSelf_blochKet_eq_blochMatrix` — **the coincidence at the matrix level:** the outer product
  `|ψ(θ,φ)⟩⟨ψ(θ,φ)| = Concrete.outerSelf (blochKet θ φ)` equals `Concrete.blochMatrix
  (blochSphereVector θ φ)`, i.e. `½(I + r⃗·σ⃗)` with `r⃗` the §1.2 vector.

The state-level coincidence `|ψ⟩ = blochState r` for the pure state `PureState qubit` is in
`AxQM/Postulates/API/BlochState.lean` and `AxQM/NC/Ch2/Exercise2_72.lean`.

## Design notes

* The amplitudes are kept as `↑(Real.cos (θ/2))` and `Complex.exp (↑φ * I) · ↑(Real.sin (θ/2))`,
  faithful to N&C's `e^{iφ}`; the outer product `|ψ⟩⟨ψ|` reuses `Concrete.outerSelf v = vecMulVec v
  (star v)` from `Concrete.PauliEigenvectors`, so `star` supplies the bra automatically (eq. 2.20).
* The matrix identity is proved entrywise from `blochMatrix_eq` (the explicit `2 × 2` form) and the
  half-angle identities `cos²(θ/2) = (1+cos θ)/2`, `sin²(θ/2) = (1−cos θ)/2`,
  `2 sin(θ/2) cos(θ/2) = sin θ` (from `Real.cos_sq` / `Real.sin_two_mul`), with `e^{iφ}` expanded
  through `Complex.exp_mul_I`. This matches the entrywise idiom of `Concrete.BlochMatrix`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **§1.2 single-qubit pure-state vector** `|ψ(θ,φ)⟩ = cos(θ/2) |0⟩ + e^{iφ} sin(θ/2) |1⟩`
(Nielsen & Chuang eq. 1.4), as a column vector `Fin 2 → ℂ`. Its polar angle `θ` and azimuth `φ`
locate the state on the Bloch sphere. -/
noncomputable def blochKet (θ φ : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos (θ / 2) : ℂ), Complex.exp ((φ : ℂ) * Complex.I) * (Real.sin (θ / 2) : ℂ)]

/-- The **§1.2 Cartesian Bloch vector** `r⃗ = (sin θ cos φ, sin θ sin φ, cos θ)` of the pure state
`blochKet θ φ`: the spherical-to-Cartesian coordinates of the point `(θ, φ)` on the Bloch sphere
(Nielsen & Chuang §1.2, Figure 1.3), with the `z`-axis along `|0⟩`. -/
noncomputable def blochSphereVector (θ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- **The §1.2 Bloch vector is a unit vector:** `r₀² + r₁² + r₂² = 1` for `r⃗ = blochSphereVector θ
φ`. Indeed `sin²θ(cos²φ + sin²φ) + cos²θ = sin²θ + cos²θ = 1`. Consequently a pure state lies on the
*surface* `‖r⃗‖ = 1` of the Bloch ball (Nielsen & Chuang, Exercise 2.72(3)), and the vector is a
legitimate Bloch vector (`‖r⃗‖ ≤ 1`) for `Concrete.blochMatrix` / `blochState`. -/
theorem blochSphereVector_normSq (θ φ : ℝ) :
    blochSphereVector θ φ 0 ^ 2 + blochSphereVector θ φ 1 ^ 2
      + blochSphereVector θ φ 2 ^ 2 = 1 := by
  simp only [blochSphereVector, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

/-- **Nielsen & Chuang, Exercise 2.72(4), matrix level: the Bloch vector of the §1.2 pure state is
the §1.2 Cartesian vector.** The density matrix `|ψ(θ,φ)⟩⟨ψ(θ,φ)| = Concrete.outerSelf (blochKet θ
φ)` equals `Concrete.blochMatrix (blochSphereVector θ φ) = ½(I + r⃗·σ⃗)` with `r⃗ = (sin θ cos φ,
sin θ sin φ, cos θ)`. So the mixed-state Bloch vector of part (1), read off `½(I + r⃗·σ⃗)`,
coincides with the §1.2 parametrization for this pure state.

Proof: expand `e^{iφ} = cos φ + i sin φ` (`Complex.exp_mul_I`) and compare entries with the explicit
form `blochMatrix_eq`, using the half-angle identities `cos²(θ/2) = (1 + cos θ)/2`,
`sin²(θ/2) = (1 − cos θ)/2`, and `2 sin(θ/2) cos(θ/2) = sin θ`. E.g. the `(0,0)` entry is
`cos²(θ/2) = ½(1 + cos θ)`, the `(1,1)` entry `sin²(θ/2)(cos²φ + sin²φ) = ½(1 − cos θ)`, and the
off-diagonals `cos(θ/2) sin(θ/2) e^{∓iφ} = ½ sin θ · e^{∓iφ}`. -/
theorem outerSelf_blochKet_eq_blochMatrix (θ φ : ℝ) :
    outerSelf (blochKet θ φ) = blochMatrix (blochSphereVector θ φ) := by
  have hc : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
    have := Real.cos_sq (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; rw [this]; ring
  have hs : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have h1 := Real.sin_sq_add_cos_sq (θ / 2)
    have h2 := Real.cos_sq (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at h2; nlinarith [h1, h2]
  have hsc : 2 * Real.sin (θ / 2) * Real.cos (θ / 2) = Real.sin θ := by
    have := Real.sin_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; linarith [this]
  have hpyth : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  -- the two off-diagonal entries need `hsc` scaled by `cos φ` / `sin φ`.
  have hsc_c : 2 * Real.sin (θ / 2) * Real.cos (θ / 2) * Real.cos φ = Real.sin θ * Real.cos φ := by
    rw [hsc]
  have hsc_s : 2 * Real.sin (θ / 2) * Real.cos (θ / 2) * Real.sin φ = Real.sin θ * Real.sin φ := by
    rw [hsc]
  have hexp : Complex.exp ((φ : ℂ) * Complex.I)
      = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by norm_num
  rw [blochMatrix_eq]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, outerSelf_apply, blochKet, blochSphereVector,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two,
      Matrix.tail_cons, hexp, h2, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      Complex.neg_re, Complex.neg_im,
      RCLike.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I] <;>
    constructor <;> nlinarith [hc, hs, hsc, hpyth, hsc_c, hsc_s]

/-- The Bloch direction `blochSphereVector` is jointly continuous in `(θ, φ)`. -/
theorem continuous_blochSphereVector :
    Continuous (fun p : ℝ × ℝ => blochSphereVector p.1 p.2) := by
  apply continuous_pi; intro i
  fin_cases i <;> · simp only [blochSphereVector]; fun_prop

/-- For a fixed polar angle `θ`, the Bloch direction is continuous in the azimuth `φ`. -/
theorem continuous_blochSphereVector_snd (θ : ℝ) :
    Continuous (fun φ : ℝ => blochSphereVector θ φ) := by
  apply continuous_pi; intro i
  fin_cases i <;> · simp only [blochSphereVector]; fun_prop

end AxQM.Concrete
