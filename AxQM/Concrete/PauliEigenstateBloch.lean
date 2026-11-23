/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochPureState

/-!
# Concrete: the Pauli eigenvectors as §1.2 Bloch kets, and their Cartesian Bloch points

Supporting Nielsen & Chuang, Exercise 4.1 ("find the
points on the Bloch sphere for the normalized eigenvectors of the Pauli matrices", p. 174). At the
matrix/vector level it records two families of identities, at the six equator/pole points
`(θ,φ) ∈ {(π/2,0), (π/2,π), (π/2,π/2), (π/2,3π/2), (0,0), (π,0)}`:

* each normalized Pauli eigenvector of Exercise 2.11 (`|±⟩`, `|±i⟩`, `|0⟩`, `|1⟩`) *is* the §1.2
  Bloch ket `blochKet θ φ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩` (eq. 1.4) at that point; and
* the §1.2 Cartesian Bloch vector `blochSphereVector θ φ = (sin θ cos φ, sin θ sin φ, cos θ)` there
  evaluates to the corresponding coordinate axis `±x̂ / ±ŷ / ±ẑ`.

Everything is stated for raw matrix/vector data (`Fin 2 → ℂ`, `Fin 3 → ℝ`, `Concrete.blochKet`,
`Concrete.blochSphereVector`, the eigenvectors `xPlus`/`…`). Exercise 4.1
(`AxQM/NC/Ch4/Exercise4_1.lean`) builds on these identities.

## Design notes

* The amplitude `1/√2` shared by the `X`/`Y` eigenvectors is `Concrete.invSqrt2 = (√2)⁻¹`; it equals
  `cos(π/4) = sin(π/4) = √2/2` (`ofReal_cos_pi_div_four`, `ofReal_sin_pi_div_four`), the bridge to
  the half-angle values at `θ/2 = π/4`.
* The `e^{iφ}` factor is expanded via `Complex.exp_mul_I` to `cos φ + i sin φ` and the real trig
  evaluated at `φ ∈ {0, π/2, π, 3π/2}` (`3π/2 = π + π/2` via the addition formulas).
-/

namespace AxQM.Concrete

open Matrix Complex

/-! ### `1/√2 = cos(π/4) = sin(π/4)` -/

/-- `√2/2 = (√2)⁻¹` in `ℝ` (the two spellings of `1/√2`). -/
private theorem sqrt2_div_two : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [div_eq_iff (two_ne_zero), inv_mul_eq_div, eq_div_iff h2]
  exact Real.mul_self_sqrt (by norm_num)

/-- `cos(π/4) = 1/√2` (as a complex number): the `(θ = π/2)` half-angle value is the shared
`X`/`Y`-eigenvector amplitude `invSqrt2`. -/
theorem ofReal_cos_pi_div_four : ((Real.cos (Real.pi / 4) : ℝ) : ℂ) = invSqrt2 := by
  rw [Real.cos_pi_div_four, sqrt2_div_two, Complex.ofReal_inv, invSqrt2]

/-- `sin(π/4) = 1/√2` (as a complex number). -/
theorem ofReal_sin_pi_div_four : ((Real.sin (Real.pi / 4) : ℝ) : ℂ) = invSqrt2 := by
  rw [Real.sin_pi_div_four, sqrt2_div_two, Complex.ofReal_inv, invSqrt2]

/-! ### Trig values at `3π/2`, and the `e^{iφ}` phase factors -/

/-- `cos(3π/2) = 0` (`3π/2 = π + π/2`, addition formula). Not available upstream,
so a shared private fact reused by both `|-i⟩` identities. -/
private theorem cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show (3 * Real.pi / 2) = Real.pi + Real.pi / 2 by ring, Real.cos_add,
    Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring

/-- `sin(3π/2) = -1` (`3π/2 = π + π/2`, addition formula). Not available upstream, so a shared
private fact reused by both `|-i⟩` identities. -/
private theorem sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show (3 * Real.pi / 2) = Real.pi + Real.pi / 2 by ring, Real.sin_add,
    Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring

/-- `e^{i π/2} = i` (the §1.2 phase at `φ = π/2`): Mathlib's `Complex.exp_pi_div_two_mul_I` after
matching the coercion `↑(π/2) = ↑π/2`. -/
private theorem exp_pi_div_two_mul_I :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [show ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]

/-- `e^{i 3π/2} = -i` (the §1.2 phase at `φ = 3π/2`): `Complex.exp_mul_I` with the shared `3π/2`
trig values `cos_three_pi_div_two` / `sin_three_pi_div_two`. -/
private theorem exp_three_pi_div_two_mul_I :
    Complex.exp (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    cos_three_pi_div_two, sin_three_pi_div_two]
  push_cast; ring

/-! ### The Pauli eigenvectors as §1.2 Bloch kets

At `θ = π/2` the two half-angle amplitudes are both `1/√2`, so `blochKet (π/2) φ = (1/√2)(|0⟩ +
e^{iφ}|1⟩)`; the four equatorial eigenvectors are read off by evaluating `e^{iφ}`. -/

/-- **`blochKet (π/2) φ = (1/√2, e^{iφ}/√2)`** — the §1.2 pure state on the equator, in terms of its
phase `e^{iφ}`. The shared reduction behind the four `X`/`Y` eigenvector identities. -/
theorem blochKet_pi_div_two (φ : ℝ) :
    blochKet (Real.pi / 2) φ = ![invSqrt2, Complex.exp ((φ : ℂ) * Complex.I) * invSqrt2] := by
  funext i
  fin_cases i <;>
    simp only [blochKet, show (Real.pi / 2 / 2) = Real.pi / 4 by ring,
      ofReal_cos_pi_div_four, ofReal_sin_pi_div_four]

/-- **`|+⟩ = blochKet (π/2) 0`** — the `+1` eigenvector of `X` at equator azimuth `φ = 0`. -/
theorem blochKet_pi_div_two_zero : blochKet (Real.pi / 2) 0 = xPlus := by
  rw [blochKet_pi_div_two]
  funext i; fin_cases i <;> simp [xPlus]

/-- **`|-⟩ = blochKet (π/2) π`** — the `-1` eigenvector of `X` (`e^{iπ} = -1`). -/
theorem blochKet_pi_div_two_pi : blochKet (Real.pi / 2) Real.pi = xMinus := by
  rw [blochKet_pi_div_two, Complex.exp_pi_mul_I]
  funext i; fin_cases i <;> simp [xMinus]

/-- **`|+i⟩ = blochKet (π/2) (π/2)`** — the `+1` eigenvector of `Y` (`e^{iπ/2} = i`). -/
theorem blochKet_pi_div_two_pi_div_two : blochKet (Real.pi / 2) (Real.pi / 2) = yPlus := by
  unfold yPlus
  rw [blochKet_pi_div_two, exp_pi_div_two_mul_I, mul_comm]

/-- **`|-i⟩ = blochKet (π/2) (3π/2)`** — the `-1` eigenvector of `Y` (`e^{i3π/2} = -i`). -/
theorem blochKet_pi_div_two_three_pi_div_two :
    blochKet (Real.pi / 2) (3 * Real.pi / 2) = yMinus := by
  unfold yMinus
  rw [blochKet_pi_div_two, exp_three_pi_div_two_mul_I, neg_mul, mul_comm]

/-- **`|0⟩ = blochKet 0 0`** — the `+1` eigenvector of `Z` is the north pole `θ = 0`. -/
theorem blochKet_zero_zero : blochKet 0 0 = ket 0 := by
  funext i
  fin_cases i <;> simp [blochKet, ket]

/-- **`|1⟩ = blochKet π 0`** — the `-1` eigenvector of `Z` is the south pole `θ = π`. -/
theorem blochKet_pi_zero : blochKet Real.pi 0 = ket 1 := by
  funext i
  fin_cases i <;> simp [blochKet, ket, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-! ### The Cartesian Bloch points of the eigenvectors

`blochSphereVector θ φ = (sin θ cos φ, sin θ sin φ, cos θ)` evaluated at the six points. -/

/-- The Bloch point of `|+⟩` is `+x̂ = (1, 0, 0)`. -/
theorem blochSphereVector_pi_div_two_zero :
    blochSphereVector (Real.pi / 2) 0 = ![1, 0, 0] := by
  funext i
  fin_cases i <;> simp [blochSphereVector, Real.sin_pi_div_two, Real.cos_pi_div_two]

/-- The Bloch point of `|-⟩` is `-x̂ = (-1, 0, 0)`. -/
theorem blochSphereVector_pi_div_two_pi :
    blochSphereVector (Real.pi / 2) Real.pi = ![-1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [blochSphereVector, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi, Real.cos_pi]

/-- The Bloch point of `|+i⟩` is `+ŷ = (0, 1, 0)`. -/
theorem blochSphereVector_pi_div_two_pi_div_two :
    blochSphereVector (Real.pi / 2) (Real.pi / 2) = ![0, 1, 0] := by
  funext i
  fin_cases i <;> simp [blochSphereVector, Real.sin_pi_div_two, Real.cos_pi_div_two]

/-- The Bloch point of `|-i⟩` is `-ŷ = (0, -1, 0)`. -/
theorem blochSphereVector_pi_div_two_three_pi_div_two :
    blochSphereVector (Real.pi / 2) (3 * Real.pi / 2) = ![0, -1, 0] := by
  funext i
  fin_cases i <;> simp [blochSphereVector, Real.sin_pi_div_two, Real.cos_pi_div_two,
    cos_three_pi_div_two, sin_three_pi_div_two]

/-- The Bloch point of `|0⟩` is `+ẑ = (0, 0, 1)`. -/
theorem blochSphereVector_zero_zero :
    blochSphereVector 0 0 = ![0, 0, 1] := by
  funext i
  fin_cases i <;> simp [blochSphereVector]

/-- The Bloch point of `|1⟩` is `-ẑ = (0, 0, -1)`. -/
theorem blochSphereVector_pi_zero :
    blochSphereVector Real.pi 0 = ![0, 0, -1] := by
  funext i
  fin_cases i <;> simp [blochSphereVector, Real.sin_pi, Real.cos_pi]

end AxQM.Concrete
