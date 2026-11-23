/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Normed.Algebra.MatrixExponential
import ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Concrete: absorption by a detuned two-level block

This file gives the closed-form matrix
exponential of the `2 × 2` Hamiltonian block

`M(δ, g) = [[-δ, g], [g, δ]]`  (`detunedBlock`),

together with the resulting **absorption / loss probability**. This is the reusable computational
core behind the photon-absorption estimates of Nielsen & Chuang's cavity-QED cross-phase-modulation
model (§7.5.3): the survival amplitude `⟨0| exp(-i t M) |0⟩` for a single excitation coupled with
strength `g` to a two-level system detuned by `2δ`.

`M(δ, g)` is exactly the one-excitation block of the (generalised, non-resonant) Jaynes–Cummings
Hamiltonian: `-δ` and `δ` are the energies of the "photon present, atom in the ground level" and
"photon absorbed, atom excited" states, and `g` is the coupling that exchanges a quantum between
them (N&C eq. (7.84)). It is also the effective block governing the two-photon absorption of
Exercise 7.22 once the three-level `H₂` (eq. (7.85)) is reduced to its bright subspace, with the
single coupling `g` replaced by the effective coupling `√(gₐ² + g_b²)`; that reduction, and the
resulting comparison of the one- and two-photon losses, are built on this file.

## Main results

* `detunedBlock_mul_self` — the involution-up-to-scale `M² = (δ² + g²) • I`, the algebraic fact
  driving every closed form here.
* `detunedBlock_exp_apply_zero_zero` — the **survival amplitude**
  `⟨0| exp(-i t M) |0⟩ = cos(Ω t) + i (δ/Ω) sin(Ω t)`, where `Ω = √(δ² + g²)` is the generalised
  Rabi frequency (`Ω ≠ 0`, i.e. there is some coupling or detuning).
* `detunedBlock_absorptionProb` — the **absorption/loss probability**
  `1 - |⟨0| exp(-i t M) |0⟩|² = g²/(δ² + g²) · sin²(Ω t)`: the probability that the excitation has
  left the `|0⟩` state (been absorbed by the atom) after time `t`.

## Design notes

The statement uses Mathlib's matrix exponential `NormedSpace.exp`, the concrete `2 × 2` matrix
`detunedBlock`, `Complex.normSq`, and the real trigonometric functions. The proof of the amplitude
writes the exponent as `(θ i) • (M/Ω)` with the *involution* `(M/Ω)² = I` (`detunedBlock_mul_self`),
so the general Euler formula `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` gives the trigonometric
closed form directly; this reuses the same mechanism as `pauliDot_exp_of_unit` (Exercise 2.35). The
matrix exponential needs a norm to name its series; we supply the `ℓ^∞`-operator norm locally via
`open scoped Matrix.Norms.Operator`, exactly as Mathlib's own `Matrix.exp_*` lemmas do (the norm
choice does not affect the value of `exp`).
-/

namespace AxQM.Concrete

open NormedSpace Matrix

noncomputable section

open scoped Matrix.Norms.Operator

/-- The detuned two-level Hamiltonian block `M(δ, g) = [[-δ, g], [g, δ]]`: the one-excitation block
of the (non-resonant) Jaynes–Cummings Hamiltonian, with level splitting `2δ` and coupling `g`
(Nielsen & Chuang eq. (7.84)). -/
def detunedBlock (δ g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-δ : ℂ), (g : ℂ); (g : ℂ), (δ : ℂ)]

/-- `M(δ, g)² = (δ² + g²) • I`: the detuned block squares to a scalar, so `M/Ω` is an involution
for `Ω = √(δ² + g²)`. This is the algebraic content behind every closed form in this file. -/
theorem detunedBlock_mul_self (δ g : ℝ) :
    detunedBlock δ g * detunedBlock δ g
      = ((δ ^ 2 + g ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [detunedBlock]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Survival amplitude.** For the generalised Rabi frequency `Ω = √(δ² + g²) ≠ 0`,
`⟨0| exp(-i t M(δ, g)) |0⟩ = cos(Ω t) + i (δ/Ω) sin(Ω t)`.

Writing `-i t M = (θ i) • (M/Ω)` with `θ = -Ω t` and the involution `(M/Ω)² = I`
(`detunedBlock_mul_self`), the Euler formula `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` gives
`cos θ • I + i sin θ • (M/Ω)`; the `(0,0)` entry of `M/Ω` is `-δ/Ω`, and `cos`/`sin` are even/odd,
producing the stated form. -/
theorem detunedBlock_exp_apply_zero_zero (δ g t Ω : ℝ)
    (hΩ : Ω = Real.sqrt (δ ^ 2 + g ^ 2)) (hne : Ω ≠ 0) :
    (exp (-(Complex.I * (t : ℂ)) • detunedBlock δ g)) 0 0
      = (Real.cos (Ω * t) : ℂ) + ((δ / Ω * Real.sin (Ω * t) : ℝ) : ℂ) * Complex.I := by
  have hΩsq : (Ω : ℝ) ^ 2 = δ ^ 2 + g ^ 2 := by rw [hΩ]; exact Real.sq_sqrt (by positivity)
  have hΩC : ((Ω : ℂ)) ≠ 0 := by exact_mod_cast hne
  set a : Matrix (Fin 2) (Fin 2) ℂ := ((Ω : ℂ))⁻¹ • detunedBlock δ g with ha
  have haa : a * a = 1 := by
    have h1 : a * a
        = ((Ω : ℂ)⁻¹ * (Ω : ℂ)⁻¹ * ((δ ^ 2 + g ^ 2 : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [ha, Matrix.smul_mul, Matrix.mul_smul, detunedBlock_mul_self, smul_smul, smul_smul]
    rw [h1, show ((Ω : ℂ)⁻¹ * (Ω : ℂ)⁻¹ * ((δ ^ 2 + g ^ 2 : ℝ) : ℂ)) = 1 from ?_, one_smul]
    push_cast [← hΩsq]; field_simp
  have hrw : -(Complex.I * (t : ℂ)) • detunedBlock δ g
      = (((-(t * Ω) : ℝ) : ℂ) * Complex.I) • a := by
    rw [ha, smul_smul]; congr 1; push_cast; field_simp
  have haentry : a 0 0 = ((Ω : ℂ))⁻¹ * (-(δ : ℂ)) := by rw [ha]; simp [detunedBlock]
  clear_value a
  have hexpEq : exp (-(Complex.I * (t : ℂ)) • detunedBlock δ g)
      = (Real.cos (-(t * Ω)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + ((Real.sin (-(t * Ω)) : ℂ) * Complex.I) • a := by
    rw [hrw]; exact exp_smul_mul_I_of_mul_self_eq_one haa (-(t * Ω))
  rw [hexpEq, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_eq, haentry,
    Real.cos_neg, Real.sin_neg]
  simp only [mul_comm t Ω]
  push_cast
  ring

/-- **Absorption / loss probability.** For `Ω = √(δ² + g²) ≠ 0`,
`1 - |⟨0| exp(-i t M(δ, g)) |0⟩|² = g²/(δ² + g²) · sin²(Ω t)`: the probability that the excitation
has been absorbed (left the `|0⟩` state) after time `t`. Since `1 - cos²(Ω t) = sin²(Ω t)` and
`Ω² - δ² = g²`, the survival probability `cos²(Ω t) + (δ²/Ω²) sin²(Ω t)` loses exactly the
`(g²/Ω²) sin²(Ω t)` fraction. -/
theorem detunedBlock_absorptionProb (δ g t Ω : ℝ)
    (hΩ : Ω = Real.sqrt (δ ^ 2 + g ^ 2)) (hne : Ω ≠ 0) :
    1 - Complex.normSq ((exp (-(Complex.I * (t : ℂ)) • detunedBlock δ g)) 0 0)
      = g ^ 2 / (δ ^ 2 + g ^ 2) * Real.sin (Ω * t) ^ 2 := by
  have hΩsq : (Ω : ℝ) ^ 2 = δ ^ 2 + g ^ 2 := by rw [hΩ]; exact Real.sq_sqrt (by positivity)
  have hpos : δ ^ 2 + g ^ 2 ≠ 0 := by rw [← hΩsq]; exact pow_ne_zero 2 hne
  rw [detunedBlock_exp_apply_zero_zero δ g t Ω hΩ hne, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  field_simp
  rw [← hΩsq]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (Ω * t), sq_nonneg (Real.sin (Ω * t)), hΩsq]

end

end AxQM.Concrete
