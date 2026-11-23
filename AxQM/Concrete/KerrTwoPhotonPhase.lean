/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the two-photon Kerr phase shift (Nielsen & Chuang, Exercise 7.21)

Nielsen & Chuang §7.5.3 models the optical Kerr effect microscopically: two orthogonally polarised
photon modes `a`, `b` (each with at most one photon) interact with a single three-level atom, giving
a modified Jaynes–Cummings Hamiltonian (7.81). In the total-excitation basis the relevant part of
the Hamiltonian is block diagonal (7.82), `H = diag(H₀, H₁, H₂)`, with

* `H₀ = -δ` (7.83) on the vacuum `|000⟩`, and
* `H₂` (7.85) the `3 × 3` block on the two-excitation sector `|110⟩, |011⟩, |102⟩`:

`H₂ = !![-δ, gₐ, g_b; gₐ, δ, 0; g_b, 0, δ]`.

Writing the time-evolution operator `U = exp(iHt)` (Nielsen & Chuang p. 305 convention), the two
photon phase shift is `ϕ_ab = arg⟨110|U|110⟩ − arg⟨000|U|000⟩`. Exercise 7.21 asks to *explicitly
exponentiate* (7.82) and show (7.86)

`ϕ_ab = arg[e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)]`,   with `Ω' = √(δ² + gₐ² + g_b²)`.

## What is formalised

This is a pure matrix-exponential computation. The statement of Exercise 7.21 is in
`AxQM/NC/Ch7/Exercise7_21.lean`. Compare Exercise 7.16 (`AxQM/Concrete/DipoleSelectionRules.lean`).

* `kerrRabiFreq` — the generalised Rabi frequency `Ω' = √(δ² + gₐ² + g_b²)`.
* `kerrBlockTwo`, `kerrBlockZero` — the `H₂` (7.85) and `H₀` (7.83) blocks (over `ℂ`).
* `kerrBlockTwo_exp_apply_zero_zero_eigensum` — the **explicit exponentiation** of `H₂`: the `(0,0)`
  entry of `exp((it)·H₂)` as the eigenvalue expansion `∑ₖ |⟨110|kₖ⟩|² e^{iλₖt}` over the spectrum
  `{Ω', −Ω', δ}` of `H₂` (`H₂` is orthogonally diagonalised; `|110⟩` has no overlap with the
  `δ`-eigenvector, so only `±Ω'` contribute).
* `kerrBlockTwo_exp_apply_zero_zero` — the closed form `⟨110|U|110⟩ = cos Ω't − i(δ/Ω') sin Ω't`.
* `kerrBlockZero_exp_apply_zero_zero` — `⟨000|U|000⟩ = e^{-iδt}` (the `1 × 1` block `H₀ = -δ`).
* `kerrTwoPhotonPhase_ratio` — the exact amplitude ratio
  `⟨110|U|110⟩ / ⟨000|U|000⟩ = e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)`, the complex number whose
  argument is `ϕ_ab`.
* `kerrTwoPhotonPhase_arg` — Exercise 7.21, eq. (7.86):
  `ϕ_ab = arg[e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)]`.

A physically inessential nondegeneracy hypothesis `0 < gₐ² + g_b²` (there is a genuine atom–field
coupling — the interacting regime of N&C's Fig. 7.5, where `gₐ = g_b = 1`) makes `H₂`'s spectrum
simple and `Ω' > 0`, so the quotient `δ/Ω'` is well defined.

Computing the single-photon shifts `ϕ_a`, `ϕ_b` (the `4 × 4` block `H₁`, 7.84) and hence
`χ₃ = ϕ_ab − ϕ_a − ϕ_b` (the plotted Kerr shift, Fig. 7.5) is the exercise's follow-on numerical
discussion; the verifiable proposition (7.86) is `ϕ_ab`, formalised here.
-/

open scoped Matrix Matrix.Norms.Operator
open Matrix

noncomputable section

namespace AxQM.Concrete

/-- The **generalised Rabi frequency** `Ω' = √(δ² + gₐ² + g_b²)` of the modified Jaynes–Cummings
model (Nielsen & Chuang §7.5.3, eq. 7.86): the level splitting of the two-excitation sector. -/
def kerrRabiFreq (δ ga gb : ℝ) : ℝ := Real.sqrt (δ ^ 2 + ga ^ 2 + gb ^ 2)

/-- The **`H₂` block** (Nielsen & Chuang eq. 7.85) of the modified Jaynes–Cummings Hamiltonian on
the two-excitation sector, in the basis `|110⟩, |011⟩, |102⟩`:
`H₂ = !![-δ, gₐ, g_b; gₐ, δ, 0; g_b, 0, δ]`. Real detuning `δ` and couplings `gₐ, g_b`, as a complex
`3 × 3` matrix (so its matrix exponential is available). -/
def kerrBlockTwo (δ ga gb : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(δ : ℂ), (ga : ℂ), (gb : ℂ); (ga : ℂ), (δ : ℂ), 0; (gb : ℂ), 0, (δ : ℂ)]

/-- The **`H₀` block** (Nielsen & Chuang eq. 7.83) on the vacuum `|000⟩`: the `1 × 1` matrix `[-δ]`,
whose exponential gives the reference amplitude `⟨000|U|000⟩ = e^{-iδt}`. -/
def kerrBlockZero (δ : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := !![-(δ : ℂ)]

/-- **Explicit exponentiation of the `H₂` block** (Nielsen & Chuang eq. 7.85). Diagonalising `H₂`
over its spectrum `{Ω', −Ω', δ}` (with `Ω² = δ² + gₐ² + g_b²`), the `(0,0)` entry — the amplitude
`⟨110|exp(itH₂)|110⟩` — is the eigenvalue expansion
`(Ω−δ)²/N₊ · e^{iΩt} + (Ω+δ)²/N₋ · e^{−iΩt}` with `N₊ = (Ω−δ)² + gₐ² + g_b²`,
`N₋ = (Ω+δ)² + gₐ² + g_b²` (the squared norms of the two eigenvectors overlapping `|110⟩`; the
`δ`-eigenvector is orthogonal to `|110⟩` and drops out). Proved by writing `H₂ = P D P⁻¹` with `P`
the (unnormalised, orthogonal-column) eigenvector matrix, using `Matrix.exp_conj` and
`Matrix.exp_diagonal`. -/
theorem kerrBlockTwo_exp_apply_zero_zero_eigensum (δ ga gb t Ω : ℝ)
    (hΩ2 : Ω ^ 2 = δ ^ 2 + ga ^ 2 + gb ^ 2) (hg : 0 < ga ^ 2 + gb ^ 2) :
    (NormedSpace.exp ((Complex.I * t) • kerrBlockTwo δ ga gb)) 0 0
      = ((Ω : ℂ) - δ) ^ 2 * (((Ω : ℂ) - δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2)⁻¹
          * Complex.exp (Complex.I * t * Ω)
        + ((Ω : ℂ) + δ) ^ 2 * (((Ω : ℂ) + δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2)⁻¹
          * Complex.exp (Complex.I * t * -Ω) := by
  have hOm : (Ω : ℂ) ^ 2 = (δ : ℂ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 := by exact_mod_cast hΩ2
  have hNp : ((Ω : ℂ) - δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 ≠ 0 := by
    have hr : (0 : ℝ) < (Ω - δ) ^ 2 + ga ^ 2 + gb ^ 2 := by nlinarith [sq_nonneg (Ω - δ)]
    have : ((Ω : ℂ) - δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2
        = (((Ω - δ) ^ 2 + ga ^ 2 + gb ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast hr.ne'
  have hNm : ((Ω : ℂ) + δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 ≠ 0 := by
    have hr : (0 : ℝ) < (Ω + δ) ^ 2 + ga ^ 2 + gb ^ 2 := by nlinarith [sq_nonneg (Ω + δ)]
    have : ((Ω : ℂ) + δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2
        = (((Ω + δ) ^ 2 + ga ^ 2 + gb ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast hr.ne'
  have hNz : (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 ≠ 0 := by
    have : (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 = ((ga ^ 2 + gb ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast hg.ne'
  rw [kerrBlockTwo]
  set dl : ℂ := (δ : ℂ) with hdl
  set gA : ℂ := (ga : ℂ) with hgA
  set gB : ℂ := (gb : ℂ) with hgB
  set Om : ℂ := (Ω : ℂ) with hOmc
  set z : ℂ := Complex.I * (t : ℂ) with hz
  set Hm : Matrix (Fin 3) (Fin 3) ℂ := !![-dl, gA, gB; gA, dl, 0; gB, 0, dl] with hHmdef
  set Np : ℂ := (Om - dl) ^ 2 + gA ^ 2 + gB ^ 2 with hNpdef
  set Nm : ℂ := (Om + dl) ^ 2 + gA ^ 2 + gB ^ 2 with hNmdef
  set Nz : ℂ := gA ^ 2 + gB ^ 2 with hNzdef
  set Pr : Matrix (Fin 3) (Fin 3) ℂ := !![Om - dl, -Om - dl, 0; gA, gA, gB; gB, gB, -gA] with hPrdef
  set Dm : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![Om, -Om, dl] with hDmdef
  set DN : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![Np, Nm, Nz] with hDNdef
  set DNi : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![Np⁻¹, Nm⁻¹, Nz⁻¹] with hDNidef
  -- eigen-equation `H₂ P = P D`
  have hEig : Hm * Pr = Pr * Dm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [hHmdef, hPrdef, hDmdef, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_fin_one,
        Matrix.empty_val', Matrix.head_fin_const, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add,
        mul_neg, neg_zero] <;>
      (first | ring1 | linear_combination -hOm)
  -- orthogonality of eigenvectors: `Pᵀ P = diag(N₊, N₋, N_z)`
  have hGram : Prᵀ * Pr = DN := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [hPrdef, hDNdef, hNpdef, hNmdef, hNzdef, Matrix.transpose_apply, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.diagonal, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_fin_const, Fin.isValue,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero, zero_mul,
        zero_add] <;>
      (first | ring1 | linear_combination -hOm)
  have hDNiDN : DNi * DN = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [DNi, DN, Matrix.mul_apply, Matrix.diagonal, hNp, hNm, hNz]
  have hLeft : DNi * Prᵀ * Pr = 1 := by rw [Matrix.mul_assoc, hGram, hDNiDN]
  have hPrB : Pr * (DNi * Prᵀ) = 1 := mul_eq_one_comm.mp hLeft
  have hunit : IsUnit Pr := ⟨⟨Pr, DNi * Prᵀ, hPrB, hLeft⟩, rfl⟩
  have hinv : Pr⁻¹ = DNi * Prᵀ := Matrix.inv_eq_left_inv hLeft
  have hPrPinv : Pr * Pr⁻¹ = 1 := by rw [hinv]; exact hPrB
  have hHfact : z • Hm = Pr * (z • Dm) * Pr⁻¹ := by
    have hh : Hm = Pr * Dm * Pr⁻¹ := by rw [← hEig, Matrix.mul_assoc, hPrPinv, Matrix.mul_one]
    rw [hh, Matrix.mul_smul, Matrix.smul_mul]
  rw [hHfact, Matrix.exp_conj _ _ hunit]
  have hzD : z • Dm = Matrix.diagonal ![z * Om, z * (-Om), z * dl] := by
    rw [hDmdef]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.smul_apply]
  rw [hzD, Matrix.exp_diagonal, hinv]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    hPrdef, hDNidef, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_fin_one,
    Matrix.empty_val', Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    mul_zero, zero_mul, add_zero]
  ring

/-- **Exercise 7.21, the two-photon amplitude** `⟨110|U|110⟩` (with `U = exp(itH)`, N&C p. 305):
`⟨110|U|110⟩ = cos Ω't − i(δ/Ω') sin Ω't`, where `Ω' = kerrRabiFreq δ gₐ g_b`. The closed form of
the exponentiated `H₂` block (7.85), from the eigenvalue expansion via Euler's formula and
`N₊ = 2Ω'(Ω'−δ)`, `N₋ = 2Ω'(Ω'+δ)`. -/
theorem kerrBlockTwo_exp_apply_zero_zero (δ ga gb t : ℝ) (hg : 0 < ga ^ 2 + gb ^ 2) :
    (NormedSpace.exp ((Complex.I * t) • kerrBlockTwo δ ga gb)) 0 0
      = (Real.cos (kerrRabiFreq δ ga gb * t) : ℂ)
        - ((δ : ℂ) / (kerrRabiFreq δ ga gb : ℂ)) * (Real.sin (kerrRabiFreq δ ga gb * t) : ℂ)
          * Complex.I := by
  have hpos : 0 < δ ^ 2 + ga ^ 2 + gb ^ 2 := by nlinarith [sq_nonneg δ]
  set Ω : ℝ := kerrRabiFreq δ ga gb with hΩdef
  have hΩpos : 0 < Ω := Real.sqrt_pos.mpr hpos
  have hΩ2 : Ω ^ 2 = δ ^ 2 + ga ^ 2 + gb ^ 2 := Real.sq_sqrt hpos.le
  have hΩgt : δ ^ 2 < Ω ^ 2 := by rw [hΩ2]; nlinarith
  have hbound := abs_lt_of_sq_lt_sq' hΩgt hΩpos.le
  rw [kerrBlockTwo_exp_apply_zero_zero_eigensum δ ga gb t Ω hΩ2 hg]
  have hΩ2c : (Ω : ℂ) ^ 2 = (δ : ℂ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 := by exact_mod_cast hΩ2
  have hΩc0 : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩpos.ne'
  have hmδc : (Ω : ℂ) - δ ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast (ne_of_gt hbound.2)
  have hpδc : (Ω : ℂ) + δ ≠ 0 := by
    have : (0 : ℝ) < Ω + δ := by linarith [hbound.1]
    exact_mod_cast this.ne'
  have hE1 : Complex.exp (Complex.I * ↑t * ↑Ω)
      = ↑(Real.cos (Ω * t)) + ↑(Real.sin (Ω * t)) * Complex.I := by
    have he : Complex.I * ↑t * ↑Ω = ((Ω * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hE2 : Complex.exp (Complex.I * ↑t * -↑Ω)
      = ↑(Real.cos (Ω * t)) - ↑(Real.sin (Ω * t)) * Complex.I := by
    have he : Complex.I * ↑t * -↑Ω = ((-(Ω * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  rw [hE1, hE2,
    show ((Ω : ℂ) - δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 = 2 * Ω * (Ω - δ) from by
      linear_combination -hΩ2c,
    show ((Ω : ℂ) + δ) ^ 2 + (ga : ℂ) ^ 2 + (gb : ℂ) ^ 2 = 2 * Ω * (Ω + δ) from by
      linear_combination -hΩ2c]
  field_simp
  ring

/-- **The reference amplitude** `⟨000|U|000⟩` (`U = exp(itH)`): exponentiating the `1 × 1` block
`H₀ = -δ` (N&C eq. 7.83) gives `⟨000|U|000⟩ = e^{-iδt}`. -/
theorem kerrBlockZero_exp_apply_zero_zero (δ t : ℝ) :
    (NormedSpace.exp ((Complex.I * t) • kerrBlockZero δ)) 0 0
      = Complex.exp (Complex.I * t * -(δ : ℂ)) := by
  have h1 : (Complex.I * t) • kerrBlockZero δ = Matrix.diagonal ![Complex.I * t * -(δ : ℂ)] := by
    rw [kerrBlockZero]; ext i j; fin_cases i; fin_cases j
    simp [Matrix.diagonal, Matrix.smul_apply]
  rw [h1, Matrix.exp_diagonal]
  simp only [Matrix.diagonal_apply, Fin.isValue, ↓reduceIte, Pi.coe_exp, Matrix.cons_val_fin_one,
    ← Complex.exp_eq_exp_ℂ]

/-- **Exercise 7.21, the two-photon phase amplitude ratio** (Nielsen & Chuang eq. 7.86). The
complex number whose argument is the two-photon phase `ϕ_ab = arg⟨110|U|110⟩ − arg⟨000|U|000⟩`:
`⟨110|U|110⟩ / ⟨000|U|000⟩ = e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)`. The single `e^{iδt}` prefactor is
the reference phase `−arg⟨000|U|000⟩ = δt` of the vacuum. -/
theorem kerrTwoPhotonPhase_ratio (δ ga gb t : ℝ) (hg : 0 < ga ^ 2 + gb ^ 2) :
    (NormedSpace.exp ((Complex.I * t) • kerrBlockTwo δ ga gb)) 0 0
        / (NormedSpace.exp ((Complex.I * t) • kerrBlockZero δ)) 0 0
      = Complex.exp (Complex.I * δ * t)
        * ((Real.cos (kerrRabiFreq δ ga gb * t) : ℂ)
          - ((δ : ℂ) / (kerrRabiFreq δ ga gb : ℂ)) * (Real.sin (kerrRabiFreq δ ga gb * t) : ℂ)
            * Complex.I) := by
  rw [kerrBlockZero_exp_apply_zero_zero, kerrBlockTwo_exp_apply_zero_zero δ ga gb t hg,
    div_eq_mul_inv, ← Complex.exp_neg,
    show -(Complex.I * ↑t * -(δ : ℂ)) = Complex.I * ↑δ * ↑t from by ring]
  ring

/-- **Exercise 7.21 (Nielsen & Chuang eq. 7.86).** The two-photon Kerr phase shift
`ϕ_ab = arg⟨110|U|110⟩ − arg⟨000|U|000⟩` (`U = exp(itH)`) equals
`arg[e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)]`, with `Ω' = √(δ² + gₐ² + g_b²)`. Here `ϕ_ab` is realised
as the argument of the amplitude ratio `⟨110|U|110⟩ / ⟨000|U|000⟩` (`arg` of a quotient being the
difference of arguments, mod `2π` — the physical phase's inherent ambiguity), so the statement is
the argument of `kerrTwoPhotonPhase_ratio`. -/
theorem kerrTwoPhotonPhase_arg (δ ga gb t : ℝ) (hg : 0 < ga ^ 2 + gb ^ 2) :
    Complex.arg ((NormedSpace.exp ((Complex.I * t) • kerrBlockTwo δ ga gb)) 0 0
        / (NormedSpace.exp ((Complex.I * t) • kerrBlockZero δ)) 0 0)
      = Complex.arg (Complex.exp (Complex.I * δ * t)
        * ((Real.cos (kerrRabiFreq δ ga gb * t) : ℂ)
          - ((δ : ℂ) / (kerrRabiFreq δ ga gb : ℂ)) * (Real.sin (kerrRabiFreq δ ga gb * t) : ℂ)
            * Complex.I)) :=
  congrArg Complex.arg (kerrTwoPhotonPhase_ratio δ ga gb t hg)

end AxQM.Concrete

end
