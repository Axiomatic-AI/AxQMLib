/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import ToMathlib.Analysis.Calculus.Deriv.PolynomialIntegral
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Algebra.Polynomial

/-!
# Electric-dipole selection rules — spherical harmonics and the overlap integral (N&C 7.60)

This file develops the concrete special-function mathematics behind **Nielsen & Chuang,
Exercise 7.16** (p. 300): the electric-dipole *selection rules*. The physical setup (N&C §7.5.1)
is a matrix element `⟨ℓ₁,m₁| r̂ |ℓ₂,m₂⟩` of the position operator between hydrogenic orbital
wavefunctions; writing `r̂` in the `x̂–ŷ` plane in terms of the dipole spherical harmonics
`Y_{1,±1}` (N&C eq. 7.59), the angular part reduces to the **Gaunt-type overlap integral**

`∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ`   (N&C eq. 7.60),   with `m = ±1`,

which N&C assert is non-zero only when `m₂ − m₁ = ±1` (conservation of the `ẑ`-component of angular
momentum) and `Δℓ = ±1` (parity, plus the dipole triangle rule).

## The azimuthal `m`-rule

The spherical harmonics are modelled in the standard **separated** form
`Y_{ℓm}(θ,φ) = R_{ℓm}(θ)·e^{imφ}`
(N&C eq. 7.63), with the associated-Legendre radial factor of eq. 7.64 rewritten in `θ` to avoid
fractional powers: on `[0,π]` we have `sin θ ≥ 0`, so `(1−cos²θ)^{|m|/2} = (sin θ)^{|m|}`, and
`(d/dx)^{|m|} P_ℓ(x)` at `x = cos θ` is the `(ℓ+|m|)`-th derivative of the Rodrigues polynomial
`(X²−1)^ℓ` (the `1/(2^ℓ ℓ!)` of `P_ℓ`'s Rodrigues formula is folded into the normalization
`sphHarmNorm`). The `|m|` convention is used throughout; the exact normalization/phase is irrelevant
to the selection rules, which only concern *where the integral vanishes* and are invariant under any
nonzero rescaling of the harmonics.

* `sphHarmNorm`, `sphHarmRadial`, `sphHarm` — the spherical harmonic `Y_{ℓm}` (N&C 7.63/7.64).
* `dipoleOverlap` — the overlap integral (7.60), written as the iterated integral over `θ ∈ [0,π]`,
  `φ ∈ [0,2π]` with the solid-angle weight `sin θ` (so no Fubini/integrability lemmas are needed:
  the inner `φ`-integral already vanishes pointwise in `θ`).
* `dipoleOverlap_ne_zero_imp_azimuthal` — the **azimuthal (`m`) selection rule**: a nonvanishing
  overlap forces `m₁ = m + m₂`. This is the "conservation of angular momentum" half of the exercise,
  and follows from `∫₀^{2π} e^{ikφ} dφ = 0` for nonzero integer `k` (`integral_exp_int_period`).
* `dipoleOverlap_ne_zero_imp_delta_m` — the dipole corollary `m₂ − m₁ = ±1` for `m = ±1`, exactly as
  N&C state it.

The parity rule (`Δℓ` odd) and the triangle bound (`|Δℓ| ≤ 1`), which together give `Δℓ = ±1`, are
developed later in this file (`dipoleOverlap_ne_zero_imp_parity`,
`dipoleOverlap_ne_zero_imp_triangle`, `dipoleOverlap_ne_zero_imp_delta_l`), on top of the
definitions established here.

## Setting

Everything here is special-function mathematics — integrals of complex-valued functions built from
`Polynomial`/`Real.sin`/`Complex.exp` (compare Exercise 7.9). These are the statements of N&C
Exercise 7.16 (`AxQM/NC/Ch7/Exercise7_16.lean`).
-/

open scoped Real
open Polynomial

namespace AxQM.Concrete

/-- The φ-integral over a full period of `e^{ikφ}` vanishes for nonzero integer `k`: the algebraic
heart of the azimuthal selection rule. -/
lemma integral_exp_int_period (k : ℤ) (hk : k ≠ 0) :
    (∫ φ in (0:ℝ)..(2 * Real.pi), Complex.exp (↑k * ↑φ * Complex.I)) = 0 := by
  have hc : (↑k * Complex.I : ℂ) ≠ 0 := by simp [hk]
  have hrw : (fun φ : ℝ => Complex.exp (↑k * ↑φ * Complex.I))
      = (fun φ : ℝ => Complex.exp ((↑k * Complex.I) * ↑φ)) := by
    funext φ; ring_nf
  rw [hrw, integral_exp_mul_complex hc]
  rw [show (↑k * Complex.I * ↑(2 * Real.pi) : ℂ) = (↑k : ℂ) * (2 * ↑Real.pi * Complex.I) by
    push_cast; ring]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- A constant times a full-period `e^{ikφ}` integrates to zero for nonzero integer `k`. -/
lemma integral_const_mul_exp_int_period (C : ℂ) (k : ℤ) (hk : k ≠ 0) :
    (∫ φ in (0:ℝ)..(2 * Real.pi), C * Complex.exp (↑k * ↑φ * Complex.I)) = 0 := by
  have h1 : (∫ φ in (0:ℝ)..(2 * Real.pi), C * Complex.exp (↑k * ↑φ * Complex.I))
      = C * (∫ φ in (0:ℝ)..(2 * Real.pi), Complex.exp (↑k * ↑φ * Complex.I)) :=
    intervalIntegral.integral_const_mul C _
  rw [h1, integral_exp_int_period k hk, mul_zero]

/-- Normalization constant of the spherical harmonic `Y_{ℓm}`, N&C (7.63), with the `1/(2^ℓ ℓ!)`
of the Rodrigues formula (7.64) folded in (see `sphHarmRadial`). Uses the `|m|` convention. Its
value never enters the selection-rule proofs, which are invariant under nonzero rescaling. -/
noncomputable def sphHarmNorm (l : ℕ) (m : ℤ) : ℝ :=
  (-1) ^ m.natAbs * Real.sqrt ((2 * (l : ℝ) + 1) / (4 * Real.pi) *
      (((l - m.natAbs).factorial : ℝ) / ((l + m.natAbs).factorial : ℝ))) /
    (2 ^ l * (l.factorial : ℝ))

/-- The θ-radial part of the spherical harmonic `Y_{ℓm}`: N&C (7.63)/(7.64) written in `θ`. The
associated Legendre factor `(1−x²)^{|m|/2} · (d/dx)^{|m|} P_ℓ(x)` at `x = cos θ` becomes
`(sin θ)^{|m|} ·` the `(ℓ+|m|)`-th derivative of the Rodrigues polynomial `(X²−1)^ℓ` at `cos θ`
(the `1/(2^ℓ ℓ!)` of `P_ℓ` sits in `sphHarmNorm`), avoiding fractional powers since `sin θ ≥ 0` on
`[0,π]`. -/
noncomputable def sphHarmRadial (l : ℕ) (m : ℤ) (θ : ℝ) : ℝ :=
  sphHarmNorm l m * (Real.sin θ) ^ (m.natAbs) *
    (Polynomial.derivative^[l + m.natAbs] ((Polynomial.X ^ 2 - 1) ^ l)).eval (Real.cos θ)

/-- The spherical harmonic `Y_{ℓm}(θ,φ)` in separated form, N&C (7.63): a real θ-radial part times
the azimuthal phase `e^{imφ}`. -/
noncomputable def sphHarm (l : ℕ) (m : ℤ) (θ φ : ℝ) : ℂ :=
  (sphHarmRadial l m θ : ℂ) * Complex.exp (↑m * ↑φ * Complex.I)

/-- Complex conjugate of a spherical harmonic: the (real) radial part is unchanged and the phase is
conjugated. -/
lemma conj_sphHarm (l : ℕ) (m : ℤ) (θ φ : ℝ) :
    (starRingEnd ℂ) (sphHarm l m θ φ)
      = (sphHarmRadial l m θ : ℂ) * Complex.exp (-(↑m * ↑φ * Complex.I)) := by
  simp only [sphHarm, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_I]

/-! ### Parity machinery for the `Δℓ` selection rule

The reflection `θ ↦ π − θ` sends `cos θ ↦ −cos θ` and fixes `sin θ`; the radial factor of `Y_{ℓm}`
therefore picks up the parity sign of the polynomial `(d/dx)^{ℓ+|m|} (x²−1)^ℓ` under `x ↦ −x`. As
`(X²−1)^ℓ` is even and each differentiation flips parity, that sign is `(−1)^{ℓ+|m|}`. -/

/-- Reflection `p(X) ↦ p(−X)` anticommutes with one differentiation (chain rule `d/dx(−x) = −1`). -/
private lemma derivative_comp_neg_X (p : ℝ[X]) :
    Polynomial.derivative (p.comp (-X)) = -(Polynomial.derivative p).comp (-X) := by
  rw [Polynomial.derivative_comp]; simp

/-- The `k`-th derivative commutes with the reflection `X ↦ −X` up to the sign `(−1)^k`. -/
private lemma iterate_derivative_comp_neg_X (k : ℕ) (p : ℝ[X]) :
    Polynomial.derivative^[k] (p.comp (-X))
      = (-1 : ℝ[X]) ^ k * (Polynomial.derivative^[k] p).comp (-X) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply' Polynomial.derivative n (p.comp (-X)),
      Function.iterate_succ_apply' Polynomial.derivative n p, ih, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_pow, Polynomial.derivative_neg, Polynomial.derivative_one,
      neg_zero, zero_mul, mul_zero, zero_add]
    rw [derivative_comp_neg_X]
    ring

/-- The `(X²−1)^ℓ` Rodrigues base is invariant under `X ↦ −X` (it is even). -/
private lemma comp_neg_X_even (l : ℕ) : ((X ^ 2 - 1 : ℝ[X]) ^ l).comp (-X) = (X ^ 2 - 1) ^ l := by
  rw [Polynomial.pow_comp]
  congr 1
  simp [sub_comp]

/-- Parity of the iterated derivative of an even polynomial: for `p` with `p(−X) = p`, the `k`-th
derivative evaluated at `−x` is `(−1)^k` times its value at `x`. -/
private lemma iterate_derivative_even_eval_neg {p : ℝ[X]} (hp : p.comp (-X) = p) (k : ℕ) (x : ℝ) :
    (Polynomial.derivative^[k] p).eval (-x) = (-1) ^ k * (Polynomial.derivative^[k] p).eval x := by
  have h := iterate_derivative_comp_neg_X k p
  rw [hp] at h
  have h2 := congrArg (fun q : ℝ[X] => q.eval x) h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_comp, Polynomial.eval_X] at h2
  have hsq : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩
  rw [h2, ← mul_assoc, hsq, one_mul]

/-- **Radial reflection** `θ ↦ π − θ`: the `θ`-radial part of `Y_{ℓm}` picks up the parity sign
`(−1)^{ℓ+|m|}`. -/
lemma sphHarmRadial_pi_sub (l : ℕ) (m : ℤ) (θ : ℝ) :
    sphHarmRadial l m (Real.pi - θ) = (-1) ^ (l + m.natAbs) * sphHarmRadial l m θ := by
  unfold sphHarmRadial
  rw [Real.sin_pi_sub, Real.cos_pi_sub,
    iterate_derivative_even_eval_neg (comp_neg_X_even l) (l + m.natAbs) (Real.cos θ)]
  ring

/-- **Reflection** `θ ↦ π − θ` of the full spherical harmonic `Y_{ℓm}`: it picks up the parity sign
`(−1)^{ℓ+|m|}` (the azimuthal phase `e^{imφ}` is untouched by a `θ`-reflection). -/
lemma sphHarm_pi_sub (l : ℕ) (m : ℤ) (θ φ : ℝ) :
    sphHarm l m (Real.pi - θ) φ = (-1) ^ (l + m.natAbs) * sphHarm l m θ φ := by
  unfold sphHarm
  rw [sphHarmRadial_pi_sub]
  push_cast
  ring

/-- The electric-dipole overlap integral, N&C (7.60): `∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ` with the
solid-angle measure `dΩ = sin θ dθ dφ`, written as the iterated integral over `θ ∈ [0,π]`,
`φ ∈ [0,2π]`. The middle factor is the dipole harmonic `Y_{1,m}` (ℓ = 1). -/
noncomputable def dipoleOverlap (l₁ : ℕ) (m₁ m : ℤ) (l₂ : ℕ) (m₂ : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi, (∫ φ in (0:ℝ)..(2 * Real.pi),
      (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ) * (Real.sin θ : ℂ)

/-- **Azimuthal (`m`) selection rule**, the "conservation of angular momentum" half of N&C
Exercise 7.16: if the dipole overlap `∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ` is nonzero then `m₁ = m + m₂`.
The φ-integral of the phase `e^{i(m+m₂−m₁)φ}` over a full period vanishes unless the exponent is
zero, so a nonvanishing overlap forces `m₁ = m + m₂`. -/
theorem dipoleOverlap_ne_zero_imp_azimuthal
    {l₁ : ℕ} {m₁ m : ℤ} {l₂ : ℕ} {m₂ : ℤ}
    (h : dipoleOverlap l₁ m₁ m l₂ m₂ ≠ 0) : m₁ = m + m₂ := by
  by_contra hne
  apply h
  rw [dipoleOverlap]
  have hk : m + m₂ - m₁ ≠ 0 := by omega
  have hinner : ∀ θ : ℝ, (∫ φ in (0:ℝ)..(2 * Real.pi),
      (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ) = 0 := by
    intro θ
    have hfun : (fun φ : ℝ =>
          (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ)
        = (fun φ : ℝ => (↑(sphHarmRadial l₁ m₁ θ * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ) : ℂ)
                        * Complex.exp (↑(m + m₂ - m₁) * ↑φ * Complex.I)) := by
      funext φ
      have e1 : sphHarm 1 m θ φ
          = (sphHarmRadial 1 m θ : ℂ) * Complex.exp (↑m * ↑φ * Complex.I) := rfl
      have e2 : sphHarm l₂ m₂ θ φ
          = (sphHarmRadial l₂ m₂ θ : ℂ) * Complex.exp (↑m₂ * ↑φ * Complex.I) := rfl
      rw [conj_sphHarm, e1, e2]
      rw [show ((sphHarmRadial l₁ m₁ θ : ℂ) * Complex.exp (-(↑m₁ * ↑φ * Complex.I)))
            * ((sphHarmRadial 1 m θ : ℂ) * Complex.exp (↑m * ↑φ * Complex.I))
            * ((sphHarmRadial l₂ m₂ θ : ℂ) * Complex.exp (↑m₂ * ↑φ * Complex.I))
          = ((sphHarmRadial l₁ m₁ θ : ℂ) * (sphHarmRadial 1 m θ : ℂ) * (sphHarmRadial l₂ m₂ θ : ℂ))
            * (Complex.exp (-(↑m₁ * ↑φ * Complex.I)) * Complex.exp (↑m * ↑φ * Complex.I)
                * Complex.exp (↑m₂ * ↑φ * Complex.I)) by ring]
      rw [← Complex.exp_add, ← Complex.exp_add]
      rw [show (-(↑m₁ * ↑φ * Complex.I) + ↑m * ↑φ * Complex.I + ↑m₂ * ↑φ * Complex.I)
            = (↑(m + m₂ - m₁) : ℂ) * ↑φ * Complex.I by push_cast; ring]
      push_cast; ring
    rw [hfun]
    exact integral_const_mul_exp_int_period _ _ hk
  simp only [hinner, zero_mul, intervalIntegral.integral_zero]

/-- **Dipole azimuthal selection rule** (N&C Exercise 7.16, the `m₂ − m₁ = ±1` half): for the
electric-dipole harmonic `Y_{1,m}` with `m = ±1` (as in N&C eq. 7.59), a nonvanishing overlap
`∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ` forces `m₂ − m₁ = ±1`. -/
theorem dipoleOverlap_ne_zero_imp_delta_m
    {l₁ : ℕ} {m₁ m : ℤ} {l₂ : ℕ} {m₂ : ℤ} (hm : m = 1 ∨ m = -1)
    (h : dipoleOverlap l₁ m₁ m l₂ m₂ ≠ 0) : m₂ - m₁ = 1 ∨ m₂ - m₁ = -1 := by
  have hazi : m₁ = m + m₂ := dipoleOverlap_ne_zero_imp_azimuthal h
  rcases hm with hm | hm <;> omega

/-- **Reflection identity** for the dipole overlap. Substituting `θ ↦ π − θ` in the polar integral
reflects each spherical harmonic (a sign `(−1)^{ℓ+|m|}` apiece, `sphHarm_pi_sub`) and fixes the
`sin θ` weight, so the overlap equals itself times the total reflection sign
`(−1)^{ℓ₁+|m₁| + 1+|m| + ℓ₂+|m₂|}`. Whenever that sign is `−1` the overlap must vanish. -/
lemma dipoleOverlap_reflect (l₁ : ℕ) (m₁ m : ℤ) (l₂ : ℕ) (m₂ : ℤ) :
    dipoleOverlap l₁ m₁ m l₂ m₂
      = (-1 : ℂ) ^ (l₁ + m₁.natAbs + 1 + m.natAbs + l₂ + m₂.natAbs)
          * dipoleOverlap l₁ m₁ m l₂ m₂ := by
  rw [dipoleOverlap]
  set c : ℂ := (-1) ^ (l₁ + m₁.natAbs + 1 + m.natAbs + l₂ + m₂.natAbs) with hc
  set G : ℝ → ℂ := fun θ => (∫ φ in (0:ℝ)..(2 * Real.pi),
      (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ)
      * (Real.sin θ : ℂ) with hG
  have key : ∀ θ, G (Real.pi - θ) = c * G θ := by
    intro θ
    simp only [hG]
    rw [Real.sin_pi_sub]
    have hFF : ∀ φ : ℝ,
        (starRingEnd ℂ) (sphHarm l₁ m₁ (Real.pi - θ) φ) * sphHarm 1 m (Real.pi - θ) φ
            * sphHarm l₂ m₂ (Real.pi - θ) φ
          = c * ((starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ) := by
      intro φ
      rw [sphHarm_pi_sub l₁ m₁ θ φ, sphHarm_pi_sub 1 m θ φ, sphHarm_pi_sub l₂ m₂ θ φ, hc]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
    have h1 : (∫ φ in (0:ℝ)..(2 * Real.pi),
          (starRingEnd ℂ) (sphHarm l₁ m₁ (Real.pi - θ) φ) * sphHarm 1 m (Real.pi - θ) φ
            * sphHarm l₂ m₂ (Real.pi - θ) φ)
        = ∫ φ in (0:ℝ)..(2 * Real.pi),
          c * ((starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ) :=
      intervalIntegral.integral_congr (fun φ _ => hFF φ)
    have h2 : (∫ φ in (0:ℝ)..(2 * Real.pi),
          c * ((starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ))
        = c * ∫ φ in (0:ℝ)..(2 * Real.pi),
          (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ :=
      intervalIntegral.integral_const_mul c _
    rw [h1, h2]; ring
  calc (∫ θ in (0:ℝ)..Real.pi, G θ)
      = ∫ θ in (0:ℝ)..Real.pi, G (Real.pi - θ) := by
          rw [intervalIntegral.integral_comp_sub_left G Real.pi]; simp only [sub_self, sub_zero]
    _ = ∫ θ in (0:ℝ)..Real.pi, c * G θ := intervalIntegral.integral_congr (fun θ _ => key θ)
    _ = c * ∫ θ in (0:ℝ)..Real.pi, G θ := intervalIntegral.integral_const_mul c G

/-- **Parity selection rule** (the `Δℓ` odd half of N&C Exercise 7.16): a nonvanishing dipole
overlap `∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ` forces `ℓ₂ − ℓ₁` to be **odd**. Under the `θ`-reflection
each harmonic contributes `(−1)^{ℓ+|m|}` (`dipoleOverlap_reflect`); combined with the azimuthal
constraint `m₁ = m + m₂` (which makes `|m₁|+|m|+|m₂|` even), an even `ℓ₂ − ℓ₁` would make the total
reflection sign `−1`, forcing the overlap to vanish. This is the parity half of `Δℓ = ±1`; the
remaining triangle bound `|Δℓ| ≤ 1` (dipole `ℓ = 1`) is developed separately. -/
theorem dipoleOverlap_ne_zero_imp_parity
    {l₁ : ℕ} {m₁ m : ℤ} {l₂ : ℕ} {m₂ : ℤ}
    (h : dipoleOverlap l₁ m₁ m l₂ m₂ ≠ 0) : Odd ((l₂ : ℤ) - l₁) := by
  have hazi : m₁ = m + m₂ := dipoleOverlap_ne_zero_imp_azimuthal h
  by_contra hodd
  rw [Int.not_odd_iff_even] at hodd
  have hE : Odd (l₁ + m₁.natAbs + 1 + m.natAbs + l₂ + m₂.natAbs) := by
    rw [Nat.odd_iff]
    obtain ⟨j, hj⟩ := hodd
    omega
  refine h ?_
  have hrefl := dipoleOverlap_reflect l₁ m₁ m l₂ m₂
  have hx : dipoleOverlap l₁ m₁ m l₂ m₂ = - dipoleOverlap l₁ m₁ m l₂ m₂ := by
    conv_lhs => rw [hrefl]
    rw [Odd.neg_one_pow hE]; ring
  linear_combination (2⁻¹ : ℂ) * hx

/-! ### Reduction of the overlap to a real polynomial integral

Under `m₁ = m + m₂` the azimuthal phase is trivial (so the `φ`-integral gives `2π`) and, after
`x = cos θ` (with `sin θ dθ ↦ −dx`), the polar integral collapses to the integral over `[-1,1]` of a
*single real polynomial* `dipolePoly`. The combined `(sin θ)^{|m₁|+|m|+|m₂|}` weight is an even
power precisely because `m₁ = m + m₂`, giving the `(1−x²)ᵏ` factor with `k = (|m₁|+|m|+|m₂|)/2`. -/

/-- The real polynomial the overlap reduces to (under `m₁ = m + m₂`): the product of the three
associated-Legendre Rodrigues factors `(d/dx)^{ℓ+|m|}(x²−1)^ℓ` with the `(1−x²)ᵏ` from the combined
`sin`-weight, `k = (|m₁|+|m|+|m₂|)/2`. -/
noncomputable def dipolePoly (l₁ : ℕ) (m₁ m : ℤ) (l₂ : ℕ) (m₂ : ℤ) : ℝ[X] :=
  (1 - X ^ 2) ^ ((m₁.natAbs + m.natAbs + m₂.natAbs) / 2)
    * Polynomial.derivative^[l₁ + m₁.natAbs] ((X ^ 2 - 1) ^ l₁)
    * Polynomial.derivative^[1 + m.natAbs] ((X ^ 2 - 1) ^ 1)
    * Polynomial.derivative^[l₂ + m₂.natAbs] ((X ^ 2 - 1) ^ l₂)

/-- The dipole polynomial is symmetric under swapping the two outer harmonics `(ℓ₁,m₁) ↔ (ℓ₂,m₂)`
(the product commutes and `k` is symmetric); used to reduce the `ℓ₂ ≥ ℓ₁+2` triangle case to the
`ℓ₁ ≥ ℓ₂+2` one. -/
lemma dipolePoly_swap (l₁ : ℕ) (m₁ m : ℤ) (l₂ : ℕ) (m₂ : ℤ) :
    dipolePoly l₁ m₁ m l₂ m₂ = dipolePoly l₂ m₂ m l₁ m₁ := by
  unfold dipolePoly
  rw [show m₂.natAbs + m.natAbs + m₁.natAbs = m₁.natAbs + m.natAbs + m₂.natAbs by ring]
  ring

/-- **Reduction to a polynomial integral.** Under the azimuthal constraint `m₁ = m + m₂`, the dipole
overlap (7.60) equals `2π` times the (real) normalization product times the integral of `dipolePoly`
over `[-1,1]`. This isolates all the `Δℓ` content into a single real polynomial integral. -/
lemma dipoleOverlap_eq_dipolePoly_integral (l₁ : ℕ) (m₁ m : ℤ) (l₂ : ℕ) (m₂ : ℤ)
    (hm : m₁ = m + m₂) :
    dipoleOverlap l₁ m₁ m l₂ m₂
      = (2 * Real.pi : ℂ) * ↑(sphHarmNorm l₁ m₁ * sphHarmNorm 1 m * sphHarmNorm l₂ m₂
          * ∫ x in (-1:ℝ)..1, (dipolePoly l₁ m₁ m l₂ m₂).eval x) := by
  -- Step 1: the inner φ-integral is `2π` times the radial product.
  have hinner : ∀ θ : ℝ,
      (∫ φ in (0:ℝ)..(2 * Real.pi),
        (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ)
        = (2 * Real.pi : ℂ)
          * ↑(sphHarmRadial l₁ m₁ θ * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ) := by
    intro θ
    have hfun : (fun φ : ℝ =>
          (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ)
        = (fun _ : ℝ =>
            (↑(sphHarmRadial l₁ m₁ θ * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ) : ℂ)) := by
      funext φ
      have e1 : sphHarm 1 m θ φ
          = (sphHarmRadial 1 m θ : ℂ) * Complex.exp (↑m * ↑φ * Complex.I) := rfl
      have e2 : sphHarm l₂ m₂ θ φ
          = (sphHarmRadial l₂ m₂ θ : ℂ) * Complex.exp (↑m₂ * ↑φ * Complex.I) := rfl
      rw [conj_sphHarm, e1, e2]
      rw [show ((sphHarmRadial l₁ m₁ θ : ℂ) * Complex.exp (-(↑m₁ * ↑φ * Complex.I)))
            * ((sphHarmRadial 1 m θ : ℂ) * Complex.exp (↑m * ↑φ * Complex.I))
            * ((sphHarmRadial l₂ m₂ θ : ℂ) * Complex.exp (↑m₂ * ↑φ * Complex.I))
          = ((sphHarmRadial l₁ m₁ θ : ℂ) * (sphHarmRadial 1 m θ : ℂ) * (sphHarmRadial l₂ m₂ θ : ℂ))
            * (Complex.exp (-(↑m₁ * ↑φ * Complex.I)) * Complex.exp (↑m * ↑φ * Complex.I)
                * Complex.exp (↑m₂ * ↑φ * Complex.I)) by ring]
      rw [← Complex.exp_add, ← Complex.exp_add]
      rw [show (-(↑m₁ * ↑φ * Complex.I) + ↑m * ↑φ * Complex.I + ↑m₂ * ↑φ * Complex.I)
            = ((↑(m + m₂ - m₁) : ℂ) * ↑φ * Complex.I) by push_cast; ring]
      rw [show (m + m₂ - m₁ : ℤ) = 0 by omega]
      push_cast
      simp
    rw [hfun, intervalIntegral.integral_ofReal, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero]
    push_cast; ring
  -- Step 2: the pointwise reduction of the radial product to `dipolePoly ∘ cos`.
  have heven : m₁.natAbs + m.natAbs + m₂.natAbs
      = 2 * ((m₁.natAbs + m.natAbs + m₂.natAbs) / 2) := by omega
  have hpt : ∀ θ : ℝ,
      sphHarmRadial l₁ m₁ θ * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ * Real.sin θ
        = (sphHarmNorm l₁ m₁ * sphHarmNorm 1 m * sphHarmNorm l₂ m₂)
            * ((dipolePoly l₁ m₁ m l₂ m₂).eval (Real.cos θ) * Real.sin θ) := by
    intro θ
    set k := (m₁.natAbs + m.natAbs + m₂.natAbs) / 2 with hk
    set s := Real.sin θ with hs
    set c := Real.cos θ with hc
    set N₁ := sphHarmNorm l₁ m₁; set Nm := sphHarmNorm 1 m; set N₂ := sphHarmNorm l₂ m₂
    set Q₁ := (Polynomial.derivative^[l₁ + m₁.natAbs] ((X ^ 2 - 1) ^ l₁)).eval c with hQ₁
    set Qm := (Polynomial.derivative^[1 + m.natAbs] ((X ^ 2 - 1) ^ 1)).eval c with hQm
    set Q₂ := (Polynomial.derivative^[l₂ + m₂.natAbs] ((X ^ 2 - 1) ^ l₂)).eval c with hQ₂
    have hsin : s ^ m₁.natAbs * s ^ m.natAbs * s ^ m₂.natAbs = (1 - c ^ 2) ^ k := by
      rw [← pow_add, ← pow_add, heven, pow_mul, hs, Real.sin_sq, ← hc]
    have hdip : (dipolePoly l₁ m₁ m l₂ m₂).eval c = (1 - c ^ 2) ^ k * Q₁ * Qm * Q₂ := by
      simp only [dipolePoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X, hQ₁, hQm, hQ₂, ← hk]
    simp only [sphHarmRadial, hdip]
    calc N₁ * s ^ m₁.natAbs * Q₁ * (Nm * s ^ m.natAbs * Qm) * (N₂ * s ^ m₂.natAbs * Q₂) * s
        = N₁ * Nm * N₂ * (s ^ m₁.natAbs * s ^ m.natAbs * s ^ m₂.natAbs) * (Q₁ * Qm * Q₂) * s := by
          ring
      _ = N₁ * Nm * N₂ * ((1 - c ^ 2) ^ k) * (Q₁ * Qm * Q₂) * s := by rw [hsin]
      _ = N₁ * Nm * N₂ * ((1 - c ^ 2) ^ k * Q₁ * Qm * Q₂ * s) := by ring
  -- Step 3: the change of variables `x = cos θ`.
  have hsub : (∫ θ in (0:ℝ)..Real.pi, (dipolePoly l₁ m₁ m l₂ m₂).eval (Real.cos θ) * Real.sin θ)
      = ∫ x in (-1:ℝ)..1, (dipolePoly l₁ m₁ m l₂ m₂).eval x := by
    have hcomp := intervalIntegral.integral_deriv_smul_comp (a := (0:ℝ)) (b := Real.pi)
      (f := Real.cos) (f' := fun x => -Real.sin x)
      (g := fun x => (dipolePoly l₁ m₁ m l₂ m₂).eval x)
      (fun x _ => Real.hasDerivAt_cos x)
      (Real.continuous_sin.neg.continuousOn) (Polynomial.continuous _)
    simp only [Real.cos_zero, Real.cos_pi, Function.comp, smul_eq_mul] at hcomp
    -- hcomp : ∫ θ in 0..π, -sin θ * eval (cos θ) = ∫ x in 1..-1, eval x
    have hneg : (∫ θ in (0:ℝ)..Real.pi, -Real.sin θ * (dipolePoly l₁ m₁ m l₂ m₂).eval (Real.cos θ))
        = -∫ θ in (0:ℝ)..Real.pi, (dipolePoly l₁ m₁ m l₂ m₂).eval (Real.cos θ) * Real.sin θ := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr; intro θ _; ring
    rw [hneg, intervalIntegral.integral_symm (-1) 1, neg_inj] at hcomp
    exact hcomp
  -- The real θ-integral reduces to the polynomial integral over `[-1,1]`.
  have hreal : (∫ θ in (0:ℝ)..Real.pi,
        sphHarmRadial l₁ m₁ θ * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ * Real.sin θ)
      = (sphHarmNorm l₁ m₁ * sphHarmNorm 1 m * sphHarmNorm l₂ m₂)
          * ∫ x in (-1:ℝ)..1, (dipolePoly l₁ m₁ m l₂ m₂).eval x := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
      intervalIntegral.integral_const_mul (sphHarmNorm l₁ m₁ * sphHarmNorm 1 m * sphHarmNorm l₂ m₂),
      hsub]
  -- Assemble.
  rw [dipoleOverlap]
  calc (∫ θ in (0:ℝ)..Real.pi,
          (∫ φ in (0:ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (sphHarm l₁ m₁ θ φ) * sphHarm 1 m θ φ * sphHarm l₂ m₂ θ φ)
            * (Real.sin θ : ℂ))
      = ∫ θ in (0:ℝ)..Real.pi, (2 * Real.pi : ℂ) * ↑(sphHarmRadial l₁ m₁ θ
          * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ * Real.sin θ) := by
        apply intervalIntegral.integral_congr; intro θ _; dsimp only; rw [hinner θ]; push_cast; ring
    _ = (2 * Real.pi : ℂ) * ∫ θ in (0:ℝ)..Real.pi, (↑(sphHarmRadial l₁ m₁ θ
          * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ * Real.sin θ) : ℂ) :=
        intervalIntegral.integral_const_mul _ _
    _ = (2 * Real.pi : ℂ) * ↑(∫ θ in (0:ℝ)..Real.pi,
          sphHarmRadial l₁ m₁ θ * sphHarmRadial 1 m θ * sphHarmRadial l₂ m₂ θ * Real.sin θ) := by
        rw [intervalIntegral.integral_ofReal]
    _ = (2 * Real.pi : ℂ) * ↑(sphHarmNorm l₁ m₁ * sphHarmNorm 1 m * sphHarmNorm l₂ m₂
          * ∫ x in (-1:ℝ)..1, (dipolePoly l₁ m₁ m l₂ m₂).eval x) := by rw [hreal]

/-! ### The triangle bound and `Δℓ = ±1`

The `Δℓ = ±1` half rests on two general, dipole-agnostic facts, now in `ToMathlib/`
(`ToMathlib.Analysis.Calculus.Deriv.PolynomialIntegral`): the Rodrigues integration by parts
`Polynomial.integral_iterate_derivative_mul` and the vanishing lemma
`Polynomial.eval_iterate_derivative_eq_zero_of_dvd`. -/

/-- **Vanishing of the polynomial integral when `ℓ₁ ≥ ℓ₂ + 2`** (with `|m₁| ≤ k`,
`k = (|m₁|+|m|+|m₂|)/2`). Writing `dipolePoly = (dⁿ/dxⁿ (x²−1)^ℓ₁)·S` (`n = ℓ₁+|m₁|`, `S` vanishing
to order `≥ k ≥ |m₁|` at `±1`), Rodrigues IBP moves all `n` derivatives onto `S`, where
`deg S = ℓ₂+|m₁|+1 < n`, so `dⁿ/dxⁿ S = 0`. -/
lemma dipolePoly_integral_eq_zero_of_lt (l₁ : ℕ) (m₁ m : ℤ) (l₂ : ℕ) (m₂ : ℤ)
    (hlt : l₂ + 1 < l₁) (hmb : m₁.natAbs ≤ (m₁.natAbs + m.natAbs + m₂.natAbs) / 2) :
    (∫ x in (-1:ℝ)..1, (dipolePoly l₁ m₁ m l₂ m₂).eval x) = 0 := by
  set k := (m₁.natAbs + m.natAbs + m₂.natAbs) / 2 with hk
  -- If any Rodrigues factor is zero, `dipolePoly = 0` and the integral is trivially zero.
  rcases eq_or_ne (Polynomial.derivative^[1 + m.natAbs] ((X ^ 2 - 1 : ℝ[X]) ^ 1)) 0 with hQm | hQm
  · have hz : dipolePoly l₁ m₁ m l₂ m₂ = 0 := by simp only [dipolePoly, hQm, mul_zero, zero_mul]
    rw [hz]; simp
  rcases eq_or_ne (Polynomial.derivative^[l₂ + m₂.natAbs] ((X ^ 2 - 1 : ℝ[X]) ^ l₂)) 0 with
    hQ2 | hQ2
  · have hz : dipolePoly l₁ m₁ m l₂ m₂ = 0 := by simp only [dipolePoly, hQ2, mul_zero]
    rw [hz]; simp
  -- The nonvanishing factors force `|m| ≤ 1` and `|m₂| ≤ ℓ₂`.
  have hm_le : m.natAbs ≤ 1 := by
    by_contra hc
    refine hQm (Polynomial.iterate_derivative_eq_zero ?_)
    calc ((X ^ 2 - 1 : ℝ[X]) ^ 1).natDegree ≤ 2 := by compute_degree!
      _ < 1 + m.natAbs := by omega
  have hm2_le : m₂.natAbs ≤ l₂ := by
    by_contra hc
    refine hQ2 (Polynomial.iterate_derivative_eq_zero ?_)
    have hb : (X ^ 2 - 1 : ℝ[X]).natDegree ≤ 2 := by compute_degree!
    calc ((X ^ 2 - 1 : ℝ[X]) ^ l₂).natDegree
          ≤ l₂ * (X ^ 2 - 1 : ℝ[X]).natDegree := Polynomial.natDegree_pow_le
      _ ≤ l₂ * 2 := by gcongr
      _ < l₂ + m₂.natAbs := by omega
  -- Factor `dipolePoly = (dⁿ/dxⁿ u)·S`.
  set u : ℝ[X] := (X ^ 2 - 1) ^ l₁ with hu
  set S : ℝ[X] := (1 - X ^ 2) ^ k * Polynomial.derivative^[1 + m.natAbs] ((X ^ 2 - 1) ^ 1)
      * Polynomial.derivative^[l₂ + m₂.natAbs] ((X ^ 2 - 1) ^ l₂) with hS
  have hfact : dipolePoly l₁ m₁ m l₂ m₂ = Polynomial.derivative^[l₁ + m₁.natAbs] u * S := by
    rw [hS, hu, dipolePoly, ← hk]; ring
  -- Divisibilities: `u` vanishes to order `ℓ₁`, `S` to order `k`, at both `±1`.
  have hdu1 : (X - C (1:ℝ)) ^ l₁ ∣ u := by
    rw [hu]; exact pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.2 (by simp)) l₁
  have hdum1 : (X - C (-1:ℝ)) ^ l₁ ∣ u := by
    rw [hu]; exact pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.2 (by simp)) l₁
  have hdS1 : (X - C (1:ℝ)) ^ k ∣ S := by
    rw [hS]
    exact ((pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.2 (by simp)) k).mul_right _).mul_right _
  have hdSm1 : (X - C (-1:ℝ)) ^ k ∣ S := by
    rw [hS]
    exact ((pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.2 (by simp)) k).mul_right _).mul_right _
  -- Boundary products vanish at both endpoints.
  have hbdry1 : ∀ a b, a + b + 1 = l₁ + m₁.natAbs →
      (Polynomial.derivative^[a] u).eval 1 * (Polynomial.derivative^[b] S).eval 1 = 0 := by
    intro a b hab
    rcases lt_or_ge a l₁ with ha | ha
    · rw [eval_iterate_derivative_eq_zero_of_dvd hdu1 ha, zero_mul]
    · rw [eval_iterate_derivative_eq_zero_of_dvd hdS1 (show b < k by omega), mul_zero]
  have hbdrym1 : ∀ a b, a + b + 1 = l₁ + m₁.natAbs →
      (Polynomial.derivative^[a] u).eval (-1) * (Polynomial.derivative^[b] S).eval (-1) = 0 := by
    intro a b hab
    rcases lt_or_ge a l₁ with ha | ha
    · rw [eval_iterate_derivative_eq_zero_of_dvd hdum1 ha, zero_mul]
    · rw [eval_iterate_derivative_eq_zero_of_dvd hdSm1 (show b < k by omega), mul_zero]
  -- The degree bound `deg S < ℓ₁ + |m₁|`.
  have hSdeg : S.natDegree < l₁ + m₁.natAbs := by
    have e1 : ((1 - X ^ 2 : ℝ[X]) ^ k).natDegree ≤ k * 2 := by
      have hb : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 := by compute_degree!
      exact Polynomial.natDegree_pow_le.trans (by gcongr)
    have e2 : (Polynomial.derivative^[1 + m.natAbs] ((X ^ 2 - 1 : ℝ[X]) ^ 1)).natDegree
        ≤ 2 - (1 + m.natAbs) := by
      refine (Polynomial.natDegree_iterate_derivative _ _).trans ?_
      have : ((X ^ 2 - 1 : ℝ[X]) ^ 1).natDegree ≤ 2 := by compute_degree!
      omega
    have e3 : (Polynomial.derivative^[l₂ + m₂.natAbs] ((X ^ 2 - 1 : ℝ[X]) ^ l₂)).natDegree
        ≤ 2 * l₂ - (l₂ + m₂.natAbs) := by
      refine (Polynomial.natDegree_iterate_derivative _ _).trans ?_
      have hb : (X ^ 2 - 1 : ℝ[X]).natDegree ≤ 2 := by compute_degree!
      have : ((X ^ 2 - 1 : ℝ[X]) ^ l₂).natDegree ≤ l₂ * 2 :=
        Polynomial.natDegree_pow_le.trans (by gcongr)
      omega
    have hb : S.natDegree ≤ ((1 - X ^ 2 : ℝ[X]) ^ k).natDegree
        + (Polynomial.derivative^[1 + m.natAbs] ((X ^ 2 - 1 : ℝ[X]) ^ 1)).natDegree
        + (Polynomial.derivative^[l₂ + m₂.natAbs] ((X ^ 2 - 1 : ℝ[X]) ^ l₂)).natDegree := by
      rw [hS]
      exact Polynomial.natDegree_mul_le.trans (add_le_add Polynomial.natDegree_mul_le le_rfl)
    omega
  -- Assemble via the Rodrigues integration by parts.
  rw [hfact]
  simp only [Polynomial.eval_mul]
  rw [integral_iterate_derivative_mul (l₁ + m₁.natAbs) u S hbdry1 hbdrym1,
    Polynomial.iterate_derivative_eq_zero hSdeg]
  simp

/-- **Dipole triangle bound** (N&C Exercise 7.16, the `|Δℓ| ≤ 1` half). A nonvanishing overlap
`∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ` forces `|ℓ₂ − ℓ₁| ≤ 1` (the dipole harmonic has `ℓ = 1`).
Reducing to `dipolePoly` under the azimuthal constraint (`dipoleOverlap_eq_dipolePoly_integral`),
both `ℓ₁ ≥ ℓ₂+2` and `ℓ₂ ≥ ℓ₁+2` make that polynomial integral vanish
(`dipolePoly_integral_eq_zero_of_lt`, using `dipolePoly_swap` for the second). -/
theorem dipoleOverlap_ne_zero_imp_triangle
    {l₁ : ℕ} {m₁ m : ℤ} {l₂ : ℕ} {m₂ : ℤ}
    (h : dipoleOverlap l₁ m₁ m l₂ m₂ ≠ 0) : (l₁ : ℤ) ≤ l₂ + 1 ∧ (l₂ : ℤ) ≤ l₁ + 1 := by
  have hazi : m₁ = m + m₂ := dipoleOverlap_ne_zero_imp_azimuthal h
  refine ⟨?_, ?_⟩
  · by_contra hc
    rw [not_le] at hc
    refine h ?_
    rw [dipoleOverlap_eq_dipolePoly_integral l₁ m₁ m l₂ m₂ hazi,
      dipolePoly_integral_eq_zero_of_lt l₁ m₁ m l₂ m₂ (by omega) (by omega)]
    simp
  · by_contra hc
    rw [not_le] at hc
    refine h ?_
    rw [dipoleOverlap_eq_dipolePoly_integral l₁ m₁ m l₂ m₂ hazi]
    have hz : (∫ x in (-1:ℝ)..1, (dipolePoly l₁ m₁ m l₂ m₂).eval x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun x => (dipolePoly l₂ m₂ m l₁ m₁).eval x)
          (fun x _ => by dsimp only; rw [dipolePoly_swap])]
      exact dipolePoly_integral_eq_zero_of_lt l₂ m₂ m l₁ m₁ (by omega) (by omega)
    rw [hz]; simp

/-- **The `Δℓ = ±1` selection rule** (N&C Exercise 7.16, second stated rule). Combining the parity
rule `Odd (ℓ₂ − ℓ₁)` (`dipoleOverlap_ne_zero_imp_parity`) with the triangle bound `|ℓ₂ − ℓ₁| ≤ 1`
(`dipoleOverlap_ne_zero_imp_triangle`), a nonvanishing overlap forces `ℓ₂ − ℓ₁ = ±1`. -/
theorem dipoleOverlap_ne_zero_imp_delta_l
    {l₁ : ℕ} {m₁ m : ℤ} {l₂ : ℕ} {m₂ : ℤ}
    (h : dipoleOverlap l₁ m₁ m l₂ m₂ ≠ 0) : (l₂ : ℤ) - l₁ = 1 ∨ (l₂ : ℤ) - l₁ = -1 := by
  have hpar : Odd ((l₂ : ℤ) - l₁) := dipoleOverlap_ne_zero_imp_parity h
  obtain ⟨htri1, htri2⟩ := dipoleOverlap_ne_zero_imp_triangle h
  obtain ⟨j, hj⟩ := hpar
  omega

end AxQM.Concrete
