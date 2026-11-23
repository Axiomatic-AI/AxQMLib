/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochPureState
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Concrete: the spherical average over the unit sphere, and `⟨nₐn_b⟩ = δₐb/3`

This file defines the **spherical average**
of a function of the unit direction `n̂` and computes the second-moment identity

`⟨nₐ n_b⟩ = (1/3) δₐb`,

the analytic heart of Nielsen & Chuang, Exercise 7.35 (motional narrowing, p. 328).

## The spherical average

For `f : (Fin 3 → ℝ) → ℂ`, the **spherical average** over all unit directions `n̂` is the mean value
of `f n̂` over the unit sphere. Parametrising `n̂` by spherical coordinates `(θ, φ)` via
`blochSphereVector θ φ = (sin θ cos φ, sin θ sin φ, cos θ)` and using the solid-angle
weight `sin θ`, this is the iterated interval integral

`sphericalAverage f = (4π)⁻¹ ∫₀^π (∫₀^{2π} f(n̂(θ,φ)) dφ) sin θ dθ`,

the normalisation `(4π)⁻¹` being the reciprocal of the total solid angle `∫₀^π sin θ dθ ∫₀^{2π} dφ =
2 · 2π = 4π`. This is the same iterated `∫θ (∫φ …) sin θ` shape used for the solid-angle overlap
integral `Concrete.dipoleOverlap` (Ex. 7.16); we take the parametrisation as the definition of the
average rather than routing through the abstract surface measure `Measure.toSphere`, which would
make the value computation `⟨nₐ n_b⟩ = δₐb/3` far harder.

## The declarations

* `sphericalAverage` / `realSphericalAverage` — the complex- and real-valued spherical average.
* `sphericalAverage_ofReal` — the average of a real integrand is the coercion of its real average.
* `realSphericalAverage_separable` — for a **separable** folded integrand `n̂(θ,φ) ↦ P θ · Q φ`,
  the average factors as `(4π)⁻¹ (∫₀^π P θ sin θ)(∫₀^{2π} Q φ)`; the workhorse of the computation.
* `realSphericalAverage_blochComponent_mul` / `sphericalAverage_blochComponent_mul` — the **crux**
  `⟨nₐ n_b⟩ = (1/3) δₐb`, in real and complex form.

The nine component cases reduce to the elementary definite integrals
`∫₀^π sin³θ = 4/3`, `∫₀^π cos²θ sin θ = 2/3`, `∫₀^{2π} cos²φ = ∫₀^{2π} sin²φ = π`,
`∫₀^{2π} 1 = 2π`, and `∫₀^{2π} cos φ = ∫₀^{2π} sin φ = ∫₀^{2π} cos φ sin φ = 0`, collected below.
-/

namespace AxQM.Concrete

open intervalIntegral MeasureTheory

/-! ### Elementary definite integrals over `[0, π]` and `[0, 2π]` -/

/-- `∫₀^π sin θ cos²θ dθ = 2/3`, the endpoint values of Mathlib's `integral_sin_mul_cos_sq`. -/
theorem integral_sin_mul_cos_sq_pi :
    ∫ θ in (0:ℝ)..Real.pi, Real.sin θ * Real.cos θ ^ 2 = 2 / 3 := by
  rw [integral_sin_mul_cos_sq, Real.cos_zero, Real.cos_pi]; norm_num

/-- `∫₀^π sin³θ dθ = 4/3`, the endpoint values of Mathlib's `integral_sin_pow_three`. -/
theorem integral_sin_cube_pi : ∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ 3 = 4 / 3 := by
  rw [integral_sin_pow_three, Real.cos_zero, Real.cos_pi]; norm_num

/-- `∫₀^π sin²θ · sin θ dθ = 4/3` (the `sin³θ` integral in factored form). -/
theorem integral_sin_sq_mul_sin_pi :
    ∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ 2 * Real.sin θ = 4 / 3 := by
  simp_rw [show ∀ θ : ℝ, Real.sin θ ^ 2 * Real.sin θ = Real.sin θ ^ 3 from fun θ => by ring]
  exact integral_sin_cube_pi

/-- `∫₀^π cos²θ · sin θ dθ = 2/3` (the `sin θ cos²θ` integral in factored form). -/
theorem integral_cos_sq_mul_sin_pi :
    ∫ θ in (0:ℝ)..Real.pi, Real.cos θ ^ 2 * Real.sin θ = 2 / 3 := by
  simp_rw [show ∀ θ : ℝ, Real.cos θ ^ 2 * Real.sin θ = Real.sin θ * Real.cos θ ^ 2 from
    fun θ => by ring]
  exact integral_sin_mul_cos_sq_pi

/-- `∫₀^{2π} cos²φ dφ = π`. -/
theorem integral_cos_sq_two_pi : ∫ φ in (0:ℝ)..(2 * Real.pi), Real.cos φ ^ 2 = Real.pi := by
  rw [integral_cos_sq, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]; ring

/-- `∫₀^{2π} sin²φ dφ = π`. -/
theorem integral_sin_sq_two_pi : ∫ φ in (0:ℝ)..(2 * Real.pi), Real.sin φ ^ 2 = Real.pi := by
  rw [integral_sin_sq, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]; ring

/-- `∫₀^{2π} 1 dφ = 2π`. -/
theorem integral_one_two_pi : ∫ _φ in (0:ℝ)..(2 * Real.pi), (1 : ℝ) = 2 * Real.pi := by
  simp

/-- `∫₀^{2π} cos φ dφ = 0`. -/
theorem integral_cos_zero_two_pi : ∫ φ in (0:ℝ)..(2 * Real.pi), Real.cos φ = 0 := by
  rw [integral_cos, Real.sin_two_pi, Real.sin_zero]; ring

/-- `∫₀^{2π} sin φ dφ = 0`. -/
theorem integral_sin_zero_two_pi : ∫ φ in (0:ℝ)..(2 * Real.pi), Real.sin φ = 0 := by
  rw [integral_sin, Real.cos_two_pi, Real.cos_zero]; ring

/-- `∫₀^{2π} cos φ sin φ dφ = 0`, from Mathlib's `integral_sin_mul_cos₁` after `mul_comm`. -/
theorem integral_cos_mul_sin_two_pi :
    ∫ φ in (0:ℝ)..(2 * Real.pi), Real.cos φ * Real.sin φ = 0 := by
  simp_rw [mul_comm (Real.cos _) (Real.sin _)]
  rw [integral_sin_mul_cos₁, Real.sin_two_pi, Real.sin_zero]; norm_num

/-! ### The spherical average -/

/-- The **spherical average** of a complex-valued function of the unit direction `n̂`, computed in
spherical coordinates `n̂(θ,φ) = blochSphereVector θ φ` with solid-angle weight `sin θ` and total
solid angle `4π`: `(4π)⁻¹ ∫₀^π (∫₀^{2π} f(n̂(θ,φ)) dφ) sin θ dθ`. -/
noncomputable def sphericalAverage (f : (Fin 3 → ℝ) → ℂ) : ℂ :=
  (4 * Real.pi : ℂ)⁻¹ * ∫ θ in (0:ℝ)..Real.pi,
    (∫ φ in (0:ℝ)..(2 * Real.pi), f (blochSphereVector θ φ)) * (Real.sin θ : ℂ)

/-- The **real-valued spherical average**, the real analogue of `sphericalAverage`. -/
noncomputable def realSphericalAverage (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  (4 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..Real.pi,
    (∫ φ in (0:ℝ)..(2 * Real.pi), f (blochSphereVector θ φ)) * Real.sin θ

/-- The spherical average of a **real** integrand is the coercion of its real spherical average. -/
theorem sphericalAverage_ofReal (g : (Fin 3 → ℝ) → ℝ) :
    sphericalAverage (fun n => (g n : ℂ)) = (realSphericalAverage g : ℂ) := by
  rw [sphericalAverage, realSphericalAverage]
  simp_rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_mul,
    intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- **Separable reduction.** If the folded integrand factors as `n̂(θ,φ) ↦ P θ · Q φ`, its real
spherical average is `(4π)⁻¹ (∫₀^π P θ sin θ dθ)(∫₀^{2π} Q φ dφ)`. Purely formal: no integrability
hypotheses are needed, only `intervalIntegral.integral_const_mul`/`integral_mul_const`. -/
theorem realSphericalAverage_separable {f : (Fin 3 → ℝ) → ℝ} (P Q : ℝ → ℝ)
    (hsep : ∀ θ φ, f (blochSphereVector θ φ) = P θ * Q φ) :
    realSphericalAverage f =
      (4 * Real.pi)⁻¹ *
        ((∫ θ in (0:ℝ)..Real.pi, P θ * Real.sin θ) * ∫ φ in (0:ℝ)..(2 * Real.pi), Q φ) := by
  rw [realSphericalAverage]
  congr 1
  simp_rw [hsep, intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro θ _
  ring

/-! ### The crux: `⟨nₐ n_b⟩ = δₐb / 3` -/

/-- **Crux of Ex. 7.35, real form.** The spherical average of the product `nₐ n_b` of two Cartesian
components of the unit direction is `(1/3) δₐb`: `1/3` on the diagonal, `0` off it. The off-diagonal
cases vanish because one azimuthal integral (`∫ cos φ`, `∫ sin φ`, or `∫ cos φ sin φ`) is zero; the
diagonal cases give `(4π)⁻¹ · (4/3) · π = 1/3` (`x, y`) and `(4π)⁻¹ · (2/3) · 2π = 1/3` (`z`). -/
theorem realSphericalAverage_blochComponent_mul (a b : Fin 3) :
    realSphericalAverage (fun n => n a * n b) = 1 / 3 * (if a = b then 1 else 0) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  fin_cases a <;> fin_cases b
  · -- (0,0)
    rw [ite_eq_left rfl, realSphericalAverage_separable (fun θ => Real.sin θ ^ 2)
        (fun φ => Real.cos φ ^ 2) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_sin_sq_mul_sin_pi, integral_cos_sq_two_pi]
    field_simp
  · -- (0,1)
    rw [ite_eq_right (by decide), realSphericalAverage_separable (fun θ => Real.sin θ ^ 2)
        (fun φ => Real.cos φ * Real.sin φ) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_cos_mul_sin_two_pi]
    ring
  · -- (0,2)
    rw [ite_eq_right (by decide), realSphericalAverage_separable (fun θ => Real.sin θ * Real.cos θ)
        (fun φ => Real.cos φ) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_cos_zero_two_pi]
    ring
  · -- (1,0)
    rw [ite_eq_right (by decide), realSphericalAverage_separable (fun θ => Real.sin θ ^ 2)
        (fun φ => Real.cos φ * Real.sin φ) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_cos_mul_sin_two_pi]
    ring
  · -- (1,1)
    rw [ite_eq_left rfl, realSphericalAverage_separable (fun θ => Real.sin θ ^ 2)
        (fun φ => Real.sin φ ^ 2) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_sin_sq_mul_sin_pi, integral_sin_sq_two_pi]
    field_simp
  · -- (1,2)
    rw [ite_eq_right (by decide), realSphericalAverage_separable (fun θ => Real.sin θ * Real.cos θ)
        (fun φ => Real.sin φ) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_sin_zero_two_pi]
    ring
  · -- (2,0)
    rw [ite_eq_right (by decide), realSphericalAverage_separable (fun θ => Real.sin θ * Real.cos θ)
        (fun φ => Real.cos φ) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_cos_zero_two_pi]
    ring
  · -- (2,1)
    rw [ite_eq_right (by decide), realSphericalAverage_separable (fun θ => Real.sin θ * Real.cos θ)
        (fun φ => Real.sin φ) (fun θ φ => by simp [blochSphereVector]; ring),
        integral_sin_zero_two_pi]
    ring
  · -- (2,2)
    rw [ite_eq_left rfl, realSphericalAverage_separable (fun θ => Real.cos θ ^ 2) (fun _ => (1 : ℝ))
        (fun θ φ => by simp [blochSphereVector]; ring), integral_cos_sq_mul_sin_pi,
        integral_one_two_pi]
    field_simp; ring

/-- **Crux of Ex. 7.35, complex form.** `⟨nₐ n_b⟩ = (1/3) δₐb` for the complexified components, by
casting `realSphericalAverage_blochComponent_mul`. -/
theorem sphericalAverage_blochComponent_mul (a b : Fin 3) :
    sphericalAverage (fun n => (n a : ℂ) * (n b : ℂ)) = 1 / 3 * (if a = b then 1 else 0) := by
  simp_rw [← Complex.ofReal_mul]
  rw [sphericalAverage_ofReal, realSphericalAverage_blochComponent_mul]
  split <;> push_cast <;> ring

/-! ### `sphericalAverage` is ℂ-linear on continuous integrands

The reusable linearity API of `sphericalAverage`, culminating in the **bilinear second moment**
`⟨(∑ₐ pₐ nₐ)(∑_b q_b n_b)⟩ = ⅓ ∑ₐ pₐ qₐ` — the engine that lifts the diagonal moment
`sphericalAverage_blochComponent_mul` to averages of arbitrary quadratic forms in the components of
`n̂`. It is used for the dipolar coupling of Exercise 7.35. -/

/-- The spherical average is ℂ-homogeneous: `⟨c · f⟩ = c · ⟨f⟩`. No integrability hypothesis is
needed — only `intervalIntegral.integral_smul` (via `c * · = c • ·` on `ℂ`). -/
theorem sphericalAverage_smul (c : ℂ) (f : (Fin 3 → ℝ) → ℂ) :
    sphericalAverage (fun n => c * f n) = c * sphericalAverage f := by
  have hc : ∀ (g : ℝ → ℂ) (a b : ℝ), (∫ x in a..b, c * g x) = c * ∫ x in a..b, g x :=
    fun g a b => by simpa only [smul_eq_mul] using intervalIntegral.integral_smul c g
  simp only [sphericalAverage]
  simp_rw [hc, mul_assoc, hc]
  ring

/-- The spherical average of the constant function `1` is `1` (the average is normalised). -/
theorem sphericalAverage_one : sphericalAverage (fun _ => (1:ℂ)) = 1 := by
  have h1 : (fun _ : Fin 3 → ℝ => (1:ℂ)) = (fun n => (((fun _ => (1:ℝ)) n : ℝ) : ℂ)) := rfl
  rw [h1, sphericalAverage_ofReal,
      realSphericalAverage_separable (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) (fun _ _ => by norm_num)]
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rw [integral_sin, Real.cos_zero, Real.cos_pi]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast; field_simp; ring

/-- The spherical average of a constant is that constant. -/
theorem sphericalAverage_const (c : ℂ) : sphericalAverage (fun _ => c) = c := by
  have h := sphericalAverage_smul c (fun _ => (1:ℂ))
  simp only [mul_one] at h
  rw [h, sphericalAverage_one, mul_one]

/-- The outer `θ`-integrand of a spherical average is continuous when the integrand is:
`θ ↦ ∫₀^{2π} f (blochSphereVector θ φ) dφ` is continuous for continuous `f`. -/
theorem continuous_sphericalAverage_outer {f : (Fin 3 → ℝ) → ℂ} (hf : Continuous f) :
    Continuous (fun θ => ∫ φ in (0:ℝ)..(2*Real.pi), f (blochSphereVector θ φ)) := by
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2*Real.pi)
  exact hf.comp continuous_blochSphereVector

/-- The spherical average is additive on **continuous** integrands: `⟨f + g⟩ = ⟨f⟩ + ⟨g⟩`.
Continuity supplies the interval-integrability of the iterated integrand (inner via
`Continuous.intervalIntegrable`, outer via `continuous_sphericalAverage_outer`). -/
theorem sphericalAverage_add {f g : (Fin 3 → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g) :
    sphericalAverage (fun n => f n + g n) = sphericalAverage f + sphericalAverage g := by
  simp only [sphericalAverage]
  rw [← mul_add]; congr 1
  have hfi : ∀ θ : ℝ, IntervalIntegrable (fun φ => f (blochSphereVector θ φ)) volume 0
      (2*Real.pi) := fun θ => (hf.comp (continuous_blochSphereVector_snd θ)).intervalIntegrable _ _
  have hgi : ∀ θ : ℝ, IntervalIntegrable (fun φ => g (blochSphereVector θ φ)) volume 0
      (2*Real.pi) := fun θ => (hg.comp (continuous_blochSphereVector_snd θ)).intervalIntegrable _ _
  have huf := continuous_sphericalAverage_outer hf
  have hug := continuous_sphericalAverage_outer hg
  have hfo : IntervalIntegrable
      (fun θ => (∫ φ in (0:ℝ)..(2*Real.pi), f (blochSphereVector θ φ)) * (Real.sin θ:ℂ))
      volume 0 Real.pi :=
    (huf.mul (Complex.continuous_ofReal.comp Real.continuous_sin)).intervalIntegrable 0 Real.pi
  have hgo : IntervalIntegrable
      (fun θ => (∫ φ in (0:ℝ)..(2*Real.pi), g (blochSphereVector θ φ)) * (Real.sin θ:ℂ))
      volume 0 Real.pi :=
    (hug.mul (Complex.continuous_ofReal.comp Real.continuous_sin)).intervalIntegrable 0 Real.pi
  rw [← intervalIntegral.integral_add hfo hgo]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [intervalIntegral.integral_add (hfi θ) (hgi θ), add_mul]

/-- The spherical average negates under negation: `⟨-f⟩ = -⟨f⟩`. -/
theorem sphericalAverage_neg (f : (Fin 3 → ℝ) → ℂ) :
    sphericalAverage (fun n => -f n) = -sphericalAverage f := by
  simpa using sphericalAverage_smul (-1 : ℂ) f

/-- The spherical average is subtractive on continuous integrands: `⟨f − g⟩ = ⟨f⟩ − ⟨g⟩`. -/
theorem sphericalAverage_sub {f g : (Fin 3 → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g) :
    sphericalAverage (fun n => f n - g n) = sphericalAverage f - sphericalAverage g := by
  simp only [sub_eq_add_neg]
  rw [show (fun n => f n + -g n) = (fun n => f n + (-g) n) from rfl,
    sphericalAverage_add hf hg.neg,
    show sphericalAverage (-g) = -sphericalAverage g from sphericalAverage_neg g]

/-- The spherical average commutes with finite sums of continuous integrands. -/
theorem sphericalAverage_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → (Fin 3 → ℝ) → ℂ) (hF : ∀ i ∈ s, Continuous (F i)) :
    sphericalAverage (fun n => ∑ i ∈ s, F i n) = ∑ i ∈ s, sphericalAverage (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using sphericalAverage_const 0
  | @insert a s ha ih =>
    have hcont : Continuous (fun n => ∑ i ∈ s, F i n) :=
      continuous_finsetSum s (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert ha]
    rw [sphericalAverage_add (hF a (Finset.mem_insert_self a s)) hcont,
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

/-- **Bilinear second moment.** For complex coefficient vectors `p, q`, the spherical average of the
product of two linear forms in the components of `n̂` is `⅓ ∑ₐ pₐ qₐ`. This lifts the diagonal
identity `⟨nₐ n_b⟩ = δₐb/3` (`sphericalAverage_blochComponent_mul`) through ℂ-linearity. -/
theorem sphericalAverage_bilinear (p q : Fin 3 → ℂ) :
    sphericalAverage (fun n => (∑ a, p a * (n a : ℂ)) * (∑ b, q b * (n b : ℂ)))
      = (1 / 3) * ∑ a, p a * q a := by
  have hrw : (fun n : Fin 3 → ℝ => (∑ a, p a * (n a : ℂ)) * (∑ b, q b * (n b : ℂ)))
      = (fun n => ∑ a, ∑ b, (p a * q b) * ((n a : ℂ) * (n b : ℂ))) := by
    funext n
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  have inner : ∀ a : Fin 3,
      sphericalAverage (fun n => ∑ b, (p a * q b) * ((n a : ℂ) * (n b : ℂ)))
        = p a * q a * (1/3) := by
    intro a
    rw [sphericalAverage_finsetSum Finset.univ _ (fun b _ => by fun_prop)]
    simp_rw [sphericalAverage_smul, sphericalAverage_blochComponent_mul]
    simp
  rw [hrw, sphericalAverage_finsetSum Finset.univ _ (fun a _ => by fun_prop)]
  simp_rw [inner]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => by ring)

end AxQM.Concrete
