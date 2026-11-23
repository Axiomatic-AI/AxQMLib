/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DipolarCoupling

/-!
# Nielsen & Chuang, Exercise 7.35 (Motional narrowing)

Motional narrowing: show the spherical average of the dipolar coupling H^D_{1,2} over n̂ is zero.

(N&C §7.7.2, p. 328.) The through-space **dipolar coupling** of two spin-½ nuclei a distance `r`
apart along the unit direction `n̂` is (eq. 7.136)

`H^D_{1,2}(n̂) = (γ₁ γ₂ ℏ / 4r³) · [ σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂) ]`,

with `σ⃗ᵢ` the (twice-magnetic-moment) spin vector of nucleus `i`. In a low-viscosity liquid the
internuclear direction `n̂` tumbles rapidly through all orientations, and the interaction averages
away: the exercise asks to show that the spherical average of `H^D_{1,2}` over `n̂` is **zero**. The
physical mechanism is the second-moment identity `⟨nₐ n_b⟩ = δₐb/3`, which makes the average of the
anisotropic term `(σ⃗₁·n̂)(σ⃗₂·n̂)` equal to `⅓ σ⃗₁·σ⃗₂`, exactly cancelling the isotropic term.

The content is a statement about the entrywise spherical average of a `4 × 4`
complex-matrix-valued function of `n̂ ∈ ℝ³` (`Matrix`, the Pauli matrices, `sphericalAverage`).
Compare the dipole exercise `AxQM/NC/Ch7/Exercise7_16.lean`.

## The formalisation

The exercise is formalised in the files below (namespace `AxQM.Concrete`).

### The analytic core — `AxQM/Concrete/SphericalAverage.lean`

* `sphericalAverage` / `realSphericalAverage` — the spherical average of a (complex- / real-valued)
  function of the unit direction `n̂`, the iterated integral `(4π)⁻¹ ∫₀^π (∫₀^{2π} · dφ) sin θ dθ`.
* `sphericalAverage_blochComponent_mul` — the **second moment** `⟨nₐ n_b⟩ = (1/3) δₐb`.
* `sphericalAverage_const` / `_smul` / `_neg` / `_add` / `_sub` / `_finsetSum` — the spherical
  average is **ℂ-linear** on continuous integrands, and `sphericalAverage_bilinear` lifts the second
  moment to `⟨(∑ₐ pₐ nₐ)(∑_b q_b n_b)⟩ = ⅓ ∑ₐ pₐ qₐ`.

### The dipolar operator — `AxQM/Concrete/DipolarCoupling.lean`

* `spinSpinCoupling` (`σ⃗₁·σ⃗₂ = ∑ₐ σ^a⊗σ^a`), `spinDirProduct` (`(σ⃗₁·n̂)(σ⃗₂·n̂) = (n·σ)⊗(n·σ)`,
  with `spinDirProduct_eq_mul` identifying it as the product of the two single-spin projections),
  `dipolarBracket` (the bracket of 7.136), and `dipolarCoupling γ₁ γ₂ ℏ r` (`H^D_{1,2}` itself).
* `sphericalAverage_spinDirProduct` — `⟨(σ⃗₁·n̂)(σ⃗₂·n̂)⟩ = ⅓ σ⃗₁·σ⃗₂` (entrywise).
* `matrixSphericalAverage` — the entrywise spherical average of a matrix-valued function of `n̂`.
* `dipolarBracket_matrixSphericalAverage` — the bracket averages to `0`.
* `dipolarCoupling_matrixSphericalAverage` — **Exercise 7.35 itself:** `⟨H^D_{1,2}⟩ = 0` over `n̂`,
  for every choice of the physical constants `γ₁, γ₂, ℏ, r`.
-/
