/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SphericalAverage
import AxQM.Concrete.PauliCommutator
import ToMathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: the dipolar coupling `H^D_{1,2}` and its vanishing spherical average

This file defines the **through-space dipolar coupling Hamiltonian** of two spin-½ nuclei,

`H^D_{1,2}(n̂) = (γ₁ γ₂ ℏ / 4r³) · [ σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂) ]`   (Nielsen & Chuang eq. 7.136),

as a `4 × 4` matrix depending on the internuclear unit direction `n̂`, and proves that its
**spherical average over `n̂` is the zero matrix** — the analytic content of Nielsen & Chuang,
Exercise 7.35 (*motional narrowing*, p. 328): in a low-viscosity liquid the direction `n̂` samples
the whole sphere and the dipolar interaction averages away.

Everything here is stated for matrices (`Matrix`, `Concrete.pauliDot`, the Pauli triple
`Concrete.pauliSigma`, and the reusable `Concrete.sphericalAverage`). It builds on the
analytic core `Concrete/SphericalAverage.lean` (Exercise 7.35); compare the dipole selection rules
`Concrete/DipoleSelectionRules.lean` (Exercise 7.16). These are the statements of N&C Exercise
7.35 (`AxQM/NC/Ch7/Exercise7_35.lean`).

## The averaging engine (reused, not re-proved)

The heart is the second-moment identity `⟨nₐ n_b⟩ = δₐb/3` (`sphericalAverage_blochComponent_mul`)
together with the ℂ-linearity API of `sphericalAverage` and the bilinear second moment
`sphericalAverage_bilinear` (`⟨(∑ₐ pₐ nₐ)(∑_b q_b n_b)⟩ = ⅓ ∑ₐ pₐ qₐ`) — all of which live next to
their definitions in `Concrete/SphericalAverage.lean` and are imported here.

## The two-qubit operators and the result

The two spins live on the register `ℂ² ⊗ ℂ² = ℂ⁴`, indexed `Fin 2 × Fin 2` (basis `|00⟩,…,|11⟩`).
With `σ^a` the Cartesian Pauli triple (`pauliSigma`) and `n·σ = ∑ₐ nₐ σ^a = pauliDot n`:

* `spinSpinCoupling = ∑ₐ σ^a ⊗ σ^a` is `σ⃗₁·σ⃗₂` (`σ⃗ᵢ` acting on qubit `i`), the isotropic term.
* `spinDirProduct n = (n·σ) ⊗ (n·σ)` is the anisotropic term `(σ⃗₁·n̂)(σ⃗₂·n̂)`: since
  `σ⃗₁·n̂ = (n·σ) ⊗ I` and `σ⃗₂·n̂ = I ⊗ (n·σ)`, the Kronecker mixed-product rule
  `((n·σ)⊗I)·(I⊗(n·σ)) = (n·σ)⊗(n·σ)` identifies the product with `(n·σ)⊗(n·σ)`
  (`spinDirProduct_eq_mul`).
* `dipolarBracket n = spinSpinCoupling − 3 · spinDirProduct n` is the bracket of (7.136), and
  `dipolarCoupling γ₁ γ₂ ℏ r n = (γ₁γ₂ℏ/4r³) · dipolarBracket n` is `H^D_{1,2}` itself.

Applied entrywise to `(n·σ)⊗(n·σ)`, `sphericalAverage_bilinear` gives `⟨spinDirProduct⟩ = ⅓ σ⃗₁·σ⃗₂`
(`sphericalAverage_spinDirProduct`), whence the bracket averages to `σ⃗₁·σ⃗₂ − 3·⅓ σ⃗₁·σ⃗₂ = 0` and

* `dipolarBracket_matrixSphericalAverage` — `⟨dipolarBracket⟩ = 0`;
* `dipolarCoupling_matrixSphericalAverage` — `⟨H^D_{1,2}⟩ = 0` for **all** `γ₁, γ₂, ℏ, r` (the
  scalar prefactor factors out of the zero average). This is Exercise 7.35.

`matrixSphericalAverage` is the entrywise spherical average of a matrix-valued function of `n̂`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker BigOperators

/-- The **isotropic coupling** `σ⃗₁·σ⃗₂ = ∑ₐ σ^a ⊗ σ^a`, the direction-independent term of `H^D`. -/
noncomputable def spinSpinCoupling : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ a, pauliSigma a ⊗ₖ pauliSigma a

/-- The **anisotropic coupling** `(σ⃗₁·n̂)(σ⃗₂·n̂) = (n·σ) ⊗ (n·σ)`, the direction-dependent term
of `H^D` (see `spinDirProduct_eq_mul` for the identification with the product of the two spins). -/
noncomputable def spinDirProduct (n : Fin 3 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  pauliDot n ⊗ₖ pauliDot n

/-- **Fidelity of the anisotropic term.** `spinDirProduct n` is literally the product of the two
single-spin projections `σ⃗₁·n̂ = (n·σ)⊗I` and `σ⃗₂·n̂ = I⊗(n·σ)`, by the Kronecker mixed-product
rule `((n·σ)⊗I)·(I⊗(n·σ)) = (n·σ)⊗(n·σ)`. -/
theorem spinDirProduct_eq_mul (n : Fin 3 → ℝ) :
    spinDirProduct n = (pauliDot n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliDot n) := by
  rw [spinDirProduct, ← Matrix.mul_kronecker_mul]; simp

/-- Each entry of the anisotropic coupling is continuous in `n` (a product of two linear forms). -/
theorem continuous_spinDirProduct_entry (i j : Fin 2 × Fin 2) :
    Continuous (fun n => spinDirProduct n i j) := by
  obtain ⟨i₁, i₂⟩ := i; obtain ⟨j₁, j₂⟩ := j
  simp_rw [spinDirProduct, Matrix.kronecker_apply]
  exact (continuous_pauliDot_entry i₁ j₁).mul (continuous_pauliDot_entry i₂ j₂)

/-- **Spherical average of the anisotropic term:** `⟨(σ⃗₁·n̂)(σ⃗₂·n̂)⟩ = ⅓ σ⃗₁·σ⃗₂`, entrywise.
Each entry `((n·σ)⊗(n·σ))ᵢⱼ = (n·σ)_{i₁j₁}(n·σ)_{i₂j₂}` is a product of two linear forms, so the
bilinear second moment gives `⅓ ∑ₐ (σ^a)_{i₁j₁}(σ^a)_{i₂j₂} = ⅓ (σ⃗₁·σ⃗₂)ᵢⱼ`. -/
theorem sphericalAverage_spinDirProduct (i j : Fin 2 × Fin 2) :
    sphericalAverage (fun n => spinDirProduct n i j) = (1/3) * spinSpinCoupling i j := by
  obtain ⟨i₁, i₂⟩ := i; obtain ⟨j₁, j₂⟩ := j
  have hrw : (fun n => spinDirProduct n (i₁, i₂) (j₁, j₂))
      = (fun n => (∑ a, pauliSigma a i₁ j₁ * (n a : ℂ))
          * (∑ b, pauliSigma b i₂ j₂ * (n b : ℂ))) := by
    funext n
    rw [spinDirProduct, Matrix.kronecker_apply, pauliDot_entry_eq_sum, pauliDot_entry_eq_sum]
  rw [hrw, sphericalAverage_bilinear]
  simp only [spinSpinCoupling, Matrix.sum_apply, Matrix.kronecker_apply]

/-- The **dipolar bracket** `σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂)`, the `n̂`-dependent operator inside
`H^D_{1,2}` (Nielsen & Chuang eq. 7.136). -/
noncomputable def dipolarBracket (n : Fin 3 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinSpinCoupling - (3 : ℂ) • spinDirProduct n

/-- The **through-space dipolar coupling Hamiltonian** `H^D_{1,2}(n̂)` of two spin-½ nuclei a
distance `r` apart along `n̂`, with gyromagnetic factors `γ₁, γ₂` and `ℏ` (Nielsen & Chuang
eq. 7.136): `(γ₁ γ₂ ℏ / 4r³) · [σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂)]`. -/
noncomputable def dipolarCoupling (γ₁ γ₂ ℏ r : ℝ) (n : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((γ₁ * γ₂ * ℏ / (4 * r ^ 3) : ℝ) : ℂ) • dipolarBracket n

/-- The **entrywise spherical average** of a matrix-valued function of the unit direction `n̂`. -/
noncomputable def matrixSphericalAverage {m p : Type*}
    (F : (Fin 3 → ℝ) → Matrix m p ℂ) : Matrix m p ℂ :=
  Matrix.of fun i j => sphericalAverage (fun n => F n i j)

/-- `matrixSphericalAverage` is ℂ-homogeneous: `⟨c · F⟩ = c · ⟨F⟩`. -/
theorem matrixSphericalAverage_smul {m p : Type*} (c : ℂ)
    (F : (Fin 3 → ℝ) → Matrix m p ℂ) :
    matrixSphericalAverage (fun n => c • F n) = c • matrixSphericalAverage F := by
  ext i j
  simp only [matrixSphericalAverage, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact sphericalAverage_smul c _

/-- **The dipolar bracket averages to zero:** `⟨σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂)⟩ = 0`. Since
`⟨(σ⃗₁·n̂)(σ⃗₂·n̂)⟩ = ⅓ σ⃗₁·σ⃗₂`, the isotropic and averaged anisotropic terms cancel. -/
theorem dipolarBracket_matrixSphericalAverage :
    matrixSphericalAverage dipolarBracket = 0 := by
  ext i j
  simp only [matrixSphericalAverage, Matrix.of_apply, Matrix.zero_apply]
  have hb : (fun n => dipolarBracket n i j)
      = (fun n => spinSpinCoupling i j - (3:ℂ) * spinDirProduct n i j) := by
    funext n
    simp only [dipolarBracket, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hf : Continuous (fun _ : Fin 3 → ℝ => spinSpinCoupling i j) := continuous_const
  have hg : Continuous (fun n => (3:ℂ) * spinDirProduct n i j) :=
    continuous_const.mul (continuous_spinDirProduct_entry i j)
  rw [hb, sphericalAverage_sub hf hg, sphericalAverage_const, sphericalAverage_smul,
      sphericalAverage_spinDirProduct]
  ring

/-- **Nielsen & Chuang, Exercise 7.35 (motional narrowing).** The spherical average of the dipolar
coupling Hamiltonian `H^D_{1,2}` over the internuclear direction `n̂` is the **zero** matrix, for
every choice of the physical constants `γ₁, γ₂, ℏ, r`: the scalar prefactor factors out of the
already-vanishing average of the bracket. -/
theorem dipolarCoupling_matrixSphericalAverage (γ₁ γ₂ ℏ r : ℝ) :
    matrixSphericalAverage (dipolarCoupling γ₁ γ₂ ℏ r) = 0 := by
  unfold dipolarCoupling
  rw [matrixSphericalAverage_smul, dipolarBracket_matrixSphericalAverage, smul_zero]

end AxQM.Concrete
