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
# Concrete: Rabi oscillations — exponentiating the single-excitation Jaynes–Cummings Hamiltonian
(Nielsen & Chuang, Exercise 7.18)

Every statement is about matrices (`Matrix`, `NormedSpace.exp`, `Real.cos`/`Real.sin`,
`Complex.exp`). It exponentiates its Hamiltonian through the same Mathlib
Euler-for-involutions lemma `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` used by the sibling
matrix-exponential file `Concrete/PauliExponential.lean` (N&C Ex. 2.35), and imports that lemma's
source (`ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution`) directly.

## The exercise

N&C §7.5.3 restricts the Jaynes–Cummings Hamiltonian (7.71) to the single-excitation sector
`span{|00⟩, |01⟩, |10⟩}` (field⊗atom), where in this ordered basis it is the `3×3` matrix (7.76)

`H = -!![δ, 0, 0; 0, δ, g; 0, g, -δ]`,

with `δ` the detuning and `g` the coupling. Exercise 7.18 asks to obtain the time-evolution
operator `U = exp(-i H t)` — the *Rabi-oscillation* form (7.77) — by using the Pauli-exponential
identity (7.78) `exp(i n·σ) = cos|n| · I + i sin|n| · n̂·σ` (the corrected form of the printed
(7.78); it is N&C's own eq. (4.8), the same identity N&C Ex. 2.35 formalises as
`AxQM.Concrete.pauliDot_exp_of_unit` — both discharge it via the shared Mathlib lemma
`NormedSpace.exp_smul_mul_I_of_mul_self_eq_one`), rather than by solving coupled ODEs. The Rabi
frequency is `Ω = √(g² + δ²)`.

## What is proved

`exp_neg_I_smul_rabiHamiltonian`:
`exp((-i t) • rabiHamiltonian δ g) = rabiUnitary δ g t`  (for `Ω ≠ 0`),
where `rabiUnitary` is the explicit unitary

`U = e^{iδt} |00⟩⟨00|`
`  + (cos Ωt + i (δ/Ω) sin Ωt) |01⟩⟨01| + (cos Ωt - i (δ/Ω) sin Ωt) |10⟩⟨10|`
`  + i (g/Ω) sin Ωt (|01⟩⟨10| + |10⟩⟨01|)`.

This is the physically essential content of (7.77): Rabi oscillations at frequency
`Ω = √(g²+δ²)`, coherently exchanging a quantum of energy between `|01⟩` and `|10⟩`, with the
Lorentzian absorption profile `(g²/Ω²) sin²Ωt` read off the off-diagonal. The `|00⟩` entry of
`rabiUnitary` is written in the factored form `e^{it(δ-Ω)}·(cos Ωt + i sin Ωt)` the exponentiation
produces; `rabiUnitary_apply_zero_zero` proves it equals N&C's `e^{iδt}`.

## Fidelity note — two typos in the printed (7.77)/(7.78)

Computing `exp(-iHt)` for `H` *exactly as printed in (7.76)* (verified independently by symbolic
matrix exponentiation) gives the `|00⟩` phase `e^{+iδt}` and off-diagonal coupling
`+i(g/Ω) sin Ωt`, whereas N&C's printed (7.77) shows `e^{-iδt}` and `-i(g/Ω) sin Ωt`. These two
signs cannot *both* be produced by any single sign choice of `H` or `t` (fixing them flips the
`|01⟩,|10⟩` diagonal, which N&C prints correctly), so (7.77) as printed is internally inconsistent
— a known erratum. We therefore prove the *true* exponential (the corrected (7.77)); the diagonal
Rabi terms, the frequency `Ω`, and all physical content are exactly as N&C states. Likewise the
printed (7.78) swaps `cos`/`sin` and drops the `I` term; the identity actually used is the correct
one, N&C's (4.8).

## Method (sigma-free block exponentiation)

`H` is block-diagonal: the `|00⟩` mode is a `1×1` block `(-δ)`, and `span{|01⟩,|10⟩}` carries the
`2×2` block `-(δZ + gX) = -Ω (n̂·σ)` with `n̂ = (g, 0, δ)/Ω` a unit vector. Rather than fight
`Matrix.exp_blockDiagonal'` on a dependent `Σ`-index (whose operator-norm `CompleteSpace`
instance does not compose with `map_exp`), we split the exponent into two *commuting* pieces on
`Fin 3`:

`(-i t) • H = (i t (δ - Ω)) • P₀  +  ((Ω t) i) • Ĵ`,

where `P₀ = diagonal ![1,0,0]` is the `|00⟩` projector and `Ĵ = P₀ + n̂·σ`(padded) is a genuine
**involution** (`Ĵ² = I`, using `n̂` unit). Then `Matrix.exp_add_of_commute` factors the
exponential; the `P₀` term exponentiates by `Matrix.exp_diagonal`, and the involution term by the
same Euler lemma `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` that underlies `pauliDot`
(this *is* the identity (7.78)). Multiplying the two factors gives `rabiUnitary` entrywise (each
entry a ring identity), and `rabiUnitary_apply_zero_zero` performs the `|00⟩` collapse
`e^{it(δ-Ω)}·e^{iΩt} = e^{iδt}`.
-/

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

namespace AxQM.Concrete

/-- The **Rabi frequency** `Ω = √(g² + δ²)` (Nielsen & Chuang §7.5.3, below eq. 7.77):
the angular frequency at which the atom and field exchange a quantum of energy. -/
noncomputable def rabiFrequency (δ g : ℝ) : ℝ := Real.sqrt (g ^ 2 + δ ^ 2)

/-- The **single-excitation Jaynes–Cummings Hamiltonian** (Nielsen & Chuang eq. 7.76), the
restriction of (7.71) to `span{|00⟩, |01⟩, |10⟩}` (basis ordered `|field, atom⟩`, `N` neglected):
`H = -!![δ,0,0; 0,δ,g; 0,g,-δ]`, with detuning `δ` and coupling `g`. -/
noncomputable def rabiHamiltonian (δ g : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(δ : ℂ), 0, 0; 0, -(δ : ℂ), -(g : ℂ); 0, -(g : ℂ), (δ : ℂ)]

/-- `H` is Hermitian (a real symmetric matrix): observables are self-adjoint. -/
theorem rabiHamiltonian_isHermitian (δ g : ℝ) : (rabiHamiltonian δ g).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rabiHamiltonian, Matrix.conjTranspose_apply]

/-- The **real** form of the involution `Ĵ = |00⟩⟨00| + n̂·σ`, `!![1,0,0; 0, δ/Ω, g/Ω;
0, g/Ω, -δ/Ω]` over `ℝ` (`Ω = √(g²+δ²)`). Working over `ℝ` keeps the involution algebra a clean
real computation; the complex `rabiInvolution` is its entrywise `ℝ → ℂ` image. -/
noncomputable def rabiInvolutionReal (δ g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, δ / rabiFrequency δ g, g / rabiFrequency δ g;
     0, g / rabiFrequency δ g, -(δ / rabiFrequency δ g)]

/-- The **involution** `Ĵ = |00⟩⟨00| + n̂·σ` (padded into the `3×3` block form) used to
exponentiate `H`: `Ĵ = !![1,0,0; 0, δ/Ω, g/Ω; 0, g/Ω, -δ/Ω]` with `Ω = √(g²+δ²)`. On
`span{|01⟩,|10⟩}` it is the unit Pauli combination `n̂·σ` (which squares to `I`), and it fixes
`|00⟩`, so `Ĵ² = I` (`rabiInvolution_mul_self`). -/
noncomputable def rabiInvolution (δ g : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, ((δ / rabiFrequency δ g : ℝ) : ℂ), ((g / rabiFrequency δ g : ℝ) : ℂ);
     0, ((g / rabiFrequency δ g : ℝ) : ℂ), -((δ / rabiFrequency δ g : ℝ) : ℂ)]

/-- `Ĵ² = I` over `ℝ`: the diagonal block entries reduce to `(δ/Ω)² + (g/Ω)² = 1` for the unit
vector `n̂ = (g,0,δ)/Ω`, and the off-diagonal cross terms cancel. -/
theorem rabiInvolutionReal_mul_self (δ g : ℝ) (hΩ : rabiFrequency δ g ≠ 0) :
    rabiInvolutionReal δ g * rabiInvolutionReal δ g = 1 := by
  have hΩsq : rabiFrequency δ g * rabiFrequency δ g = g ^ 2 + δ ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rabiInvolutionReal, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;>
    nlinarith [hΩsq]

/-- `Ĵ² = I`: the padded unit Pauli combination is an involution (`|00⟩` entry `1² = 1`; the
`span{|01⟩,|10⟩}` block is `(n̂·σ)² = I`). Proved by transporting the real identity
`rabiInvolutionReal_mul_self` along the ring homomorphism `Complex.ofReal : ℝ →+* ℂ`, which
sidesteps the complex-instance bookkeeping of an entrywise complex computation. -/
theorem rabiInvolution_mul_self (δ g : ℝ) (hΩ : rabiFrequency δ g ≠ 0) :
    rabiInvolution δ g * rabiInvolution δ g = 1 := by
  have hmap : rabiInvolution δ g = (rabiInvolutionReal δ g).map (⇑Complex.ofRealHom) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rabiInvolution, rabiInvolutionReal, Matrix.map_apply]
  rw [hmap, ← Matrix.map_mul, rabiInvolutionReal_mul_self δ g hΩ,
    Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)]

/-- The **Rabi-oscillation unitary** `U = exp(-iHt)` (the corrected Nielsen & Chuang eq. 7.77):
`U = e^{iδt} |00⟩⟨00| + (cos Ωt + i(δ/Ω) sin Ωt) |01⟩⟨01| + (cos Ωt - i(δ/Ω) sin Ωt) |10⟩⟨10|
     + i(g/Ω) sin Ωt (|01⟩⟨10| + |10⟩⟨01|)`,
with `Ω = √(g²+δ²)` the Rabi frequency. (See the file header on the two printed sign typos.)

The `|00⟩⟨00|` entry is written in the factored form `e^{it(δ-Ω)}·(cos Ωt + i sin Ωt)` in which the
exponentiation naturally produces it (the `|00⟩` phase `e^{it(δ-Ω)}` from the diagonal block times
the `|00⟩` Rabi phase `e^{iΩt}` from the involution block); `rabiUnitary_apply_zero_zero` proves it
equals `e^{iδt}` exactly as N&C states. -/
noncomputable def rabiUnitary (δ g t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.exp (Complex.I * (t : ℂ) * ((δ : ℂ) - ((rabiFrequency δ g : ℝ) : ℂ)))
       * ((Real.cos (rabiFrequency δ g * t) : ℂ)
           + (Real.sin (rabiFrequency δ g * t) : ℂ) * Complex.I), 0, 0;
     0,
       (Real.cos (rabiFrequency δ g * t) : ℂ)
         + Complex.I * ((δ / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ),
       Complex.I * ((g / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ);
     0,
       Complex.I * ((g / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ),
       (Real.cos (rabiFrequency δ g * t) : ℂ)
         - Complex.I * ((δ / rabiFrequency δ g : ℝ) : ℂ) * (Real.sin (rabiFrequency δ g * t) : ℂ)]

/-- **Nielsen & Chuang, Exercise 7.18 (Rabi oscillations).** The time-evolution operator
`exp(-iHt)` of the single-excitation Jaynes–Cummings Hamiltonian (7.76) is the Rabi-oscillation
unitary (7.77):
`exp((-i t) • rabiHamiltonian δ g) = rabiUnitary δ g t`,
for nonzero Rabi frequency `Ω = √(g²+δ²) ≠ 0` (needed for the `n̂·σ` normalisation, and the
division by `Ω` in (7.77) itself). -/
theorem exp_neg_I_smul_rabiHamiltonian (δ g t : ℝ) (hΩ : rabiFrequency δ g ≠ 0) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • rabiHamiltonian δ g) = rabiUnitary δ g t := by
  have hΩne : ((rabiFrequency δ g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΩ
  -- decompose `-i t H` into a `|00⟩` diagonal block plus the involution block; the two commute
  have hdecomp : (-Complex.I * (t : ℂ)) • rabiHamiltonian δ g
      = Matrix.diagonal
          ![Complex.I * (t : ℂ) * ((δ : ℂ) - ((rabiFrequency δ g : ℝ) : ℂ)), 0, 0]
        + (((rabiFrequency δ g * t : ℝ) : ℂ) * Complex.I) • rabiInvolution δ g := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rabiHamiltonian, rabiInvolution, Matrix.add_apply, Matrix.smul_apply] <;>
      field_simp
    ring
  have hcomm : Commute
      (Matrix.diagonal
        ![Complex.I * (t : ℂ) * ((δ : ℂ) - ((rabiFrequency δ g : ℝ) : ℂ)), 0, 0])
      ((((rabiFrequency δ g * t : ℝ) : ℂ) * Complex.I) • rabiInvolution δ g) := by
    unfold Commute SemiconjBy
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rabiInvolution, Matrix.diagonal_apply, Matrix.mul_apply]
    ring
  -- exp of the `|00⟩` diagonal block (entrywise, `exp 0 = 1`)
  have hExpDiag : NormedSpace.exp
      (Matrix.diagonal
        ![Complex.I * (t : ℂ) * ((δ : ℂ) - ((rabiFrequency δ g : ℝ) : ℂ)), 0, 0])
      = Matrix.diagonal
          ![Complex.exp (Complex.I * (t : ℂ) * ((δ : ℂ) - ((rabiFrequency δ g : ℝ) : ℂ))),
            1, 1] := by
    rw [Matrix.exp_diagonal]; congr 1; funext i
    fin_cases i <;>
      simp [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  -- exp of the involution block (the Euler identity 7.78 / N&C 4.8)
  have hExpInv : NormedSpace.exp
      ((((rabiFrequency δ g * t : ℝ) : ℂ) * Complex.I) • rabiInvolution δ g)
      = (Real.cos (rabiFrequency δ g * t) : ℂ) • 1
        + ((Real.sin (rabiFrequency δ g * t) : ℂ) * Complex.I) • rabiInvolution δ g :=
    exp_smul_mul_I_of_mul_self_eq_one (rabiInvolution_mul_self δ g hΩ) _
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm, hExpDiag, hExpInv, mul_add, mul_smul_comm,
    mul_smul_comm, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    -- reduce the matrix product entrywise; with the `|00⟩` entry of `rabiUnitary` written in the
    -- same factored `e^{it(δ-Ω)}·(cos Ωt + i sin Ωt)` form the exponentiation produces, every entry
    -- (block, off-diagonal, and `|00⟩`) is a ring identity
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    simp [rabiUnitary, rabiInvolution, -mul_eq_zero, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    ring

/-- The `|00⟩` phase collapses to N&C's `e^{iδt}`: the factored `|00⟩` entry
`e^{it(δ-Ω)}·(cos Ωt + i sin Ωt)` of `rabiUnitary` equals `e^{iδt}`, since
`cos Ωt + i sin Ωt = e^{iΩt}` (Euler) and `e^{it(δ-Ω)}·e^{iΩt} = e^{iδt}`. This is the "fixed
phase" of the `|00⟩` mode that N&C notes may be neglected. -/
theorem rabiUnitary_apply_zero_zero (δ g t : ℝ) :
    rabiUnitary δ g t 0 0 = Complex.exp (Complex.I * ((δ * t : ℝ) : ℂ)) := by
  simp only [rabiUnitary, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have heuler : ((Real.cos (rabiFrequency δ g * t) : ℂ)
        + (Real.sin (rabiFrequency δ g * t) : ℂ) * Complex.I)
      = Complex.exp (((rabiFrequency δ g * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [heuler, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end AxQM.Concrete
