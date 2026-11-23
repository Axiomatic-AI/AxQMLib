/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HarmonicOscillatorAmplitudeDamping
import AxQM.Concrete.PauliExponential
import ToMathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import ToMathlib.Algebra.BigOperators.Fin

/-!
# Concrete: the beam-splitter propagator of a harmonic oscillator (N&C, Exercise 8.21, part 1)

This file begins the **derivation** of the
amplitude-damping operation elements of a harmonic oscillator (Nielsen & Chuang, Exercise 8.21,
p. 381) from the interaction Hamiltonian `H = χ(a†b + b†a)` and the propagator `U = exp(-iHΔt)` —
part **(1)** of the exercise — rather than *positing* eq. 8.110 as a definition. The trace-
preservation half — part **(2)**, `Σₖ Eₖ† Eₖ = I` — is developed in
`AxQM/Concrete/HarmonicOscillatorAmplitudeDamping.lean`; the statement of the exercise is in
`AxQM/NC/Ch8/Exercise8_21.lean`.

## The physics, and why the derivation is finite-dimensional

`H = χ(a†b + b†a)` **conserves the total number of quanta** `N = a†a + b†b`: it moves one quantum
between the principal mode `a` and the environment mode `b`, so it is block diagonal over the
excitation-number sectors, and the propagator `U = exp(-iHΔt)` is the direct sum of its restrictions
`Uⁿ` to the `(n+1)`-dimensional sectors `Nⁿ = span{|n-j⟩ₐ|j⟩_b : j = 0,…,n}`. Because the initial
state `|n⟩ₐ|0_b⟩` sits in the `N = n` sector and the operation element `Eₖ = ⟨k_b|U|0_b⟩` reads off
its overlap with `|k_b⟩`, the entire content of eq. 8.110 is captured **sector by sector**, in the
genuinely *finite*-dimensional matrix exponential `Uⁿ = exp(-iΔt·χMₙ)` — no unbounded-operator /
Stone's-theorem apparatus is needed.

In the number basis `|n-j⟩ₐ|j⟩_b` (index `j` = number of quanta in the environment) the Hamiltonian
`a†b + b†a` is the honest tridiagonal (Jacobi) matrix `Mₙ` (`fockBeamGen`) with off-diagonal entries
`⟨j±1| Mₙ |j⟩ = √((j+1)(n-j))` — the exact creation/annihilation matrix elements `√(n-j) √(j+1)` of
`b†a` (and its transpose `a†b`). Writing `θ = χΔt`, the sector propagator is
`Uⁿ(θ) = exp(-iθMₙ)` (`fockBeamProp`), a unitary (`fockBeamProp_mem_unitaryGroup`). Its first column
(the evolution of `|n⟩ₐ|0_b⟩`, `j = 0`) is the claimed amplitude vector
`⟨j| Uⁿ(θ) |0⟩ = √(C(n,j)) cosⁿ⁻ʲθ (-i sinθ)ʲ` (`fockBeamAmp`), whose modulus is precisely the real
amplitude `√(C(n,j)(1-γ)ⁿ⁻ʲγʲ)` of eq. 8.110 with `γ = 1 - cos²θ = sin²θ` (`fockBeamAmp_norm`).

## What this file establishes

* `fockBeamGen n`, `fockBeamGen_isHermitian` — the honest number-basis matrix `Mₙ` of `a†b + b†a`
  on the `n`-quantum sector, and its Hermiticity (`Mₙ` is real symmetric).
* `fockBeamProp n θ`, `fockBeamProp_mem_unitaryGroup` — the sector propagator `exp(-iθMₙ)` and its
  unitarity (`exp` of the skew-Hermitian `-iθMₙ`).
* `fockBeamAmp θ n k`, `fockBeamAmp_norm` — the complex sector amplitude
  `√(C(n,k)) cosⁿ⁻ᵏθ (-i sinθ)ᵏ` of eq. 8.110, and the bridge `‖·‖ = fockDampingAmp (sin²θ) n k` to
  the real amplitude used for the trace-preservation half.
* `fockBeamGen_zero`, `fockBeamProp_zero` — the vacuum sector `N = 0`: `M₀ = 0`, `U⁰ = I`
  (nothing to couple; the vacuum is invariant).
* `fockBeamGen_one`, `fockBeamProp_one`, `fockBeamProp_one_col` — the **single-excitation sector**
  `N = 1`, worked out fully: `M₁ = X` (Pauli-X), so `U¹(θ) = exp(-iθX) = cosθ·I - i sinθ·X` (via the
  Exercise 2.35 Euler formula `pauliDot_exp_of_unit`), and its first column
  `⟨j| U¹(θ) |0⟩ = fockBeamAmp θ 1 j` — **eq. 8.110 for `n = 1`, derived from `exp(-iHΔt)`**
  (`E₀|1⟩ = cosθ|1⟩`, `E₁|1⟩ = -i sinθ|0⟩`, the amplitudes `√(1-γ)`, `√γ` up to the operation
  element phase `-i`).
* `sqrt_choose_succ_mul`, `sqrt_choose_pred_mul` — the two `√`-form binomial recurrences
  (`√(C(n,k))·(n-k) = √((k+1)(n-k))·√(C(n,k+1))` and `√(C(n,k))·k = √(k(n-(k-1)))·√(C(n,k-1))`) that
  drive the dynamics; the `√`-forms of Pascal's rule `C(n,k+1)(k+1) = C(n,k)(n-k)`.
* `fockBeamAmpVec θ n`, `fockBeamAmp_hasDerivAt`, `fockBeamGen_mulVec_amp`,
  `fockBeamAmpVec_hasDerivAt` — the **sector Schrödinger equation** for the amplitude vector
  `c(θ)_j = fockBeamAmp θ n j`, `d/dθ c(θ) = -i Mₙ c(θ)`. `fockBeamAmp_hasDerivAt` is the
  component derivative in vector-field form; `fockBeamGen_mulVec_amp` evaluates the tridiagonal
  `Mₙ c(θ)` to its two neighbour terms; `fockBeamAmpVec_hasDerivAt` assembles them into the vector
  ODE. This is the dynamical heart of the general-`n` derivation.
* `fockBeamProp_eq_exp`, `fockBeamProp_apply_zero`, `fockBeamAmpVec_zero`,
  `fockBeamProp_col_hasDerivAt`, `fockBeamProp_col` — the **general-`n` first column, eq. 8.110 for
  all `n`**. `fockBeamProp_eq_exp` rewrites `Uⁿ(θ) = exp(θ B)` (`B = -i Mₙ`);
  `fockBeamProp_col_hasDerivAt` shows `Uⁿ(θ) e₀` solves the sector Schrödinger IVP (the
  matrix-exponential derivative `d/dθ exp(θ B) = B exp(θ B)` composed with `M ↦ M e₀`); with the
  initial conditions `fockBeamProp_apply_zero`/`fockBeamAmpVec_zero`, ODE uniqueness
  (`ODE_solution_unique_univ`) gives `fockBeamProp_col : ⟨j| Uⁿ(θ) |0⟩ = fockBeamAmp θ n j`.

This completes the sector-by-sector derivation of eq. 8.110 from `U = exp(-iHΔt)`: for every `n`,
the operation element `Eₖ = ⟨k_b|U|0_b⟩` restricted to the `n`-quantum sector is `fockBeamProp_col`,
whose modulus is the eq.-8.110 amplitude `√(C(n,k)(1-γ)ⁿ⁻ᵏγᵏ)` (`fockBeamAmp_norm`, `γ = sin²θ`).

* `fockBeamKraus θ k`, `fockBeamKraus_apply`, `fockBeamKraus_eq_prop_col`, `fockBeamKraus_norm`,
  `fockBeamGram_eq`, `fockBeamKraus_completeness` — the **assembly** of these sector first columns
  into the single `ℕ`-indexed operation element `Eₖ = ⟨k_b|U|0_b⟩` (`Matrix ℕ ℕ ℂ`), and its
  **reconciliation** with part (2). `fockBeamKraus θ k` lowers `|n⟩` to `|n-k⟩` with amplitude
  `fockBeamAmp θ n k`, which `fockBeamKraus_eq_prop_col` certifies is the sector first-column
  reading `fockBeamProp n θ ⟨k⟩ 0`. Its entrywise modulus is part (2)'s `fockDampingKraus (sin²θ)`
  (`fockBeamKraus_norm`, the phase `(-i)ᵏ` dropping out), and the derived `Eₖ` are themselves trace
  preserving — `Σₖ Eₖ† Eₖ = I` (`fockBeamKraus_completeness`), the phase cancelling in `Eₖ† Eₖ`.

This closes Exercise 8.21: part (1) derives eq. 8.110 from `U = exp(-iHΔt)` for all `n` and
assembles the `ℕ`-indexed `Eₖ`; part (2) (this file's import `HarmonicOscillatorAmplitudeDamping`)
proves trace preservation, now established directly for the derived `Eₖ` as well.
-/

namespace AxQM.Concrete

open scoped Matrix Matrix.Norms.Operator
open Matrix

/-! ### The sector Hamiltonian `Mₙ = a†b + b†a` in the number basis (eq. 8.109) -/

/-- The **number-basis matrix of `a†b + b†a`** on the total-excitation sector `N = n`
(Nielsen & Chuang eq. 8.109, `H = χ(a†b + b†a)`), as an `(n+1) × (n+1)` complex matrix. The index
`j : Fin (n+1)` counts the quanta in the environment mode `b` (so the principal mode `a` holds
`n - j`); the tridiagonal off-diagonal entry `⟨j+1| Mₙ |j⟩ = √((j+1)(n-j))` is the exact
annihilation/creation matrix element `√(n-j)·√(j+1)` of `b†a` (its symmetric partner `⟨j| Mₙ |j+1⟩`
being that of `a†b`). The full Hamiltonian is `H = χ·Mₙ`. -/
noncomputable def fockBeamGen (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun r c =>
    if (r : ℕ) + 1 = (c : ℕ) then (Real.sqrt (((r : ℕ) + 1) * (n - (r : ℕ))) : ℂ)
    else if (c : ℕ) + 1 = (r : ℕ) then (Real.sqrt (((c : ℕ) + 1) * (n - (c : ℕ))) : ℂ)
    else 0

/-- `Mₙ` is Hermitian: it is real (entries are real square roots) and symmetric (the `j ↔ j+1`
off-diagonal entries coincide), reflecting that `a†b + b†a` is self-adjoint. -/
theorem fockBeamGen_isHermitian (n : ℕ) : (fockBeamGen n).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, fockBeamGen, fockBeamGen]
  by_cases h1 : (j : ℕ) + 1 = (i : ℕ)
  · rw [ite_eq_left h1, ite_eq_right (by omega),
        ite_eq_left (by omega)]; exact Complex.conj_ofReal _
  · by_cases h2 : (i : ℕ) + 1 = (j : ℕ)
    · rw [ite_eq_right (by omega), ite_eq_left (by omega),
          ite_eq_left h2]; exact Complex.conj_ofReal _
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2,
          star_zero]

/-! ### The sector propagator `Uⁿ(θ) = exp(-iθMₙ)` (`θ = χΔt`) -/

/-- The **sector propagator** `Uⁿ(θ) = exp(-iθMₙ)` — the restriction of `U = exp(-iHΔt)` to the
`n`-quantum sector, with `θ = χΔt` (`H = χMₙ`, so `-iHΔt = -iθMₙ`). This is a genuine finite matrix
exponential; the `k`-th operation element `Eₖ = ⟨k_b|U|0_b⟩` of eq. 8.110 reads its first column
off, sector by sector. -/
noncomputable def fockBeamProp (n : ℕ) (θ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  NormedSpace.exp ((-Complex.I * (θ : ℂ)) • fockBeamGen n)

/-- The generator `-iθMₙ` of the propagator is skew-Hermitian (`Mₙ` Hermitian, `θ` real). -/
theorem fockBeamGenArg_skew (n : ℕ) (θ : ℝ) :
    ((-Complex.I * (θ : ℂ)) • fockBeamGen n)ᴴ = -((-Complex.I * (θ : ℂ)) • fockBeamGen n) := by
  rw [Matrix.conjTranspose_smul, (fockBeamGen_isHermitian n),
    show star (-Complex.I * (θ : ℂ)) = Complex.I * (θ : ℂ) by
      simp [star_mul', Complex.conj_ofReal],
    ← neg_smul, neg_mul, neg_neg]

/-- **The sector propagator is unitary.** `Uⁿ(θ) = exp(-iθMₙ)` is the exponential of the skew-
Hermitian generator `-iθMₙ`, so `(Uⁿ)† = exp((-iθMₙ)†) = exp(iθMₙ) = (Uⁿ)⁻¹`, whence
`(Uⁿ)† Uⁿ = I`. -/
theorem fockBeamProp_mem_unitaryGroup (n : ℕ) (θ : ℝ) :
    fockBeamProp n θ ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', fockBeamProp, Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose, fockBeamGenArg_skew, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (Matrix.isUnit_exp _))

/-! ### The sector amplitude of eq. 8.110 -/

/-- The **complex sector amplitude** `⟨n-k| Eₖ |n⟩ = √(C(n,k)) cosⁿ⁻ᵏθ (-i sinθ)ᵏ` of eq. 8.110
(`θ = χΔt`): the `(k)`-th component of the first column of `Uⁿ(θ)`, i.e. the amplitude for exactly
`k` of the `n` quanta to be transferred to the environment. Its modulus is the eq.-8.110 amplitude
`√(C(n,k)(1-γ)ⁿ⁻ᵏγᵏ)` (`fockBeamAmp_norm`); the phase `(-i)ᵏ` is the physical beam-splitter phase,
immaterial to the operation (operation elements are defined up to a phase). -/
noncomputable def fockBeamAmp (θ : ℝ) (n k : ℕ) : ℂ :=
  (Real.sqrt (n.choose k) : ℂ) * (Real.cos θ : ℂ) ^ (n - k) * (-Complex.I * (Real.sin θ : ℂ)) ^ k

/-- **The sector amplitude reproduces eq. 8.110.** Its modulus is the real amplitude
`fockDampingAmp (sin²θ) n k = √(C(n,k)(1-γ)ⁿ⁻ᵏγᵏ)` of eq. 8.110, with the single-quantum loss
probability `γ = sin²θ = 1 - cos²θ` (`fockDampingProb`). Using `|cosθ|² = cos²θ = 1 - sin²θ` and
`|-i sinθ|² = sin²θ`, so the phase drops out of the modulus. -/
theorem fockBeamAmp_norm (θ : ℝ) (n k : ℕ) :
    ‖fockBeamAmp θ n k‖ = fockDampingAmp (Real.sin θ ^ 2) n k := by
  have hsq : ∀ (x : ℝ) (m : ℕ), Real.sqrt ((x ^ 2) ^ m) = |x| ^ m := fun x m => by
    rw [← sq_abs, ← pow_mul, mul_comm, pow_mul, Real.sqrt_sq (by positivity)]
  rw [fockBeamAmp, fockDampingAmp, fockDampingProbCoef]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [show (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 by
    have := Real.sin_sq_add_cos_sq θ; linarith]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    abs_of_nonneg (Real.sqrt_nonneg _), hsq, hsq]

/-! ### The vacuum sector `N = 0` -/

/-- The vacuum sector generator vanishes: `M₀ = 0` (nothing can be exchanged with a single quantum
absent from both modes). -/
theorem fockBeamGen_zero : fockBeamGen 0 = 0 := by
  ext i j; fin_cases i; fin_cases j; simp [fockBeamGen]

/-- The vacuum sector propagator is the identity: `U⁰(θ) = exp(0) = I`. The joint vacuum
`|0⟩ₐ|0_b⟩` is invariant, so `E₀|0⟩ = |0⟩` — eq. 8.110 for `n = k = 0` (amplitude `1`). -/
theorem fockBeamProp_zero (θ : ℝ) : fockBeamProp 0 θ = 1 := by
  rw [fockBeamProp, fockBeamGen_zero, smul_zero, NormedSpace.exp_zero]

/-! ### The single-excitation sector `N = 1` (eq. 8.110 derived for `n = 1`) -/

/-- The single-excitation generator is the Pauli-`X`: `M₁ = X`. In the basis `|1⟩ₐ|0_b⟩`,
`|0⟩ₐ|1_b⟩`, the operator `a†b + b†a` swaps the quantum between the two modes with unit amplitude
(`√(1·1) = 1`). -/
theorem fockBeamGen_one : fockBeamGen 1 = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [fockBeamGen, pauliX]

/-- **The single-excitation propagator** `U¹(θ) = exp(-iθX) = cosθ·I - i sinθ·X`, obtained from the
Exercise 2.35 Euler formula (`pauliDot_exp_of_unit`) since `X = x̂ · σ` is a unit-axis Pauli
combination. This is the beam-splitter unitary on one photon. -/
theorem fockBeamProp_one (θ : ℝ) :
    fockBeamProp 1 θ = (Real.cos θ : ℂ) • 1 - ((Real.sin θ : ℂ) * Complex.I) • pauliX := by
  have hn : (![1, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![1, 0, 0] : Fin 3 → ℝ) 1 ^ 2
      + (![1, 0, 0] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]; norm_num
  have hpd : pauliDot ![1, 0, 0] = pauliX := by
    simp only [pauliDot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Complex.ofReal_one, Complex.ofReal_zero,
      one_smul, zero_smul, add_zero]
  rw [fockBeamProp, fockBeamGen_one, ← hpd,
    show (-Complex.I * (θ : ℂ)) = ((↑(-θ) : ℂ) * Complex.I) by push_cast; ring,
    pauliDot_exp_of_unit hn (-θ), Real.cos_neg, Real.sin_neg, hpd]
  push_cast
  module

/-- **Eq. 8.110 for the single-excitation sector, derived from `exp(-iHΔt)`.** The first column of
`U¹(θ)` is the sector amplitude vector: `⟨j| U¹(θ) |0⟩ = fockBeamAmp θ 1 j` for `j ∈ {0,1}`. Reading
off the two operation elements, `E₀|1⟩ = cosθ|1⟩` and `E₁|1⟩ = -i sinθ|0⟩`, with moduli
`√(1-γ) = cosθ` and `√γ = |sinθ|` — exactly N&C eq. 8.110 at `n = 1` (up to the operation-element
phase `-i`). -/
theorem fockBeamProp_one_col (θ : ℝ) (j : Fin 2) :
    fockBeamProp 1 θ j 0 = fockBeamAmp θ 1 (j : ℕ) := by
  rw [fockBeamProp_one]
  fin_cases j
  · simp [fockBeamAmp, pauliX, Matrix.sub_apply, Matrix.smul_apply]
  · simp [fockBeamAmp, pauliX, Matrix.sub_apply, Matrix.smul_apply]; ring

/-! ### The sector Schrödinger equation (the amplitude vector solves `dc/dθ = -i Mₙ c`)

To pin down the first column of `Uⁿ(θ) = exp(-iθMₙ)` we exhibit the closed-form amplitude vector
`c(θ)_j = fockBeamAmp θ n j` as a solution of the linear initial-value problem
`dc/dθ = -i Mₙ c(θ)`, `c(0) = e₀` — the sector Schrödinger equation. Since `Uⁿ(θ) e₀` solves the
same problem (the next section applies `hasDerivAt_exp_smul_const` and ODE uniqueness), the two
coincide, which is exactly eq. 8.110. This section supplies the harder half: the amplitude vector's
derivative. The computation is driven by the two binomial recurrences
`√(C(n,k))·(n-k) = √((k+1)(n-k))·√(C(n,k+1))` and `√(C(n,k))·k = √(k(n-k+1))·√(C(n,k-1))`, the
`√`-forms of Pascal's rule `C(n,k+1)(k+1) = C(n,k)(n-k)`. -/

/-- **Super-diagonal binomial recurrence** — the `√`-form of Pascal's rule
`C(n,k+1)(k+1) = C(n,k)(n-k)` linking level `k` to its *successor* `k+1`:
`√(C(n,k))·(n-k) = √((k+1)(n-k))·√(C(n,k+1))` (note the `(n-k)` multiplier, not a square). It
certifies that the super-diagonal entry `√((k+1)(n-k))` of `Mₙ` maps the amplitude `√(C(n,k+1))` at
level `k+1` to the `(n-k)`-weighted amplitude at level `k`. -/
theorem sqrt_choose_succ_mul (n k : ℕ) :
    Real.sqrt (n.choose k) * (↑(n - k) : ℝ)
      = Real.sqrt ((↑(k + 1) : ℝ) * ↑(n - k)) * Real.sqrt (n.choose (k + 1)) := by
  have hnat : n.choose k * (n - k) ^ 2 = (k + 1) * (n - k) * n.choose (k + 1) := by
    have h := Nat.choose_succ_right_eq n k
    rw [pow_two, ← mul_assoc, ← h]; ring
  have hL : (0 : ℝ) ≤ Real.sqrt (n.choose k) * ↑(n - k) := by positivity
  have hR : (0 : ℝ) ≤ Real.sqrt ((↑(k + 1) : ℝ) * ↑(n - k)) * Real.sqrt (n.choose (k + 1)) := by
    positivity
  have hsq : (Real.sqrt (n.choose k) * (↑(n - k) : ℝ)) ^ 2
      = (Real.sqrt ((↑(k + 1) : ℝ) * ↑(n - k)) * Real.sqrt (n.choose (k + 1))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    have hc : (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) ^ 2
        = ((k + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) * (n.choose (k + 1) : ℝ) := by exact_mod_cast hnat
    linear_combination hc
  rw [← Real.sqrt_sq hL, hsq, Real.sqrt_sq hR]

/-- **Sub-diagonal binomial recurrence** — the `√`-form of Pascal's rule at `k-1`, linking level `k`
to its *predecessor* `k-1`: `√(C(n,k))·k = √(k(n-(k-1)))·√(C(n,k-1))` (note the `k` multiplier — the
index itself, not a square). It certifies that the sub-diagonal entry `√(k(n-(k-1)))` of `Mₙ` maps
the amplitude `√(C(n,k-1))` at level `k-1` to the `k`-weighted amplitude at level `k`. Holds for all
`k` (both sides vanish at `k = 0`). -/
theorem sqrt_choose_pred_mul (n k : ℕ) :
    Real.sqrt (n.choose k) * (↑k : ℝ)
      = Real.sqrt ((↑k : ℝ) * ↑(n - (k - 1))) * Real.sqrt (n.choose (k - 1)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
    simp only [Nat.zero_add, Nat.add_sub_cancel]
    have hnat : n.choose (m + 1) * (m + 1) ^ 2 = (m + 1) * (n - m) * n.choose m := by
      have h := Nat.choose_succ_right_eq n m
      rw [pow_two, ← mul_assoc, h]; ring
    have hL : (0 : ℝ) ≤ Real.sqrt (n.choose (m + 1)) * ↑(m + 1) := by positivity
    have hR : (0 : ℝ) ≤ Real.sqrt ((↑(m + 1) : ℝ) * ↑(n - m)) * Real.sqrt (n.choose m) := by
      positivity
    have hsq : (Real.sqrt (n.choose (m + 1)) * (↑(m + 1) : ℝ)) ^ 2
        = (Real.sqrt ((↑(m + 1) : ℝ) * ↑(n - m)) * Real.sqrt (n.choose m)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
      have hc : (n.choose (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2
          = ((m + 1 : ℕ) : ℝ) * ((n - m : ℕ) : ℝ) * (n.choose m : ℝ) := by exact_mod_cast hnat
      linear_combination hc
    rw [← Real.sqrt_sq hL, hsq, Real.sqrt_sq hR]

/-- The **sector amplitude vector** `c(θ) : Fin (n+1) → ℂ`, `c(θ)_j = ⟨j| Uⁿ(θ) |0⟩`, whose `j`-th
component is the claimed first-column amplitude `fockBeamAmp θ n j` of eq. 8.110. It is the
candidate first column of `Uⁿ(θ)`; `fockBeamAmpVec_hasDerivAt` shows it solves the sector
Schrödinger equation `dc/dθ = -i Mₙ c(θ)`. -/
noncomputable def fockBeamAmpVec (θ : ℝ) (n : ℕ) : Fin (n + 1) → ℂ :=
  fun j => fockBeamAmp θ n (j : ℕ)

/-- The `j`-th component of the sector amplitude vector is the eq.-8.110 amplitude
`fockBeamAmp θ n j`. -/
@[simp] theorem fockBeamAmpVec_apply (θ : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    fockBeamAmpVec θ n j = fockBeamAmp θ n (j : ℕ) := rfl

/-- **The `θ`-derivative of the sector amplitude, in vector-field form.** For `k ≤ n`,
`d/dθ fockBeamAmp θ n k` equals `-i·(√((k+1)(n-k))·fockBeamAmp θ n (k+1) +
√(k(n-(k-1)))·fockBeamAmp θ n (k-1))`, i.e. the `k`-th component of `-i Mₙ` applied to the
amplitude vector. Computed by the product/chain rule, then matched to the field by the two binomial
recurrences (`sqrt_choose_succ_mul`, `sqrt_choose_pred_mul`) and `(-i)² = -1`. -/
theorem fockBeamAmp_hasDerivAt (θ : ℝ) {n k : ℕ} (hk : k ≤ n) :
    HasDerivAt (fun t => fockBeamAmp t n k)
      (-Complex.I * ((↑(Real.sqrt ((↑(k + 1) : ℝ) * ↑(n - k))) : ℂ) * fockBeamAmp θ n (k + 1)
        + (↑(Real.sqrt ((↑k : ℝ) * ↑(n - (k - 1)))) : ℂ) * fockBeamAmp θ n (k - 1))) θ := by
  have hC : HasDerivAt (fun t => (↑(Real.cos t) : ℂ)) (↑(-Real.sin θ)) θ :=
    (Real.hasDerivAt_cos θ).ofReal_comp
  have hS : HasDerivAt (fun t => (↑(Real.sin t) : ℂ)) (↑(Real.cos θ)) θ :=
    (Real.hasDerivAt_sin θ).ofReal_comp
  have hw : HasDerivAt (fun t => (-Complex.I * ↑(Real.sin t) : ℂ)) (-Complex.I * ↑(Real.cos θ)) θ :=
    hS.const_mul (-Complex.I)
  have haC := (hC.pow (n - k)).const_mul (↑(Real.sqrt (n.choose k)) : ℂ)
  have hwpow := hw.pow k
  have hfull := haC.mul hwpow
  have hrec1 : (↑(Real.sqrt (n.choose k)) : ℂ) * (↑(n - k) : ℂ)
      = (↑(Real.sqrt ((↑(k + 1) : ℝ) * ↑(n - k))) : ℂ) * (↑(Real.sqrt (n.choose (k + 1))) : ℂ) := by
    exact_mod_cast sqrt_choose_succ_mul n k
  have hrec2 : (↑(Real.sqrt (n.choose k)) : ℂ) * (↑k : ℂ)
      = (↑(Real.sqrt ((↑k : ℝ) * ↑(n - (k - 1)))) : ℂ) * (↑(Real.sqrt (n.choose (k - 1))) : ℂ) := by
    exact_mod_cast sqrt_choose_pred_mul n k
  convert hfull using 1
  · funext t
    simp only [fockBeamAmp, Pi.mul_apply, Pi.pow_apply]
  simp only [fockBeamAmp, Complex.ofReal_neg, Pi.pow_apply]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simp only [Nat.zero_add, Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.sub_zero,
      Nat.zero_sub, Real.sqrt_zero, Complex.ofReal_zero, pow_zero, one_mul, mul_one,
      Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, pow_one] at hrec1 ⊢
    linear_combination
      ((Real.sin θ : ℂ) * (Real.cos θ : ℂ) ^ (n - 1)) * hrec1
      + ((Real.sin θ : ℂ) * (Real.cos θ : ℂ) ^ (n - 1)
          * (↑(Real.sqrt (n : ℝ)) : ℂ) * (↑(Real.sqrt (n.choose 1)) : ℂ)) * Complex.I_sq
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hrec1 hrec2 ⊢
    rw [show n - (m + 1 + 1) = n - (m + 1) - 1 from by omega]
    rw [pow_succ (-Complex.I * (Real.sin θ : ℂ)) (m + 1)]
    rw [show n - m = n - (m + 1) + 1 from by omega] at hrec2 ⊢
    rw [pow_succ (Real.cos θ : ℂ) (n - (m + 1))]
    linear_combination
      ((Real.sin θ : ℂ) * (Real.cos θ : ℂ) ^ (n - (m + 1) - 1)
          * (-Complex.I * (Real.sin θ : ℂ)) ^ (m + 1)) * hrec1
      + (Complex.I * (Real.cos θ : ℂ) ^ (n - (m + 1)) * (Real.cos θ : ℂ)
          * (-Complex.I * (Real.sin θ : ℂ)) ^ m) * hrec2
      + ((Real.sin θ : ℂ) * (Real.cos θ : ℂ) ^ (n - (m + 1) - 1)
          * (-Complex.I * (Real.sin θ : ℂ)) ^ (m + 1)
          * (↑(Real.sqrt ((↑(m + 1 + 1) : ℝ) * ↑(n - (m + 1)))) : ℂ)
          * (↑(Real.sqrt (n.choose (m + 1 + 1))) : ℂ)) * Complex.I_sq

/-- **The tridiagonal generator applied to the amplitude vector.** `(Mₙ c(θ))_r` collapses to the
two neighbour terms `√((r+1)(n-r))·fockBeamAmp θ n (r+1) + √(r(n-(r-1)))·fockBeamAmp θ n (r-1)`:
`Mₙ` is tridiagonal, so the matrix-vector sum over the `(n+1)`-dim sector picks out the super- and
sub-diagonal neighbours (the boundary terms vanishing because their `√`-coefficients do). -/
theorem fockBeamGen_mulVec_amp (θ : ℝ) (n : ℕ) (r : Fin (n + 1)) :
    (fockBeamGen n *ᵥ fockBeamAmpVec θ n) r
      = (↑(Real.sqrt ((↑((r : ℕ) + 1) : ℝ) * ↑(n - (r : ℕ)))) : ℂ) * fockBeamAmp θ n ((r : ℕ) + 1)
        + (↑(Real.sqrt ((↑(r : ℕ) : ℝ) * ↑(n - ((r : ℕ) - 1)))) : ℂ)
            * fockBeamAmp θ n ((r : ℕ) - 1) := by
  classical
  have hrange : (fockBeamGen n *ᵥ fockBeamAmpVec θ n) r
      = ∑ m ∈ Finset.range (n + 1),
          (if (r : ℕ) + 1 = m then (↑(Real.sqrt (((r : ℕ) + 1) * (n - (r : ℕ)))) : ℂ)
            else if m + 1 = (r : ℕ) then (↑(Real.sqrt ((m + 1) * (n - m))) : ℂ) else 0)
          * fockBeamAmp θ n m := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun m => (if (r : ℕ) + 1 = m then (↑(Real.sqrt (((r : ℕ) + 1) * (n - (r : ℕ)))) : ℂ)
          else if m + 1 = (r : ℕ) then (↑(Real.sqrt ((m + 1) * (n - m))) : ℂ) else 0)
        * fockBeamAmp θ n m) (n + 1)]
    simp only [Matrix.mulVec, dotProduct, fockBeamAmpVec_apply, fockBeamGen]
  rw [hrange]
  -- split the two mutually-exclusive branches into a super-diagonal and a sub-diagonal sum
  have hsplit : ∀ m,
      (if (r : ℕ) + 1 = m then (↑(Real.sqrt (((r : ℕ) + 1) * (n - (r : ℕ)))) : ℂ)
        else if m + 1 = (r : ℕ) then (↑(Real.sqrt ((m + 1) * (n - m))) : ℂ) else 0)
        * fockBeamAmp θ n m
      = (if (r : ℕ) + 1 = m then (↑(Real.sqrt (((r : ℕ) + 1) * (n - (r : ℕ)))) : ℂ)
          * fockBeamAmp θ n m else 0)
        + (if m + 1 = (r : ℕ) then (↑(Real.sqrt ((m + 1) * (n - m))) : ℂ)
            * fockBeamAmp θ n m else 0) := by
    intro m
    by_cases h1 : (r : ℕ) + 1 = m
    · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega), add_zero]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : m + 1 = (r : ℕ)
      · rw [ite_eq_left h2, ite_eq_left h2, zero_add]
      · rw [ite_eq_right h2, ite_eq_right h2, zero_mul, add_zero]
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib]
  congr 1
  · -- super-diagonal term isolates m = r + 1
    rw [Finset.sum_eq_single ((r : ℕ) + 1)]
    · rw [ite_eq_left rfl, ← Nat.cast_add_one, ← Nat.cast_sub r.is_le]
    · intro b _ hb; rw [ite_eq_right (by omega)]
    · intro hb
      rw [ite_eq_left rfl]
      -- r + 1 ∉ range (n+1) ⇒ r = n ⇒ the √-coefficient vanishes
      have hrn : (r : ℕ) = n := by
        have := r.isLt; simp only [Finset.mem_range] at hb; omega
      rw [hrn, sub_self, mul_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
  · -- sub-diagonal term isolates m = r - 1
    rw [Finset.sum_eq_single ((r : ℕ) - 1)]
    · rcases Nat.eq_zero_or_pos (r : ℕ) with hr0 | hr0
      · rw [hr0]; simp
      · have hsub : (r : ℕ) - 1 ≤ n := le_trans (Nat.sub_le _ _) r.is_le
        have hb : (↑((r : ℕ) - 1) : ℝ) + 1 = (↑(r : ℕ) : ℝ) := by
          rw [Nat.cast_sub hr0, Nat.cast_one]; ring
        rw [ite_eq_left (by omega), hb, ← Nat.cast_sub hsub]
    · intro b _ hb; rw [ite_eq_right (by omega)]
    · intro hb
      simp only [Finset.mem_range, not_lt] at hb
      have := r.isLt; omega

/-- **The sector amplitude vector solves the sector Schrödinger equation.**
`d/dθ c(θ) = -i Mₙ c(θ)` where `c(θ) = fockBeamAmpVec θ n` is the eq.-8.110 amplitude vector and
`Mₙ = fockBeamGen n`. This is the dynamical heart of part (1): the closed-form amplitude vector is a
solution of the linear IVP whose (unique) solution is the first column `Uⁿ(θ) e₀` of the sector
propagator, so `Uⁿ(θ) e₀ = c(θ)` — eq. 8.110 — once ODE uniqueness is applied (`fockBeamProp_col`).
Proved componentwise (`hasDerivAt_pi`): each `fockBeamAmp_hasDerivAt` is the `k`-th component of
`-i Mₙ c(θ)` by `fockBeamGen_mulVec_amp`. -/
theorem fockBeamAmpVec_hasDerivAt (θ : ℝ) (n : ℕ) :
    HasDerivAt (fun t => fockBeamAmpVec t n)
      ((-Complex.I • fockBeamGen n) *ᵥ fockBeamAmpVec θ n) θ := by
  rw [hasDerivAt_pi]
  intro j
  have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
  rw [Matrix.smul_mulVec, Pi.smul_apply, fockBeamGen_mulVec_amp, smul_eq_mul]
  exact fockBeamAmp_hasDerivAt θ hj

/-! ### The general-`n` first column (eq. 8.110 for all `n`) by ODE uniqueness

With the sector Schrödinger equation `dc/dθ = -i Mₙ c` in hand, we conclude the general-`n` first
column `⟨j| Uⁿ(θ) |0⟩ = fockBeamAmp θ n j` (eq. 8.110). Both the closed-form amplitude vector `c(θ)`
(`fockBeamAmpVec_hasDerivAt`) and the propagator's first column `Uⁿ(θ) e₀` solve the *same* linear
initial-value problem `dw/dθ = -i Mₙ w`, `w(0) = e₀`; the derivative of `Uⁿ(θ) e₀` comes from the
matrix-exponential derivative `d/dθ exp(θ B) = B exp(θ B)` (`hasDerivAt_exp_smul_const'`, with
`B = -i Mₙ`) composed with the fixed continuous-linear map `M ↦ M e₀`. Global Lipschitz continuity
of the linear field `x ↦ B x` (a finite-dimensional continuous-linear map) supplies uniqueness
(`ODE_solution_unique_univ`), so the two solutions coincide — which is exactly eq. 8.110.
-/

/-- The sector propagator as the real-parameter matrix-exponential curve `Uⁿ(θ) = exp(θ • B)` with
`B = -i Mₙ`, folding the scalar `-iθ` into the propagator's angle. This is the form to which the
matrix-exponential derivative `hasDerivAt_exp_smul_const'` applies. -/
theorem fockBeamProp_eq_exp (n : ℕ) (θ : ℝ) :
    fockBeamProp n θ = NormedSpace.exp (θ • (-Complex.I • fockBeamGen n)) := by
  rw [fockBeamProp, ← smul_assoc, Complex.real_smul, mul_comm]

/-- At `θ = 0` the propagator is the identity: `Uⁿ(0) = exp 0 = 1` (no time has elapsed, so nothing
is exchanged). This is the initial condition `w(0) = e₀` for the first column. -/
theorem fockBeamProp_apply_zero (n : ℕ) : fockBeamProp n 0 = 1 := by
  rw [fockBeamProp]; simp [NormedSpace.exp_zero]

/-- The amplitude vector at `θ = 0` is the first basis vector `e₀ = |0⟩` (the initial condition
`c(0) = e₀` of the sector Schrödinger equation): `cos 0 = 1` keeps the `k = 0` amplitude
`√C(n,0) = 1` and `sin 0 = 0` kills every `k ≥ 1` amplitude. -/
theorem fockBeamAmpVec_zero (n : ℕ) :
    fockBeamAmpVec 0 n = Pi.single (0 : Fin (n + 1)) 1 := by
  funext j
  rw [fockBeamAmpVec_apply, fockBeamAmp, Real.cos_zero, Real.sin_zero, Complex.ofReal_zero,
    mul_zero]
  rcases eq_or_ne j 0 with hj | hj
  · subst hj; simp
  · have hj' : (j : ℕ) ≠ 0 := by rwa [Ne, Fin.val_eq_zero_iff]
    rw [Pi.single_eq_of_ne hj, zero_pow hj', mul_zero]

/-- **The propagator's first column solves the sector Schrödinger IVP** `d/dθ (Uⁿ(θ) e₀) =
-i Mₙ (Uⁿ(θ) e₀)`. The derivative of the matrix-exponential curve `θ ↦ exp(θ B)` is `B exp(θ B)`
(`hasDerivAt_exp_smul_const'`); composing with the continuous-linear map `Φ : M ↦ M e₀` and using
`(B · exp(θB)) e₀ = B (exp(θB) e₀)` (`mulVec_mulVec`) gives the vector-field form. The required
`CompleteSpace (Matrix …)` is supplied explicitly from finite-dimensionality
(`FiniteDimensional.completeSpace`), sidestepping the operator-norm completeness instance. -/
theorem fockBeamProp_col_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun t => fockBeamProp n t *ᵥ (Pi.single (0 : Fin (n + 1)) 1))
      ((-Complex.I • fockBeamGen n) *ᵥ (fockBeamProp n θ *ᵥ (Pi.single (0 : Fin (n + 1)) 1)))
      θ := by
  have : FiniteDimensional ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Module.Finite.trans ℂ _
  simp only [fockBeamProp_eq_exp]
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := -Complex.I • fockBeamGen n with hB
  set e0 : Fin (n + 1) → ℂ := Pi.single 0 1 with he0
  let Φ : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) →L[ℝ] (Fin (n + 1) → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M *ᵥ e0,
        map_add' := fun M N => by ext i; simp [Matrix.add_mulVec],
        map_smul' := fun (c : ℝ) M => by ext i; simp [Matrix.smul_mulVec] }
  have hexp : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • B)) (B * NormedSpace.exp (θ • B)) θ :=
    @hasDerivAt_exp_smul_const' ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) _ _ _
      (FiniteDimensional.completeSpace ℂ _) B θ
  -- The composed curve `Φ ∘ exp(·•B)` is `fun t => exp(t•B) *ᵥ e₀`, with derivative
  -- `Φ (B · exp(θ•B)) = (B · exp(θ•B)) *ᵥ e₀ = B *ᵥ (exp(θ•B) *ᵥ e₀)` (`mulVec_mulVec`).
  exact (Φ.hasFDerivAt.comp_hasDerivAt θ hexp).congr_deriv
    (Matrix.mulVec_mulVec e0 B (NormedSpace.exp (θ • B))).symm

/-- **Eq. 8.110 for all `n`, derived from `U = exp(-iHΔt)`.** The first column of the sector
propagator `Uⁿ(θ)` is the eq.-8.110 amplitude vector: `⟨j| Uⁿ(θ) |0⟩ = fockBeamAmp θ n j`. Both
`Uⁿ(θ) e₀` (`fockBeamProp_col_hasDerivAt`) and the closed-form amplitude vector `c(θ)`
(`fockBeamAmpVec_hasDerivAt`) solve the linear IVP `dw/dθ = -i Mₙ w`, `w(0) = e₀`
(`fockBeamProp_apply_zero`, `fockBeamAmpVec_zero`), so by ODE uniqueness they coincide. This is the
faithful sector-by-sector content of eq. 8.110; its modulus is the real amplitude
`√(C(n,k)(1-γ)ⁿ⁻ᵏγᵏ)` (`fockBeamAmp_norm`). -/
theorem fockBeamProp_col (n : ℕ) (θ : ℝ) (j : Fin (n + 1)) :
    fockBeamProp n θ j 0 = fockBeamAmp θ n (j : ℕ) := by
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := -Complex.I • fockBeamGen n with hB
  have hKey : (fun t => fockBeamProp n t *ᵥ (Pi.single (0 : Fin (n + 1)) 1))
      = fun t => fockBeamAmpVec t n := by
    apply ODE_solution_unique_univ (t₀ := 0)
      (v := fun _ x => B *ᵥ x) (s := fun _ => Set.univ)
      (K := ‖(Matrix.mulVecLin B).toContinuousLinearMap‖₊)
    · intro t
      rw [lipschitzOnWith_univ]
      exact ((Matrix.mulVecLin B).toContinuousLinearMap).lipschitzWith
    · intro t
      exact ⟨fockBeamProp_col_hasDerivAt n t, Set.mem_univ _⟩
    · intro t
      exact ⟨fockBeamAmpVec_hasDerivAt t n, Set.mem_univ _⟩
    · rw [fockBeamProp_apply_zero, Matrix.one_mulVec, fockBeamAmpVec_zero]
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (congrFun hKey θ) j

/-! ### The assembled `ℕ`-indexed operation element `Eₖ = ⟨k_b|U|0_b⟩` (eq. 8.110)

The sector first columns `fockBeamProp_col` (eq. 8.110 derived for each `n`) assemble into a single
operation element `Eₖ = ⟨k_b|U|0_b⟩` on the principal oscillator's infinite-dimensional number
space, as a matrix `Matrix ℕ ℕ ℂ`. Reading `U = exp(-iHΔt)` sector by sector, `Eₖ` lowers `|n⟩` to
`|n-k⟩`
with the complex sector amplitude `⟨n-k|Eₖ|n⟩ = fockBeamProp n θ ⟨k⟩ 0 = fockBeamAmp θ n k`. This
closes part (1) — eq. 8.110 derived from `U` for all `n` — and reconciles it with the
trace-preservation half (part (2), `Concrete/HarmonicOscillatorAmplitudeDamping.lean`): the modulus
of the derived `Eₖ` is exactly the eq.-8.110 real operation element `fockDampingKraus (sin²θ)`
(`fockBeamKraus_norm`, the per-column phase `(-i)ᵏ` dropping out of the modulus), and the derived
`Eₖ` are themselves trace preserving (`fockBeamKraus_completeness`, `Σₖ Eₖ† Eₖ = I`, the phase
cancelling in `Eₖ† Eₖ`). -/

/-- The **operation element** `Eₖ = ⟨k_b|U|0_b⟩` of eq. 8.110, assembled over all excitation-number
sectors into a single matrix `Matrix ℕ ℕ ℂ` on the principal oscillator's number space. Reading the
propagator `U = exp(-iHΔt)` sector by sector, `Eₖ` lowers `|n⟩` to `|n-k⟩` with the complex sector
amplitude `fockBeamAmp θ n k` (`fockBeamKraus_eq_prop_col`: this entry *is* the `k`-th component
`⟨k_b|Uⁿ(θ)|0_b⟩` of the sector propagator's first column, eq. 8.110 for all `n`). The `(r,c)`
entry is `fockBeamAmp θ c k` when `r + k = c` (row `c-k`, column `c`), and `0` otherwise; its
modulus is the eq.-8.110 real operation element `fockDampingKraus (sin²θ)` (`fockBeamKraus_norm`),
the per-column
phase `(-i)ᵏ` being immaterial to the operation. -/
noncomputable def fockBeamKraus (θ : ℝ) (k : ℕ) : Matrix ℕ ℕ ℂ :=
  fun r c => if r + k = c then fockBeamAmp θ c k else 0

/-- The defining entrywise formula for the derived operation element `Eₖ` (eq. 8.110). -/
theorem fockBeamKraus_apply (θ : ℝ) (k r c : ℕ) :
    fockBeamKraus θ k r c = if r + k = c then fockBeamAmp θ c k else 0 := rfl

/-- **The assembled operation element reads off the sector propagator's first column.** For `k ≤ n`
the amplitude `⟨n-k|Eₖ|n⟩` of the assembled `Eₖ` is exactly the `k`-th component of the first column
of the sector propagator `Uⁿ(θ) = exp(-iθMₙ)` — the environment overlap `⟨k_b|Uⁿ(θ)|0_b⟩`:
`fockBeamKraus θ k (n-k) n = fockBeamProp n θ ⟨k⟩ 0`. This is the assembly of `Eₖ = ⟨k_b|U|0_b⟩` out
of the finite excitation-number sectors, through `fockBeamProp_col` (eq. 8.110 for all `n`). -/
theorem fockBeamKraus_eq_prop_col (θ : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    fockBeamKraus θ k (n - k) n = fockBeamProp n θ ⟨k, by omega⟩ 0 := by
  rw [fockBeamKraus_apply, ite_eq_left (by omega), fockBeamProp_col]

/-- **Reconciliation with part (2)'s eq.-8.110 operation element.** The modulus of the operation
element `Eₖ` derived from `U = exp(-iHΔt)` is entrywise that of the real eq.-8.110 operation element
`fockDampingKraus (sin²θ)` (with loss probability `γ = sin²θ`, `fockDampingProb`):
`‖(Eₖ)_{rc}‖ = ‖(fockDampingKraus (sin²θ) k)_{rc}‖`. The derived elements thus coincide with the
eq.-8.110 elements up to the per-column phase `(-i)ᵏ`, immaterial to the operation — closing the
loop between the part-(1) derivation and part (2)'s modulus form. -/
theorem fockBeamKraus_norm (θ : ℝ) (k r c : ℕ) :
    ‖fockBeamKraus θ k r c‖ = ‖fockDampingKraus (Real.sin θ ^ 2) k r c‖ := by
  rw [fockBeamKraus_apply, fockDampingKraus_apply]
  by_cases h : r + k = c
  · rw [ite_eq_left h, ite_eq_left h, fockBeamAmp_norm, Complex.norm_real, Real.norm_eq_abs,
      fockDampingAmp, abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [ite_eq_right h, ite_eq_right h]

/-- **The Gram operator `Eₖ† Eₖ` of the derived operation element is part (2)'s diagonal loss
operator.** `∑ᶠ j (Eₖ)ᴴ a j (Eₖ) j b = fockDampingGram (sin²θ) k a b`: the per-column phase `(-i)ᵏ`
of `Eₖ` cancels in `Eₖ† Eₖ` (`conj z · z = ‖z‖²`), leaving only the modulus — the loss probability
`C(a,k)(1-γ)^{a-k}γ^k`. Same shape as `fockDampingGram_eq`, `Eₖ` having a single nonzero entry per
column, so the product is diagonal. -/
theorem fockBeamGram_eq (θ : ℝ) (k a b : ℕ) :
    (∑ᶠ j, (fockBeamKraus θ k)ᴴ a j * fockBeamKraus θ k j b)
      = fockDampingGram (Real.sin θ ^ 2) k a b := by
  have hγ0 : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hγ1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hzero : ∀ j, j ≠ a - k →
      (fockBeamKraus θ k)ᴴ a j * fockBeamKraus θ k j b = 0 := by
    intro j hj
    simp only [Matrix.conjTranspose_apply, fockBeamKraus_apply]
    rw [ite_eq_right (show ¬ j + k = a by omega), star_zero, zero_mul]
  rw [finsum_eq_single _ (a - k) hzero]
  simp only [fockDampingGram, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    fockBeamKraus_apply]
  rcases eq_or_ne a b with hab | hab
  · subst hab
    by_cases hka : k ≤ a
    · rw [ite_eq_left (show a - k + k = a by omega), ite_eq_left rfl, ← starRingEnd_apply, mul_comm,
        Complex.mul_conj, Complex.normSq_eq_norm_sq, fockBeamAmp_norm, fockDampingAmp_sq hγ0 hγ1]
    · rw [ite_eq_right (show ¬ a - k + k = a by omega), ite_eq_left rfl,
        fockDampingProbCoef_eq_zero (show a < k by omega), Complex.ofReal_zero, star_zero, zero_mul]
  · rw [ite_eq_right hab]
    by_cases hka : k ≤ a
    · rw [ite_eq_left (show a - k + k = a by omega), ite_eq_right (show ¬ a - k + k = b by omega),
          mul_zero]
    · rw [ite_eq_right (show ¬ a - k + k = a by omega), star_zero, zero_mul]

/-- **Exercise 8.21, closing the loop: the derived operation elements are trace preserving.** The
operation elements `Eₖ = ⟨k_b|U|0_b⟩` derived from `U = exp(-iHΔt)` satisfy the completeness
relation `Σₖ Eₖ† Eₖ = I`, stated entrywise over the number-state index `ℕ`. Each `Eₖ† Eₖ` is the
diagonal loss operator `fockDampingGram (sin²θ)` (`fockBeamGram_eq`, the phase cancelling), so the
relation reduces to the binomial completeness of part (2) (`fockDampingKraus_completeness`): the
level-`n` diagonal sum is `Σₖ C(n,k)(1-γ)^{n-k}γ^k = 1`. Thus the *derived* `Eₖ` — not merely their
modulus form — define a trace-preserving quantum operation. -/
theorem fockBeamKraus_completeness (θ : ℝ) (a b : ℕ) :
    (∑ᶠ k, ∑ᶠ j, (fockBeamKraus θ k)ᴴ a j * fockBeamKraus θ k j b)
      = (1 : Matrix ℕ ℕ ℂ) a b := by
  have hγ0 : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hγ1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have h1 : (∑ᶠ k, ∑ᶠ j, (fockBeamKraus θ k)ᴴ a j * fockBeamKraus θ k j b)
      = ∑ᶠ k, fockDampingGram (Real.sin θ ^ 2) k a b :=
    finsum_congr fun k => fockBeamGram_eq θ k a b
  have h2 : (∑ᶠ k, fockDampingGram (Real.sin θ ^ 2) k a b)
      = ∑ᶠ k, ∑ᶠ j, (fockDampingKraus (Real.sin θ ^ 2) k)ᴴ a j
          * fockDampingKraus (Real.sin θ ^ 2) k j b :=
    finsum_congr fun k => (fockDampingGram_eq hγ0 hγ1 k a b).symm
  rw [h1, h2, fockDampingKraus_completeness hγ0 hγ1 a b]

end AxQM.Concrete
