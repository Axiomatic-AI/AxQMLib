/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DipolarCoupling
import ToMathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Swap
import ToMathlib.Analysis.Normed.Algebra.MatrixExponential
import ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Concrete: the SWAP and √SWAP gates from the Heisenberg exchange interaction

*Nielsen & Chuang, Exercise 7.52 (Universality of the Heisenberg Hamiltonian), Parts 1 and 2.*

The controlled Heisenberg (isotropic exchange) coupling of eq. (7.174) is
`H(t) = J(t) S⃗₁·S⃗₂` with `S⃗ᵢ = σ⃗ᵢ/2`, so the dimensionless coupling operator is

`S⃗₁·S⃗₂ = ¼ (X⊗X + Y⊗Y + Z⊗Z) = ¼ σ⃗₁·σ⃗₂`  (`heisenbergDot`, from `spinSpinCoupling`).

The whole exercise is pure `2⊗2 = 4`-dimensional complex-matrix mathematics: the
matrix exponential is Mathlib's `NormedSpace.exp`, and every statement names only concrete
matrices (`spinSpinCoupling`, the Pauli matrices, the swap matrix) and real trigonometric
functions.

## The key algebraic fact

`σ⃗₁·σ⃗₂ = 2·SWAP − I` on the two-qubit space (`spinSpinCoupling_eq_two_smul_twoQubitSwap_sub_one`),
so `S⃗₁·S⃗₂ = ½·SWAP − ¼·I` (`heisenbergDot_eq`). Since `SWAP² = I` (`twoQubitSwap_mul_self`), the
time-evolution operator `exp(−iφ S⃗₁·S⃗₂)` splits — via `Matrix.exp_add_of_commute` and the Euler
formula for an involution `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` (exactly as in
`pauliDot_exp_of_unit`) — into a global phase times a `cos/sin` combination of `I` and `SWAP`:

`heisenbergEvolution φ = exp(−iφ S⃗₁·S⃗₂) = e^{iφ/4}·(cos(φ/2)·I − i sin(φ/2)·SWAP)`
(`heisenbergEvolution_eq`).

## Main results

* `heisenbergEvolution_pi` — **Part 1.** At `φ = π` the interaction implements a swap operation:
  `exp(−iπ S⃗₁·S⃗₂) = e^{−iπ/4}·SWAP`, i.e. `SWAP` up to the physically irrelevant global phase
  `e^{−iπ/4}`.
* `sqrtSwapHeis_eq` — **Part 2.** At `φ = π/2` (half the time) one obtains the `√SWAP` gate in
  closed form `e^{iπ/8}·(√2/2)·(I − i·SWAP)`.
* `sqrtSwapHeis_mul_self` — `√SWAP² = exp(−iπ S⃗₁·S⃗₂)`, the swap-evolution of Part 1, so
  `sqrtSwapHeis` is genuinely a square root of the swap operation.

(Part 3 — the universality of `√SWAP`, i.e. building a `CNOT` from it and single-qubit gates — is
formalised in the companion file `Concrete/SqrtSwapCNOT.lean`.)
-/

open Matrix NormedSpace
open scoped Kronecker BigOperators

namespace AxQM.Concrete

/-- The **two-qubit SWAP gate** `SWAP` as a `4×4` complex matrix on `Fin 2 × Fin 2`: the basis
transposition `|01⟩ ↔ |10⟩` exchanging the two qubits (`SWAP |ab⟩ = |ba⟩`). It is Mathlib's
general transposition matrix `Matrix.swap ℂ (0,1) (1,0)`, so it inherits the full `Matrix.swap` API
(unitarity, `swap_mul_self`, entry lemmas). -/
noncomputable def twoQubitSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.swap ℂ ((0, 1) : Fin 2 × Fin 2) ((1, 0) : Fin 2 × Fin 2)

/-- `SWAP` is an involution: `SWAP² = I` (swapping the two qubits twice is the identity),
inherited from the general `Matrix.swap_mul_self`. -/
theorem twoQubitSwap_mul_self : twoQubitSwap * twoQubitSwap = 1 :=
  Matrix.swap_mul_self _ _

/-- Entrywise form of `SWAP`: `SWAP i j = 1` iff `i = Prod.swap j` (the transposition exchanging
the two coordinates), else `0`. Convenient for the `Kronecker`-level entry computation below. -/
theorem twoQubitSwap_apply (i j : Fin 2 × Fin 2) :
    twoQubitSwap i j = if i = j.swap then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [twoQubitSwap, Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Equiv.swap_apply_def, Prod.swap, Prod.ext_iff]

/-- **The exchange interaction is `2·SWAP − I`.** The isotropic spin-spin coupling
`σ⃗₁·σ⃗₂ = X⊗X + Y⊗Y + Z⊗Z` (`spinSpinCoupling`) equals `2·SWAP − I` on the two-qubit space. This
is the algebraic heart of Exercise 7.52: it identifies the eigenspaces of the Heisenberg
Hamiltonian with the symmetric (`+1`) and antisymmetric (`−3`) subspaces of `SWAP`. -/
theorem spinSpinCoupling_eq_two_smul_twoQubitSwap_sub_one :
    spinSpinCoupling = (2 : ℂ) • twoQubitSwap - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSpinCoupling, twoQubitSwap_apply, pauliSigma, pauliX, pauliY, pauliZ,
      Fin.sum_univ_three, Matrix.sub_apply, Prod.ext_iff] <;> norm_num

/-- The dimensionless **Heisenberg coupling operator** `S⃗₁·S⃗₂ = ¼ σ⃗₁·σ⃗₂` (with `S⃗ᵢ = σ⃗ᵢ/2`),
the operator appearing in the exchange Hamiltonian `H = J S⃗₁·S⃗₂` of Nielsen & Chuang (7.174). -/
noncomputable def heisenbergDot : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 4 : ℂ) • spinSpinCoupling

/-- `S⃗₁·S⃗₂ = ½·SWAP − ¼·I`, obtained from `σ⃗₁·σ⃗₂ = 2·SWAP − I` by scaling by `¼`. -/
theorem heisenbergDot_eq :
    heisenbergDot
      = (1 / 2 : ℂ) • twoQubitSwap
        - (1 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [heisenbergDot, spinSpinCoupling_eq_two_smul_twoQubitSwap_sub_one]; module

/-- The **Heisenberg time-evolution operator** `exp(−iφ S⃗₁·S⃗₂)`: turning on the exchange
interaction for a (dimensionless) duration `φ`. The swap operation of Part 1 is `φ = π` and the
`√SWAP` gate of Part 2 is `φ = π/2`. -/
noncomputable def heisenbergEvolution (φ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  exp ((-Complex.I * (φ : ℂ)) • heisenbergDot)

open scoped Matrix.Norms.Operator in
/-- **Closed form of the Heisenberg propagator.** For every real `φ`,
`exp(−iφ S⃗₁·S⃗₂) = e^{iφ/4}·(cos(φ/2)·I − i sin(φ/2)·SWAP)`.

Proof: write `−iφ S⃗₁·S⃗₂ = (iφ/4)·I + (−iφ/2)·SWAP` (from `heisenbergDot_eq`); the two summands
commute, so `Matrix.exp_add_of_commute` factors the exponential, and each factor is an involution
Euler formula `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` (with `I² = I` and `SWAP² = I`). -/
theorem heisenbergEvolution_eq (φ : ℝ) :
    heisenbergEvolution φ
      = Complex.exp (((φ / 4 : ℝ) : ℂ) * Complex.I) •
          ((Real.cos (φ / 2) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
            - ((Real.sin (φ / 2) : ℂ) * Complex.I) • twoQubitSwap) := by
  rw [heisenbergEvolution]
  have hexp : (-Complex.I * (φ : ℂ)) • heisenbergDot
      = (((φ / 4 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + (((-φ / 2 : ℝ) : ℂ) * Complex.I) • twoQubitSwap := by
    rw [heisenbergDot_eq]; push_cast; module
  have hcomm : Commute
      ((((φ / 4 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
      ((((-φ / 2 : ℝ) : ℂ) * Complex.I) • twoQubitSwap) :=
    ((Commute.one_left _).smul_left _).smul_right _
  have e1 : exp ((((φ / 4 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
      = (Real.cos (φ / 4) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + ((Real.sin (φ / 4) : ℂ) * Complex.I) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2)
            ℂ) := by
    open scoped Matrix.Norms.Operator in
    exact exp_smul_mul_I_of_mul_self_eq_one
      (by simp : (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) * 1 = 1) (φ / 4)
  have e2 : exp ((((-φ / 2 : ℝ) : ℂ) * Complex.I) • twoQubitSwap)
      = (Real.cos (-φ / 2) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + ((Real.sin (-φ / 2) : ℂ) * Complex.I) • twoQubitSwap := by
    open scoped Matrix.Norms.Operator in
    exact exp_smul_mul_I_of_mul_self_eq_one twoQubitSwap_mul_self (-φ / 2)
  rw [hexp, Matrix.exp_add_of_commute _ _ hcomm, e1, e2]
  rw [← add_smul, ← Complex.exp_ofReal_mul_I]
  rw [Matrix.smul_mul, one_mul]
  refine congrArg (_ • ·) ?_
  simp only [neg_div, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  module

/-- **Nielsen & Chuang, Exercise 7.52, Part 1 (the swap operation).** Turning on the Heisenberg
interaction for `φ = π` implements a swap operation:
`exp(−iπ S⃗₁·S⃗₂) = e^{−iπ/4}·SWAP`,
i.e. exactly `SWAP` up to the (physically irrelevant) global phase `e^{−iπ/4}`. -/
theorem heisenbergEvolution_pi :
    heisenbergEvolution Real.pi
      = Complex.exp ((-(Real.pi / 4 : ℝ) : ℂ) * Complex.I) • twoQubitSwap := by
  rw [heisenbergEvolution_eq, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_mul, zero_sub,
    smul_neg, smul_smul]
  rw [← neg_smul]
  congr 1
  have hI : (-Complex.I) = Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  rw [← mul_neg, hI, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- The **`√SWAP` gate** obtained by running the Heisenberg interaction for half the swap time,
`√SWAP = exp(−i(π/2) S⃗₁·S⃗₂) = heisenbergEvolution (π/2)`. -/
noncomputable def sqrtSwapHeis : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  heisenbergEvolution (Real.pi / 2)

/-- **Nielsen & Chuang, Exercise 7.52, Part 2 (compute the `√SWAP` transform).** The closed form
`√SWAP = e^{iπ/8}·(√2/2)·(I − i·SWAP)`, obtained from `heisenbergEvolution_eq` at `φ = π/2` with
`cos(π/4) = sin(π/4) = √2/2`. -/
theorem sqrtSwapHeis_eq :
    sqrtSwapHeis
      = Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) •
          (((Real.sqrt 2 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
            - (((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I) • twoQubitSwap) := by
  rw [sqrtSwapHeis, heisenbergEvolution_eq,
    show Real.pi / 2 / 4 = Real.pi / 8 by ring, show Real.pi / 2 / 2 = Real.pi / 4 by ring,
    Real.cos_pi_div_four, Real.sin_pi_div_four]

open scoped Matrix.Norms.Operator in
/-- **`√SWAP` is a square root of the swap operation.** Squaring `√SWAP = heisenbergEvolution (π/2)`
gives `heisenbergEvolution π = exp(−iπ S⃗₁·S⃗₂)`, the swap-with-phase of Part 1 — because running
the exchange interaction for `π/2` twice is running it for `π` (`exp` additivity). -/
theorem sqrtSwapHeis_mul_self :
    sqrtSwapHeis * sqrtSwapHeis = heisenbergEvolution Real.pi := by
  simp only [sqrtSwapHeis, heisenbergEvolution]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
  congr 2
  push_cast; ring

end AxQM.Concrete
