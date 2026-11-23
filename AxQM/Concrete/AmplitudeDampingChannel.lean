/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QubitBasisOperators
import ToMathlib.Analysis.InnerProductSpace.AdjointAntilinear
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete: the amplitude-damping channel on an abstract qubit (N&C §8.3.5)

This file defines, at the level of raw operators on an arbitrary two-dimensional complex inner
product space (a qubit) with a chosen computational orthonormal basis
`b : OrthonormalBasis (Fin 2) ℂ H`, the **amplitude-damping channel** of Nielsen & Chuang,
*Quantum Computation and Quantum Information*, §8.3.5 (eqs. 8.107,
8.108). With damping parameter `γ` the channel has the two operation elements

`E₀ = |0⟩⟨0| + √(1-γ) |1⟩⟨1| = diag(1, √(1-γ))`,   `E₁ = √γ |0⟩⟨1|`   (N&C eq. 8.108),

and acts by `E_AD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (N&C eq. 8.107). `E₀` leaves `|0⟩` unchanged and shrinks
the `|1⟩` amplitude (no photon was lost); `E₁` maps `|1⟩` to `|0⟩` (a quantum of energy was lost to
the environment). `γ` is the probability of losing the excitation.

This is the reusable *definition* of "the amplitude-damping quantum operation" that Nielsen &
Chuang's amplitude-damping cluster refers to (Exercises 8.20–8.25, 10.13, …): the circuit model
(Exercise 8.20, `Concrete/AmplitudeDampingCircuit.lean`) is shown to *equal* this channel, and later
items build on it. The concrete `Matrix (Fin 2)` version parametrised by a decay rate and time
lives in `Concrete/AmplitudeDampingMasterEquation.lean` (Problem 8.1); this abstract-qubit,
`γ`-parametrised form is the one the operator-sum / circuit development uses — the `LinearMap`
category the
partial-trace / operator-sum infrastructure (`ToMathlib.Analysis.InnerProductSpace.OperatorSum`)
works in.

The atomic lowering operator `σ₋ = |0⟩⟨1|` (`Concrete.qubitLower`), its raising adjoint
`σ₊ = |1⟩⟨0|`, and the identity `σ₊ σ₋ = P₁` are the shared computational-basis ladder operators of
`Concrete/QubitBasisOperators.lean` (reused here, not redefined).

## Contents

* `ampDampKrausZero b γ`, `ampDampKrausOne b γ` — the operation elements `E₀`, `E₁`
  (eq. 8.108), with `adjoint_ampDampKrausZero` (`E₀` is self-adjoint).
* `ampDampKrausZero_apply_basisZero`/`_basisOne`, `ampDampKrausOne_apply_basisZero`/`_basisOne` —
  the action of `E₀`, `E₁` on the computational basis (`E₀|0⟩=|0⟩`, `E₀|1⟩=√(1-γ)|1⟩`, `E₁|0⟩=0`,
  `E₁|1⟩=√γ|0⟩`), the shared reusable `@[simp]` apply lemmas for the amplitude-damping cluster.
* `ampDampChannel b γ ρ` — the amplitude-damping channel `E_AD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†`
  (N&C eq. 8.107).
* `ampDampKraus_completeness` — the completeness / trace-preservation relation `E₀† E₀ + E₁† E₁ = I`
  (for `0 ≤ γ ≤ 1`), certifying `E_AD` is a genuine (trace-preserving) quantum operation.

## Related items

The operation elements are bare `LinearMap`s on an inner product space, built from an
`OrthonormalBasis` and `InnerProductSpace.rankOne`. Compare the operator-sum channels of
Exercises 8.4 (`AxQM/Concrete/ControlledFlipOperatorSum.lean`) and 8.5
(`AxQM/Concrete/SpinFlipOperatorSum.lean`).

## Design

The qubit is an *arbitrary* two-dimensional complex inner product space `H` with a chosen
computational basis `b`, so the channel holds for every qubit rather than a fixed `ℂ²`; the
operation elements reuse the abstract-qubit projectors `Concrete.qubitProj` and lowering operator
`Concrete.qubitLower` of `Concrete/QubitBasisOperators.lean`. The two nonlinear inputs to
completeness — `(√(1-γ))² = 1-γ`
and `(√γ)² = γ` — need `0 ≤ γ ≤ 1`, exactly N&C's physical range for the damping probability.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **first operation element** `E₀ = |0⟩⟨0| + √(1-γ) |1⟩⟨1| = diag(1, √(1-γ))` of the
amplitude-damping channel (N&C eq. 8.108): it leaves `|0⟩` unchanged and shrinks the `|1⟩` amplitude
by `√(1-γ)` (no quantum of energy was lost). -/
noncomputable def ampDampKrausZero (γ : ℝ) : H →ₗ[ℂ] H :=
  qubitProj b 0 + (Real.sqrt (1 - γ) : ℂ) • qubitProj b 1

/-- The **second operation element** `E₁ = √γ |0⟩⟨1| = √γ σ₋` of the amplitude-damping channel
(N&C eq. 8.108): it maps `|1⟩` to `|0⟩` with amplitude `√γ` (a quantum of energy was lost to the
environment). -/
noncomputable def ampDampKrausOne (γ : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt γ : ℂ) • qubitLower b

-- The four single-qubit **operation-element apply-on-basis** lemmas below are the building blocks
-- of the amplitude-damping exercises (Exercises 8.22, 8.23, …).

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `E₀` fixes the ground state: `E₀ |0⟩ = |0⟩` (no quantum of energy to lose). -/
@[simp] theorem ampDampKrausZero_apply_basisZero (γ : ℝ) : ampDampKrausZero b γ (b 0) = b 0 := by
  simp only [ampDampKrausZero, LinearMap.add_apply, LinearMap.smul_apply, qubitProj_apply,
    b.inner_eq_ite, Fin.isValue, ↓reduceIte, one_smul, Fin.reduceEq, zero_smul, smul_zero, add_zero]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `E₀` shrinks the excited-state amplitude: `E₀ |1⟩ = √(1-γ) |1⟩`. -/
@[simp] theorem ampDampKrausZero_apply_basisOne (γ : ℝ) :
    ampDampKrausZero b γ (b 1) = (Real.sqrt (1 - γ) : ℂ) • b 1 := by
  simp only [ampDampKrausZero, LinearMap.add_apply, LinearMap.smul_apply, qubitProj_apply,
    b.inner_eq_ite, Fin.isValue, ↓reduceIte, one_smul, Fin.reduceEq, zero_smul, zero_add]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `E₁` annihilates the ground state: `E₁ |0⟩ = 0` (nothing below `|0⟩` to decay to). -/
@[simp] theorem ampDampKrausOne_apply_basisZero (γ : ℝ) : ampDampKrausOne b γ (b 0) = 0 := by
  simp only [ampDampKrausOne, LinearMap.smul_apply, qubitLower_apply_zero, smul_zero]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `E₁` lowers the excited state to the ground state: `E₁ |1⟩ = √γ |0⟩` (energy lost to the
environment). -/
@[simp] theorem ampDampKrausOne_apply_basisOne (γ : ℝ) :
    ampDampKrausOne b γ (b 1) = (Real.sqrt γ : ℂ) • b 0 := by
  simp only [ampDampKrausOne, LinearMap.smul_apply, qubitLower_apply_one]

/-- `E₀` is self-adjoint: `E₀† = E₀`. It is a real-diagonal operator `diag(1, √(1-γ))`, a real
combination of the self-adjoint projectors `P₀`, `P₁` (`√(1-γ)` is conjugation-fixed). -/
@[simp] theorem adjoint_ampDampKrausZero (γ : ℝ) :
    LinearMap.adjoint (ampDampKrausZero b γ) = ampDampKrausZero b γ := by
  rw [ampDampKrausZero, map_add, LinearMap.adjoint_smul, adjoint_qubitProj, adjoint_qubitProj]
  simp only [RCLike.star_def, Complex.conj_ofReal]

/-- The **amplitude-damping channel** `E_AD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (N&C eq. 8.107): the quantum
operation with operation elements `E₀ = diag(1, √(1-γ))` and `E₁ = √γ |0⟩⟨1|`. -/
noncomputable def ampDampChannel (γ : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ampDampKrausZero b γ ∘ₗ ρ ∘ₗ LinearMap.adjoint (ampDampKrausZero b γ)
    + ampDampKrausOne b γ ∘ₗ ρ ∘ₗ LinearMap.adjoint (ampDampKrausOne b γ)

/-- **Completeness / trace preservation** (N&C eq. 8.114 context): the operation elements satisfy
`E₀† E₀ + E₁† E₁ = I`, so the amplitude-damping channel is trace preserving — a genuine quantum
operation. For `0 ≤ γ ≤ 1`, `E₀† E₀ = P₀ + (1-γ) P₁` (`E₀` self-adjoint, `(√(1-γ))² = 1-γ`, the
projector algebra) and `E₁† E₁ = γ P₁` (`σ₊ σ₋ = P₁`, `(√γ)² = γ`), summing to `P₀ + P₁ = I`. -/
theorem ampDampKraus_completeness (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    LinearMap.adjoint (ampDampKrausZero b γ) ∘ₗ ampDampKrausZero b γ
      + LinearMap.adjoint (ampDampKrausOne b γ) ∘ₗ ampDampKrausOne b γ = LinearMap.id := by
  have hsq1 : (Real.sqrt (1 - γ) : ℂ) * (Real.sqrt (1 - γ) : ℂ) = ((1 - γ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsqγ : (Real.sqrt γ : ℂ) * (Real.sqrt γ : ℂ) = (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hγ0]
  -- `E₀† E₀ = P₀ + (1-γ) P₁`.
  have hE0 : LinearMap.adjoint (ampDampKrausZero b γ) ∘ₗ ampDampKrausZero b γ
      = qubitProj b 0 + ((1 - γ : ℝ) : ℂ) • qubitProj b 1 := by
    rw [adjoint_ampDampKrausZero, ampDampKrausZero]
    simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul,
      qubitProj_comp_qubitProj, Fin.isValue, Fin.reduceEq, ↓reduceIte, smul_zero, add_zero,
      zero_add, smul_smul, hsq1]
  -- `E₁† E₁ = γ P₁`.
  have hE1 : LinearMap.adjoint (ampDampKrausOne b γ) ∘ₗ ampDampKrausOne b γ
      = (γ : ℂ) • qubitProj b 1 := by
    rw [ampDampKrausOne, LinearMap.adjoint_smul, LinearMap.smul_comp, LinearMap.comp_smul,
      qubitLower_adjoint_comp_self, smul_smul, RCLike.star_def, Complex.conj_ofReal, hsqγ]
  rw [hE0, hE1, add_assoc, ← add_smul,
    show ((1 - γ : ℝ) : ℂ) + (γ : ℂ) = 1 by push_cast; ring, one_smul, sum_qubitProj]

end AxQM.Concrete

end
