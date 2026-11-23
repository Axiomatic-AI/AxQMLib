/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Concrete: amplitude damping of a general single-qubit density matrix (N&C Exercise 8.22)

This file computes the action of the
**amplitude-damping channel** `E_AD` (`Concrete/AmplitudeDampingChannel.lean`, N&C eqs. 8.107–8.108)
on an *arbitrary* single-qubit operator `ρ`, in the chosen computational basis
`b : OrthonormalBasis (Fin 2) ℂ H`, and reads off its computational-basis matrix.

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 8.22 asks: for the general
single-qubit density matrix `ρ = !![a, b; b*, c]` (eq. 8.111), show that amplitude damping gives

`E_AD(ρ) = !![1 - (1-γ)(1-a),  b √(1-γ);  b* √(1-γ),  c (1-γ)]`   (eq. 8.112).

## Contents

* `inner_ampDampChannel` — the structural identity moving the operation elements to the left of the
  inner product: `⟨x, E_AD(ρ) y⟩ = ⟨E₀ x, ρ (E₀ y)⟩ + ⟨E₁† x, ρ (E₁† y)⟩` (`E₀` self-adjoint).
* `adjoint_ampDampKrausOne_apply_basisZero/One` — the action of the raising adjoint `E₁†` on the
  computational basis (`E₁†|0⟩=√γ|1⟩`, `E₁†|1⟩=0`). (The `E₀` apply-on-basis lemmas
  `ampDampKrausZero_apply_basisZero/One` are now shared from the base module
  `Concrete/AmplitudeDampingChannel.lean`.)
* `ampDampChannel_inner_zero_zero / _zero_one / _one_zero / _one_one` — the four matrix entries of
  `E_AD(ρ)` in terms of those of `ρ` (`0 ≤ γ ≤ 1`): `a + γc`, `√(1-γ) b`, `√(1-γ) b*`, `(1-γ) c`.
* `ampDampChannel_toMatrixOrthonormal` — **the exercise, in full generality**: the
  computational-basis matrix of `E_AD(ρ)` for *any* operator `ρ`, no trace hypothesis.
* `ampDampChannel_toMatrixOrthonormal_of_trace_one` — **N&C eq. 8.112 verbatim**: for a genuine
  state (`tr ρ = a + c = 1`), the `(0,0)` entry `a + γc` is exactly N&C's `1 - (1-γ)(1-a)`.

## Related items

The computations use bare `LinearMap`s, an `OrthonormalBasis`, `inner`, and
`LinearMap.toMatrixOrthonormal`. Compare the density-matrix computations of Exercises 8.16 and 8.17
(`NonTracePreservingBlochExample`, `PauliAverage`). These are the declarations for N&C
Exercise 8.22 (`AxQM/NC/Ch8/Exercise8_22.lean`).

## Design

The channel acts on an *arbitrary* two-dimensional qubit `H` with a chosen computational basis `b`,
reusing the operation elements and self-adjointness of `Concrete/AmplitudeDampingChannel.lean`. The
matrix identity holds for **every** operator `ρ` (the channel is linear), so no
positivity/Hermiticity hypothesis is imposed; only `0 ≤ γ ≤ 1` — N&C's physical range for the
damping probability — is needed, to evaluate the squares `(√γ)² = γ` and `(√(1-γ))² = 1-γ`. The
trace-one refinement, which alone needs `a + c = 1`, is isolated in
`ampDampChannel_toMatrixOrthonormal_of_trace_one`, reproducing eq. 8.112 verbatim.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- **Structural decomposition of a matrix element of `E_AD(ρ)`.** Moving each operation element to
the left of the inner product (`E₀` self-adjoint, `E₁† = adjoint E₁`):
`⟨x, E_AD(ρ) y⟩ = ⟨E₀ x, ρ (E₀ y)⟩ + ⟨E₁† x, ρ (E₁† y)⟩`. -/
theorem inner_ampDampChannel (γ : ℝ) (ρ : H →ₗ[ℂ] H) (x y : H) :
    inner ℂ x (ampDampChannel b γ ρ y)
      = inner ℂ (ampDampKrausZero b γ x) (ρ (ampDampKrausZero b γ y))
        + inner ℂ (LinearMap.adjoint (ampDampKrausOne b γ) x)
            (ρ (LinearMap.adjoint (ampDampKrausOne b γ) y)) := by
  rw [ampDampChannel]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_right]
  rw [← LinearMap.adjoint_inner_left (ampDampKrausZero b γ)
        (ρ (LinearMap.adjoint (ampDampKrausZero b γ) y)) x,
      ← LinearMap.adjoint_inner_left (ampDampKrausOne b γ)
        (ρ (LinearMap.adjoint (ampDampKrausOne b γ) y)) x]
  simp only [adjoint_ampDampKrausZero]

-- `ampDampKrausZero_apply_basisZero` (`E₀|0⟩=|0⟩`) and `ampDampKrausZero_apply_basisOne`
-- (`E₀|1⟩=√(1-γ)|1⟩`) are the shared apply-on-basis lemmas, now in the base module
-- `Concrete/AmplitudeDampingChannel.lean` (imported above) rather than duplicated here.

/-- `E₁† |0⟩ = √γ |1⟩`. -/
@[simp] theorem adjoint_ampDampKrausOne_apply_basisZero (γ : ℝ) :
    LinearMap.adjoint (ampDampKrausOne b γ) (b 0) = (Real.sqrt γ : ℂ) • b 1 := by
  rw [ampDampKrausOne, LinearMap.adjoint_smul, adjoint_qubitLower]
  simp only [RCLike.star_def, Complex.conj_ofReal, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, b.inner_eq_ite]
  simp

/-- `E₁† |1⟩ = 0` (the raising operator annihilates the excited state on the left). -/
@[simp] theorem adjoint_ampDampKrausOne_apply_basisOne (γ : ℝ) :
    LinearMap.adjoint (ampDampKrausOne b γ) (b 1) = 0 := by
  rw [ampDampKrausOne, LinearMap.adjoint_smul, adjoint_qubitLower]
  simp only [RCLike.star_def, Complex.conj_ofReal, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, b.inner_eq_ite]
  simp

/-- **`(0,0)` entry.** `⟨0|E_AD(ρ)|0⟩ = a + γc` (the ground population gains `γc`, the fraction of
excited population `c` that relaxed to `|0⟩`). -/
theorem ampDampChannel_inner_zero_zero (γ : ℝ) (hγ0 : 0 ≤ γ) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 0) (ampDampChannel b γ ρ (b 0))
      = inner ℂ (b 0) (ρ (b 0)) + (γ : ℂ) * inner ℂ (b 1) (ρ (b 1)) := by
  have hmul : (Real.sqrt γ : ℂ) * (Real.sqrt γ : ℂ) = (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hγ0]
  rw [inner_ampDampChannel]
  simp only [ampDampKrausZero_apply_basisZero, adjoint_ampDampKrausOne_apply_basisZero, map_smul,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← mul_assoc, hmul]

/-- **`(0,1)` entry.** `⟨0|E_AD(ρ)|1⟩ = √(1-γ) b` (the coherence is damped by `√(1-γ)`). -/
theorem ampDampChannel_inner_zero_one (γ : ℝ) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 0) (ampDampChannel b γ ρ (b 1))
      = (Real.sqrt (1 - γ) : ℂ) * inner ℂ (b 0) (ρ (b 1)) := by
  rw [inner_ampDampChannel]
  simp only [ampDampKrausZero_apply_basisZero, ampDampKrausZero_apply_basisOne,
    adjoint_ampDampKrausOne_apply_basisZero, adjoint_ampDampKrausOne_apply_basisOne, map_smul,
    map_zero, inner_smul_right, inner_zero_right, add_zero]

/-- **`(1,0)` entry.** `⟨1|E_AD(ρ)|0⟩ = √(1-γ) b*` (the coherence is damped by `√(1-γ)`). -/
theorem ampDampChannel_inner_one_zero (γ : ℝ) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 1) (ampDampChannel b γ ρ (b 0))
      = (Real.sqrt (1 - γ) : ℂ) * inner ℂ (b 1) (ρ (b 0)) := by
  rw [inner_ampDampChannel]
  simp only [ampDampKrausZero_apply_basisOne, ampDampKrausZero_apply_basisZero,
    adjoint_ampDampKrausOne_apply_basisOne, adjoint_ampDampKrausOne_apply_basisZero, map_smul,
    inner_smul_left, inner_smul_right, inner_zero_left,
    Complex.conj_ofReal, mul_zero, add_zero]

/-- **`(1,1)` entry.** `⟨1|E_AD(ρ)|1⟩ = (1-γ) c` (the excited population decays by `(1-γ)`). -/
theorem ampDampChannel_inner_one_one (γ : ℝ) (hγ1 : γ ≤ 1) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 1) (ampDampChannel b γ ρ (b 1))
      = ((1 - γ : ℝ) : ℂ) * inner ℂ (b 1) (ρ (b 1)) := by
  have hmul : (Real.sqrt (1 - γ) : ℂ) * (Real.sqrt (1 - γ) : ℂ) = ((1 - γ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  rw [inner_ampDampChannel]
  simp only [ampDampKrausZero_apply_basisOne, adjoint_ampDampKrausOne_apply_basisOne, map_smul,
    map_zero, inner_smul_left, inner_smul_right, inner_zero_left,
    Complex.conj_ofReal, add_zero]
  rw [← mul_assoc, hmul]

/-- **Exercise 8.22, general form.** The computational-basis matrix of `E_AD(ρ)` for *any* operator
`ρ` with matrix `!![a, b; b*, c]` (`0 ≤ γ ≤ 1`) is
`E_AD(ρ) = !![a + γc, √(1-γ) b; √(1-γ) b*, (1-γ) c]`. No trace/positivity hypothesis is used. -/
theorem ampDampChannel_toMatrixOrthonormal (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (ρ : H →ₗ[ℂ] H) :
    LinearMap.toMatrixOrthonormal b (ampDampChannel b γ ρ)
      = !![LinearMap.toMatrixOrthonormal b ρ 0 0 + (γ : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 1,
            (Real.sqrt (1 - γ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 0 1;
           (Real.sqrt (1 - γ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 0,
            ((1 - γ : ℝ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [LinearMap.toMatrixOrthonormal_apply_apply, Matrix.of_apply, Fin.isValue]
  · exact ampDampChannel_inner_zero_zero b γ hγ0 ρ
  · exact ampDampChannel_inner_zero_one b γ ρ
  · exact ampDampChannel_inner_one_zero b γ ρ
  · exact ampDampChannel_inner_one_one b γ hγ1 ρ

/-- **Exercise 8.22, N&C eq. 8.112 verbatim.** For a genuine single-qubit *state* — matrix
`ρ = !![a, b; b*, c]` with trace `a + c = 1` — amplitude damping gives
`E_AD(ρ) = !![1 - (1-γ)(1-a),  √(1-γ) b;  √(1-γ) b*,  (1-γ) c]`. The `(0,0)` entry `a + γc`
of the general form equals N&C's `1 - (1-γ)(1-a)` because `c = 1 - a`. -/
theorem ampDampChannel_toMatrixOrthonormal_of_trace_one (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (ρ : H →ₗ[ℂ] H)
    (htr : LinearMap.toMatrixOrthonormal b ρ 0 0 + LinearMap.toMatrixOrthonormal b ρ 1 1 = 1) :
    LinearMap.toMatrixOrthonormal b (ampDampChannel b γ ρ)
      = !![1 - ((1 - γ : ℝ) : ℂ) * (1 - LinearMap.toMatrixOrthonormal b ρ 0 0),
            (Real.sqrt (1 - γ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 0 1;
           (Real.sqrt (1 - γ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 0,
            ((1 - γ : ℝ) : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 1] := by
  rw [ampDampChannel_toMatrixOrthonormal b γ hγ0 hγ1 ρ]
  have hc : LinearMap.toMatrixOrthonormal b ρ 1 1
      = 1 - LinearMap.toMatrixOrthonormal b ρ 0 0 := by linear_combination htr
  -- Only the `(0,0)` entry differs from the general form; rewrite it as a scalar identity so
  -- `push_cast` never runs over the `!![…]` vector literal (which otherwise trips a simproc).
  have h00 : LinearMap.toMatrixOrthonormal b ρ 0 0
        + (γ : ℂ) * LinearMap.toMatrixOrthonormal b ρ 1 1
      = 1 - ((1 - γ : ℝ) : ℂ) * (1 - LinearMap.toMatrixOrthonormal b ρ 0 0) := by
    rw [hc]; push_cast; ring
  rw [h00]

end AxQM.Concrete

end
