/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.GroverSearchIterations
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.ProjectiveMeasurement

/-!
# AxQM.Postulates.API — measuring the Grover search state (Nielsen & Chuang, Exercise 6.4)

The **physical** step of the quantum search algorithm: after `R` Grover iterations one *measures*
the register in the computational basis and reads off a solution. This file models that step with
a genuine `PureState`, a genuine projective `Measurement`, and the Born rule
(`Measurement.bornProb`), building on the analysis of Exercise 6.4 over the
`|α⟩, |β⟩` plane (`AxQM/Concrete/GroverSearchIterations.lean`: N&C Eq. 6.12 and the success
bound). The statement of Exercise 6.4 is in `AxQM/NC/Ch6/Exercise6_4.lean`.

## Contents

* `groverFinalState θ R` — the state **after `R` Grover iterations**, `Gᴿ|ψ⟩`, as a genuine
  `PureState` of the qubit `span{|α⟩,|β⟩}`. Its vector is literally the algorithm's output
  `(groverIteration θ)^R *ᵥ groverState θ` promoted into the Hilbert space; it is a unit
  vector because N&C Eq. 6.12 identifies it with the plane state `cos φ |α⟩ + sin φ |β⟩` at angle
  `φ = (2R+1)θ/2`, and `cos²φ + sin²φ = 1`.
* `groverSolutionMeasurement` — the two-outcome projective measurement of the reduced qubit in the
  `{|α⟩, |β⟩}` basis (`Measurement.ofOrthonormalBasis`). Outcome `0` is `|α⟩` (a *non*-solution),
  outcome `1` is `|β⟩` (a *solution*): it is the coarse-graining "did the computational-basis
  measurement return a solution?" of N&C's full `n`-qubit measurement, since `|β⟩` is the unit
  vector spanning exactly the solution outcomes.
* `bornProb_groverSolutionMeasurement_solution` — **the key computation**: the Born probability of
  the solution outcome for `Gᴿ|ψ⟩` is `sin²((2R+1)θ/2)`, exactly the squared `|β⟩`-amplitude that
  N&C Eq. 6.12 predicts.
-/

open scoped InnerProductSpace
open Matrix

noncomputable section

namespace AxQM

open Concrete

/-- **The Grover search state after `R` iterations**, `Gᴿ|ψ⟩`, as a `PureState` of the reduced qubit
`span{|α⟩, |β⟩}`. Its underlying vector is the algorithm's actual output — the starting state
`|ψ⟩ = groverState θ` acted on by the `R`-th power of the Grover iteration matrix — promoted
into the qubit space `EuclideanSpace ℂ (Fin 2)` via `WithLp.toLp`. It is a unit vector: N&C
Eq. 6.12 (`groverIteration_pow_mulVec_groverState`) identifies it with the plane state at angle
`(2R+1)θ/2`, whose norm is `√(cos² + sin²) = 1`. -/
def groverFinalState (θ : ℝ) (R : ℕ) : PureState qubit where
  vec := WithLp.toLp 2 ((groverIteration θ) ^ R *ᵥ groverState θ)
  normalized := by
    rw [groverIteration_pow_mulVec_groverState]
    change ‖(WithLp.toLp 2 (planeState ((2 * (R : ℝ) + 1) * θ / 2)) :
        EuclideanSpace ℂ (Fin 2))‖ = 1
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [planeState_apply_zero, planeState_apply_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have hpyth : Real.cos ((2 * (R : ℝ) + 1) * θ / 2) ^ 2
        + Real.sin ((2 * (R : ℝ) + 1) * θ / 2) ^ 2 = 1 :=
      by linear_combination Real.sin_sq_add_cos_sq ((2 * (R : ℝ) + 1) * θ / 2)
    rw [hpyth, Real.sqrt_one]

@[simp]
theorem groverFinalState_vec (θ : ℝ) (R : ℕ) :
    (groverFinalState θ R).vec = WithLp.toLp 2 ((groverIteration θ) ^ R *ᵥ groverState θ) := rfl

/-- The **`|β⟩` (solution) amplitude** of the state after `R` iterations is `sin((2R+1)θ/2)`: the
`1`-coordinate of `Gᴿ|ψ⟩`, read off from N&C Eq. 6.12. -/
theorem groverFinalState_ofLp_one (θ : ℝ) (R : ℕ) :
    (groverFinalState θ R).vec.ofLp 1 = (Real.sin ((2 * (R : ℝ) + 1) * θ / 2) : ℂ) := by
  rw [groverFinalState_vec, WithLp.ofLp_toLp, groverIteration_pow_mulVec_groverState,
    planeState_apply_one]

/-- **The projective measurement of the reduced qubit in the `{|α⟩, |β⟩}` basis**
(`Measurement.ofOrthonormalBasis` of the computational basis of `EuclideanSpace ℂ (Fin 2)`). Outcome
`0` is `|α⟩` — a non-solution — and outcome `1` is `|β⟩` — a solution. This is the coarse-graining
"did we measure a solution?" of the full `n`-qubit computational-basis measurement of the quantum
search algorithm (N&C's step 4), since `|β⟩` is the unit vector spanning exactly the solution
outcomes. -/
def groverSolutionMeasurement : Measurement (Fin 2) qubit :=
  Measurement.ofOrthonormalBasis (EuclideanSpace.basisFun (Fin 2) ℂ)

/-- **Nielsen & Chuang, Exercise 6.4 — the Born probability of finding a solution.** Measuring the
state `Gᴿ|ψ⟩` (after `R` Grover iterations) in the computational basis returns the solution outcome
`|β⟩` with probability `sin²((2R+1)θ/2)` — exactly the squared `|β⟩`-amplitude of N&C Eq. 6.12. This
is the physical (Born-rule) content of the quantum search algorithm's final measurement step,
grounded in `Measurement`. -/
theorem bornProb_groverSolutionMeasurement_solution (θ : ℝ) (R : ℕ) :
    groverSolutionMeasurement.bornProb (groverFinalState θ R).toState 1
      = Real.sin ((2 * (R : ℝ) + 1) * θ / 2) ^ 2 := by
  let vecGen : EuclideanSpace ℂ (Fin 2) := (groverFinalState θ R).vec
  have hbp := Measurement.bornProb_ofOrthonormalBasis_toState
    (EuclideanSpace.basisFun (Fin 2) ℂ) (groverFinalState θ R) 1
  rw [groverSolutionMeasurement, hbp]
  change ‖(inner ℂ (EuclideanSpace.basisFun (Fin 2) ℂ 1) vecGen : ℂ)‖ ^ 2 = _
  rw [EuclideanSpace.basisFun_inner]
  change ‖vecGen.ofLp 1‖ ^ 2 = _
  rw [groverFinalState_ofLp_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end AxQM
