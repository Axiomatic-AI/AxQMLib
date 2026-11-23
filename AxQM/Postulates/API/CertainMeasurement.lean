/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement

/-!
# The certain-outcome measurement

The **certain-outcome measurement** `certainMeasurement i₀` on a system `T` with outcome set `ι`:
the measurement whose operators are `M_{i₀} = 1` (the identity) and `Mⱼ = 0` for every other
outcome `j ≠ i₀`. It is a genuine `Measurement` (its completeness relation `∑ⱼ Mⱼ† Mⱼ = 1` holds
because only the `i₀` term survives, contributing `1† 1 = 1`), and measuring *any* state returns the
fixed outcome `i₀` with probability `1`.

It is the quantum counterpart of a classical decision rule that always announces the same value —
the building block for a trivial zero-error code (used, e.g., to witness that rate `0` is an
achievable communication rate over any channel, `AxQM.isProductStateAchievableRate_zero`).

Compare the other `Measurement` constructions (`Measurement.ofOrthonormalBasis`,
`Measurement.ofOrthonormalBasisFiber`). The Born-rule consequences
(`certainMeasurement_bornProb_self`, `certainMeasurement_bornProb_of_ne`) are stated with
`Measurement.bornProb`.

## Main definitions and results

* `AxQM.certainMeasurement` — the certain-outcome measurement with fixed outcome `i₀`.
* `AxQM.certainMeasurement_bornProb_self` — it returns `i₀` with probability `1`.
* `AxQM.certainMeasurement_bornProb_of_ne` — every other outcome has probability `0`.
-/

open ContinuousLinearMap InnerProductSpace
open scoped BigOperators

noncomputable section

namespace AxQM

/-- The **certain-outcome measurement** with fixed outcome `i₀`: the POVM `{Mⱼ}` with measurement
operator `M_{i₀} = 1` (the identity) and `Mⱼ = 0` for every other outcome `j ≠ i₀`. Completeness
`∑ⱼ Mⱼ† Mⱼ = 1` holds because only the `i₀` term survives, contributing `1† 1 = 1`. Measuring any
state returns the outcome `i₀` with probability `1` (`certainMeasurement_bornProb_self`); it is the
quantum counterpart of a decoder that always announces the same message. -/
def certainMeasurement {ι : Type*} [Fintype ι] [DecidableEq ι] {T : QSystem} (i₀ : ι) :
    Measurement ι T where
  op := fun j => if j = i₀ then 1 else 0
  complete := by
    rw [Finset.sum_eq_single i₀]
    · rw [ite_eq_left rfl, ← ContinuousLinearMap.star_eq_adjoint, star_one,
        ← ContinuousLinearMap.mul_def, one_mul]
    · intro j _ hj; rw [ite_eq_right hj]; simp
    · intro h; exact absurd (Finset.mem_univ i₀) h

@[simp]
theorem certainMeasurement_op {ι : Type*} [Fintype ι] [DecidableEq ι] {T : QSystem} (i₀ j : ι) :
    (certainMeasurement (T := T) i₀).op j = if j = i₀ then 1 else 0 := rfl

/-- The certain-outcome measurement assigns probability `0` to any outcome `j ≠ i₀` (its POVM effect
`Mⱼ† Mⱼ = 0`). -/
theorem certainMeasurement_bornProb_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι] {T : QSystem}
    (i₀ : ι) (ρ : State T) (j : ι) (hj : j ≠ i₀) : (certainMeasurement i₀).bornProb ρ j = 0 := by
  rw [Measurement.bornProb, POVM.toPMF_eq, Measurement.toPOVM_elements, certainMeasurement_op,
    ite_eq_right hj]
  simp

/-- The certain-outcome measurement returns its fixed outcome `i₀` with probability `1` on every
state: the other outcomes have probability `0` (`certainMeasurement_bornProb_of_ne`) and the Born
probabilities sum to `1`. -/
theorem certainMeasurement_bornProb_self {ι : Type*} [Fintype ι] [DecidableEq ι] {T : QSystem}
    (i₀ : ι) (ρ : State T) : (certainMeasurement i₀).bornProb ρ i₀ = 1 := by
  have hsum := (certainMeasurement (T := T) i₀).sum_bornProb_eq_one ρ
  rw [Finset.sum_eq_single i₀ (fun j _ hj => certainMeasurement_bornProb_of_ne i₀ ρ j hj)
    (fun h => absurd (Finset.mem_univ i₀) h)] at hsum
  exact hsum

end AxQM
