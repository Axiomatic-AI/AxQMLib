/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import ToMathlib.Analysis.InnerProductSpace.DensitySubunital

/-!
# The distinguishability bound for a measurement

For a measurement `m` on a system `T` and *any* assignment `ρ : ι → State T` of a state to each
outcome, the total probability of "each outcome correctly reporting its own state",

`∑ᵢ tr(Eᵢ ρᵢ)  ≤  dim T`,

is bounded by the Hilbert-space dimension `dim T = finrank ℂ T.space`, independently of how many
outcomes there are. This is the elementary **distinguishability bound** (a.k.a. the dimension bound
on a POVM), the operator fact behind the converse — the "no more than `dim` reliably distinguishable
states" limit — of Nielsen & Chuang's classical-communication capacity theorems (§12.2/§12.3): it
is what forces the number of reliably decodable codewords, and hence the achievable rate, to be
bounded.

## Proof

Two facts. First, for a POVM effect `E ≥ 0` and a density operator `ρ` the Born probability
`tr(E ρ)` never exceeds `tr(E)` itself (`ContinuousLinearMap.IsDensityOp.re_trace_comp_le`, the
general operator fact in the `ToMathlib` density API): the gap is `tr(E (1 − ρ)) ≥ 0`, positive
because `1 − ρ ≥ 0` (a density operator is subunital, `ContinuousLinearMap.IsDensityOp.le_one`) and
`E ≥ 0`. Second, summing over all outcomes and pulling the trace out of the sum,
`∑ᵢ tr(Eᵢ) = tr(∑ᵢ Eᵢ) = tr(1) = dim T` by the POVM completeness relation (`POVM.sum_eq_one`) and
`LinearMap.trace_one`.

## Supporting facts

The bound is stated in terms of the Born probability `Measurement.bornProb`. Its supporting operator
facts are general mathematics and are in the density-operator API
(`ToMathlib/Analysis/InnerProductSpace/DensitySubunital.lean`,
`ContinuousLinearMap.IsDensityOp.le_one` / `.re_trace_comp_le`).

## Main results

* `AxQM.Measurement.sum_bornProb_self_le_finrank` — the distinguishability bound
  `∑ᵢ bornProb ρᵢ i ≤ dim T`.
-/

open ContinuousLinearMap InnerProductSpace
open scoped BigOperators

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {T : QSystem}

/-- **The distinguishability bound.** For a measurement `m` on the system `T` and any assignment
`ρ : ι → State T` of a state to each outcome, the total Born probability of every outcome correctly
reporting *its own* state is at most the dimension of `T`:

`∑ᵢ bornProb (ρᵢ) i  ≤  dim T`.

Each term `bornProb (ρᵢ) i = re tr(Eᵢ ρᵢ) ≤ re tr(Eᵢ)`
(`ContinuousLinearMap.IsDensityOp.re_trace_comp_le`, as `ρᵢ` is a density operator and the effect
`Eᵢ = Mᵢ† Mᵢ` is positive), and summing,
`∑ᵢ re tr(Eᵢ) = re tr(∑ᵢ Eᵢ) = re tr(1) = dim T` by POVM completeness. Independent of the number of
outcomes, this is the operator input to the converse of the classical-communication capacity
theorems (N&C §12.2/§12.3). -/
theorem Measurement.sum_bornProb_self_le_finrank (m : Measurement ι T) (ρ : ι → State T) :
    ∑ i, m.bornProb (ρ i) i ≤ (Module.finrank ℂ T.space : ℝ) := by
  calc ∑ i, m.bornProb (ρ i) i
      = ∑ i, RCLike.re (LinearMap.trace ℂ T.space
          ((m.toPOVM.elements i).comp (ρ i).op : T.space →ₗ[ℂ] T.space)) := by
        simp only [Measurement.bornProb, POVM.toPMF_eq]
    _ ≤ ∑ i, RCLike.re (LinearMap.trace ℂ T.space
          (m.toPOVM.elements i : T.space →ₗ[ℂ] T.space)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact ContinuousLinearMap.IsDensityOp.re_trace_comp_le
          ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (m.toPOVM.isPositive i))
          (ρ i).isDensity
    _ = RCLike.re (LinearMap.trace ℂ T.space
          (↑(∑ i, m.toPOVM.elements i) : T.space →ₗ[ℂ] T.space)) := by
        rw [ContinuousLinearMap.toLinearMap_sum, map_sum, RCLike.re_sum]
    _ = RCLike.re (LinearMap.trace ℂ T.space (1 : T.space →ₗ[ℂ] T.space)) := by
        rw [m.toPOVM.sum_eq_one, ContinuousLinearMap.toLinearMap_one]
    _ = (Module.finrank ℂ T.space : ℝ) := by
        rw [LinearMap.trace_one]; simp

end AxQM
