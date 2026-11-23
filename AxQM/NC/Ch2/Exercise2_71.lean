/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Purity

/-!
# Nielsen & Chuang, Exercise 2.71 (criterion to decide if a state is mixed or pure)

Show tr(rho^2)<=1 with equality iff rho is a pure state.

The **purity** `tr(ρ²)` (§2.4.2) measures how mixed a state is: it is largest, and equal to `1`,
exactly for the pure states, and strictly below `1` for genuinely mixed states. This is the
standard test for purity of an unknown density operator.

* `State.purity_le_one` — `tr(ρ²) ≤ 1` for every state.
* `State.purity_eq_one_iff_isPure` — `tr(ρ²) = 1` if and only if `ρ` is pure.

Both reduce to the general density-operator facts in
`ToMathlib.Analysis.InnerProductSpace.IdempotentDensityOp`
(`re_trace_mul_self_le_one`, `re_trace_mul_self_eq_one_iff_exists_rankOne`), which run the spectral
argument: with eigenvalues `λᵢ` satisfying `0 ≤ λᵢ ≤ 1` and `∑ λᵢ = 1`, one has
`tr(ρ²) = ∑ λᵢ² ≤ ∑ λᵢ = 1`, with equality iff each `λᵢ ∈ {0, 1}` iff `ρ` is a rank-one projector.
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 2.71 (the bound).** The purity of any state is at most one:
`tr(ρ²) ≤ 1`. Reduces to `IsDensityOp.re_trace_mul_self_le_one`, i.e. `∑ λᵢ² ≤ ∑ λᵢ = 1` from
`0 ≤ λᵢ ≤ 1`. -/
theorem State.purity_le_one (ρ : State S) : ρ.purity ≤ 1 :=
  ContinuousLinearMap.IsDensityOp.re_trace_mul_self_le_one ρ.isDensity

/-- **Nielsen & Chuang, Exercise 2.71 (the equality case).** A state has purity exactly one iff it
is pure: `tr(ρ²) = 1 ↔ ρ = |ψ⟩⟨ψ|` for some pure state `ψ`. Combines the characterisation
`State.isPure_iff_exists_rankOne` with the Mathlib pure criterion
`IsDensityOp.re_trace_mul_self_eq_one_iff_exists_rankOne`. -/
theorem State.purity_eq_one_iff_isPure (ρ : State S) : ρ.purity = 1 ↔ ρ.IsPure := by
  have : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  rw [State.isPure_iff_exists_rankOne]
  exact ContinuousLinearMap.IsDensityOp.re_trace_mul_self_eq_one_iff_exists_rankOne ρ.isDensity

end AxQM
