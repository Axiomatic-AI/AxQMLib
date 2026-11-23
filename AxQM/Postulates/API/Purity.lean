/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PureState
import ToMathlib.Analysis.InnerProductSpace.IdempotentDensityOp

/-!
# AxQM.Postulates.API — purity of a state

Two quantities on states, used to state N&C Exercise 2.71 (the criterion
for deciding whether a state is mixed or pure):

* `State.purity ρ` — the **purity** `tr(ρ²)` of a density operator, as a real number
  (`re tr(ρ²)`; the trace of the positive operator `ρ²` is real), defined from `State.op` and
  `LinearMap.trace`.
* `State.IsPure ρ` — the predicate "`ρ` is a pure state", i.e. `ρ = |ψ⟩⟨ψ|` for some
  `ψ : PureState S`.

The lemma `State.isPure_iff_exists_rankOne` restates `IsPure` in terms of the underlying
rank-one operator, the form in which the Mathlib density-operator API
(`ContinuousLinearMap.IsDensityOp.re_trace_mul_self_eq_one_iff_exists_rankOne`) delivers the pure
criterion. The consequences (`purity ≤ 1` and `purity = 1 ↔ IsPure`) are the Exercise 2.71
theorems, in `AxQM/NC/Ch2/Exercise2_71.lean`.
-/

noncomputable section

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- The **purity** `tr(ρ²)` of a state `ρ`, as a real number. Since `ρ` is a positive operator,
`ρ² = ρ.op * ρ.op` is positive and its trace is real; `purity` records that real trace. Equal to
`1` exactly when `ρ` is pure (see `State.purity_eq_one_iff_isPure`), and always at most `1`
(`State.purity_le_one`). -/
def State.purity (ρ : State S) : ℝ :=
  RCLike.re (LinearMap.trace ℂ S ((ρ.op * ρ.op : S →L[ℂ] S) : S →ₗ[ℂ] S))

/-- A state `ρ` **is pure** when it is the rank-one projector `|ψ⟩⟨ψ|` of some pure state `ψ`,
i.e. `ρ = ψ.toState`. -/
def State.IsPure (ρ : State S) : Prop :=
  ∃ ψ : PureState S, ρ = ψ.toState

/-- **Purity in terms of rank-one operators.** A state is pure iff its density operator is the
rank-one self-projector `|v⟩⟨v|` of some unit vector `v`. Unfolds `State.IsPure` through
`toState_op` so it can be matched against the Mathlib pure criterion. -/
theorem State.isPure_iff_exists_rankOne (ρ : State S) :
    ρ.IsPure ↔ ∃ v : S, ‖v‖ = 1 ∧ ρ.op = InnerProductSpace.rankOne ℂ v v := by
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨ψ.vec, ψ.normalized, ψ.toState_op⟩
  · rintro ⟨v, hv, hop⟩
    refine ⟨⟨v, hv⟩, State.ext ?_⟩
    rw [hop]
    exact (PureState.toState_op ⟨v, hv⟩).symm

end AxQM
