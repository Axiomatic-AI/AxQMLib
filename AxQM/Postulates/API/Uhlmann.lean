/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.PartialTrace
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.Purification

/-!
# AxQM.Postulates.API — the purification bridge for Uhlmann's theorem

The bridge connecting the **physics** notion of a purification — a `PureState`
of a composite system `S ⊗ T` whose left marginal (`State.reducedLeft`, tracing out the ancilla
`T`) is a given state `ρ` — to the **abstract** predicate `TensorProduct.IsPurification`
over the density operator `ρ.op` and the vector `ψ.vec`.

This is the bridge Nielsen–Chuang Theorem 9.4 (Uhlmann's theorem) needs to translate its
operator-level core (`TensorProduct.isGreatest_norm_inner_of_isPurification`) into a statement
about physical purifications.

## Main statements

* `PureState.reducedLeft_toState_eq_iff_isPurification` — a pure state `ψ` of `S ⊗ T` purifies
  `ρ : State S` (its left marginal is `ρ`) iff `ψ.vec` is an abstract `IsPurification` of `ρ.op`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Physics purification ↔ abstract purification.** A pure state `ψ` of the composite system
`S ⊗ T` is a purification of `ρ : State S` — meaning its left marginal `ψ.toState.reducedLeft`
(the partial trace over the ancilla `T` of the rank-one projector `|ψ⟩⟨ψ|`) equals `ρ` — exactly
when its vector `ψ.vec` is an abstract `TensorProduct.IsPurification` of the density operator
`ρ.op`.

Both sides trace out the right factor at `stdOrthonormalBasis ℂ T.space`, so once `reducedLeft`
and `toState` are unfolded (`State.reducedLeft_op`, `PureState.toState_op`) the two conditions are
the same partial-trace equation, related only by the finite-dimensional `LinearMap ↔
ContinuousLinearMap` round-trip (`ContinuousLinearMap.toLinearMap_toContinuousLinearMap` /
`LinearMap.coe_toContinuousLinearMap`). It is the physical reading of
`TensorProduct.isPurification_iff_matricize_comp_adjoint`, feeding Uhlmann's theorem. -/
theorem PureState.reducedLeft_toState_eq_iff_isPurification
    (ψ : PureState (S ⊗ T)) (ρ : State S) :
    ψ.toState.reducedLeft = ρ ↔ TensorProduct.IsPurification ρ.op ψ.vec := by
  constructor
  · intro h
    rw [← congrArg State.op h, State.reducedLeft_op, PureState.toState_op]
    exact (LinearMap.coe_toContinuousLinearMap _).symm
  · intro h
    apply State.ext
    rw [State.reducedLeft_op, PureState.toState_op]
    exact h ▸ ContinuousLinearMap.toLinearMap_toContinuousLinearMap ρ.op

end AxQM
