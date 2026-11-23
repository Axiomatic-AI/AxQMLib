/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.QSystem
import ToMathlib.Analysis.InnerProductSpace.Density

/-!
# AxQM — Postulate 1: state space and states

The *state* of a quantum system. States are **bundled structures**, not
predicates on raw operators: a quantity defined for states takes a `State`
or `PureState`, so its definition is grounded in the postulate by its very type.

States are indexed by a `QSystem` `S`; `S` coerces to its state space `S.space`, so the
state space appears as `S` (`op : S →L[ℂ] S`, `vec : S`).

There are two descriptions, neither primary.
* `AxQM.State S` — a **density operator** (positive, trace one): the
  general (possibly mixed) state.
* `AxQM.PureState S` — a **unit vector**: a pure state.
* `PureState.toState` — the rank-one projector `|ψ⟩⟨ψ|` relating the two.

The underlying operator and vector are `State.op` and `PureState.vec`. Because `QSystem`
bundles a finite-dimensional complex
Hilbert space, completeness and finite-dimensionality derive automatically — no
per-section instance bookkeeping.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Postulate 1 (state).** A quantum **state** of the system `S` is a density
operator: a positive operator of trace one. Subsumes pure and mixed states alike.
Built on `ContinuousLinearMap.IsDensityOp` from `ToMathlib`. -/
@[ext]
structure State (S : QSystem) where
  /-- The underlying density operator. -/
  op : S →L[ℂ] S
  /-- The operator is a density operator: positive with trace one. -/
  isDensity : op.IsDensityOp

/-- **Postulate 1 (pure state).** A **pure state** of the system `S` is a unit
vector, determined up to a global phase. -/
@[ext]
structure PureState (S : QSystem) where
  /-- The underlying unit vector. -/
  vec : S
  /-- The vector is normalized: `‖vec‖ = 1`. -/
  normalized : ‖vec‖ = 1

variable {S : QSystem}

namespace State

/-- A state has trace one. -/
theorem trace_op_eq_one (ρ : State S) :
    LinearMap.trace ℂ S (ρ.op : S →ₗ[ℂ] S) = 1 :=
  ρ.isDensity.trace_eq_one

/-- A state's operator is positive. -/
theorem isPositive_op (ρ : State S) : ρ.op.IsPositive := ρ.isDensity.isPositive

/-- **A state's operator is nonzero**: its trace is `1 ≠ 0`. -/
theorem op_ne_zero (ρ : State S) : (ρ.op : S →ₗ[ℂ] S) ≠ 0 := fun h ↦ by
  have := ρ.trace_op_eq_one
  rw [h, map_zero] at this
  exact one_ne_zero this.symm

/-- **A state forces a nontrivial space**: the existence of a `State S` implies
`Nontrivial S.space`. A state's operator has trace `1 ≠ 0`, but on a subsingleton space
every operator is `0` (hence trace `0`). Lets bounds whose Mathlib lever needs
`[Nontrivial]` discharge the hypothesis from the state itself rather than assuming it. -/
theorem nontrivial_space (ρ : State S) : Nontrivial S.space :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦
    absurd ρ.trace_op_eq_one (by simp [Subsingleton.elim (ρ.op : S →ₗ[ℂ] S) 0])

end State

namespace PureState

/-- The state `|ψ⟩⟨ψ|` of a pure state `ψ` — the rank-one projector. This
relates pure states to density operators. -/
def toState (ψ : PureState S) : State S where
  op := InnerProductSpace.rankOne ℂ ψ.vec ψ.vec
  isDensity := ContinuousLinearMap.isDensityOp_rankOne_self ψ.normalized

@[simp]
theorem toState_op (ψ : PureState S) :
    ψ.toState.op = InnerProductSpace.rankOne ℂ ψ.vec ψ.vec := rfl

/-- A pure state coerces to its density-operator state `|ψ⟩⟨ψ|` — the ergonomic
direction of the relation between pure states and density operators. -/
instance : Coe (PureState S) (State S) := ⟨toState⟩

end PureState

end AxQM
