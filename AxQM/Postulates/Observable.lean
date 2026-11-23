/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.RankOneTrace
import ToMathlib.Analysis.InnerProductSpace.Spectrum

/-!
# AxQM — Postulate 2: observables

An **observable** is a bundled self-adjoint operator on a system `S`. By the spectral theorem it
has an orthonormal eigenbasis with real eigenvalues — its possible measurement values.

This file also defines the **expectation value** `⟪A⟫` for density operators
(`State.expectation`) and for pure states (`PureState.expectation`). The two agree on pure
states (`expectation_toState`).

`QSystem` bundles a finite-dimensional complex Hilbert space, so completeness (for
the adjoint/star) and finite-dimensionality (for the spectral theorem) derive — no
per-section instance bookkeeping.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Postulate 2 (observable).** An **observable** on the system `S` is a
self-adjoint operator; its real spectrum is the set of possible measurement values. -/
structure Observable (S : QSystem) where
  /-- The underlying operator. -/
  op : S →L[ℂ] S
  /-- The operator is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint op

variable {S : QSystem}

namespace Observable

/-- An observable, as a linear map, is symmetric — the bridge to the spectral
theorem. -/
theorem isSymmetric (A : Observable S) : A.op.toLinearMap.IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp A.selfAdjoint

end Observable

/-! ## Expectation values -/

namespace PureState

/-- The **expectation value** `⟪A⟫_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the pure
state `ψ`. Real because `A` is self-adjoint. -/
def expectation (ψ : PureState S) (A : Observable S) : ℝ := (⟪ψ.vec, A.op ψ.vec⟫_ℂ).re

end PureState

namespace State

/-- The **expectation value** `⟪A⟫_ρ = Tr(ρ A)` of an observable `A` in the state
`ρ`. Real because `ρ`, `A` are self-adjoint. -/
def expectation (ρ : State S) (A : Observable S) : ℝ :=
  (LinearMap.trace ℂ S ((ρ.op ∘L A.op : S →L[ℂ] S) : S →ₗ[ℂ] S)).re

end State

/-- **Spectral theorem for observables.** Every observable `A` has an orthonormal
eigenbasis `b` with **real** eigenvalues `lam`: `A (bᵢ) = lamᵢ • bᵢ`. -/
theorem Observable.exists_eigenbasis (A : Observable S) {n : ℕ}
    (hn : Module.finrank ℂ S.space = n) :
    ∃ (b : OrthonormalBasis (Fin n) ℂ S.space) (lam : Fin n → ℝ),
      ∀ i, A.op (b i) = (lam i : ℂ) • b i := by
  have hsym := A.isSymmetric
  exact ⟨hsym.eigenvectorBasis hn, hsym.eigenvalues hn, fun i ↦ hsym.apply_eigenvectorBasis hn i⟩

/-- **The two state tracks agree on pure states.** The density-operator expectation
`Tr(|ψ⟩⟨ψ| A)` equals the pure-state expectation `⟪ψ, A ψ⟫`. This is the bridge
that makes the `State`/`PureState` descriptions of a system coherent. -/
theorem expectation_toState (ψ : PureState S) (A : Observable S) :
    ψ.toState.expectation A = ψ.expectation A := by
  simp only [State.expectation, PureState.expectation, PureState.toState_op,
    InnerProductSpace.trace_rankOne_self_comp]

end AxQM
