/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.QSystem
import AxQM.Postulates.StateSpace
import AxQM.Postulates.Observable
import AxQM.Postulates.Measurement
import AxQM.Postulates.Evolution

/-!
# AxQM — system isomorphisms (`S ≃ₛ T`)

A **system isomorphism** `S ≃ₛ T` is an inner-product isometry of the state spaces,
`S.space ≃ₗᵢ[ℂ] T.space`. Every structural conversion (associator, swap, reindex,
flat↔structured, …) of tensor spaces is a `QSystem.Iso`, and **transport** of states, pure
states, observables, evolutions and measurements
(`State`/`PureState`/`Observable`/`Evolution`/`Measurement`) is proved once here, so each
named conversion inherits it.

Transport uses the Mathlib construction `LinearIsometryEquiv.conjStarAlgEquiv`
(the ⋆-algebra equivalence `(S.space →L S.space) ≃⋆ₐ (T.space →L T.space)` induced by the
isometry): density / self-adjoint / unitary / completeness are preserved because it is a
unital ⋆-algebra equivalence. **Invariance** of quantities such as entropy,
expectation and fidelity under transport follows from the matching
`*_conjStarAlgEquiv` lemmas.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- A **system isomorphism**: an inner-product isometry between the state spaces of two
systems. It transports states, observables, evolutions and measurements between systems
regarded as the same up to reorganization. -/
structure QSystem.Iso (S T : QSystem) where
  /-- The underlying isometry of state spaces. -/
  toIsometry : S.space ≃ₗᵢ[ℂ] T.space

@[inherit_doc] scoped infix:25 " ≃ₛ " => QSystem.Iso

namespace QSystem.Iso

variable {S T U : QSystem}

instance : CoeFun (S ≃ₛ T) (fun _ ↦ S.space → T.space) := ⟨fun e ↦ e.toIsometry⟩

/-- The identity system isomorphism. -/
def refl (S : QSystem) : S ≃ₛ S := ⟨LinearIsometryEquiv.refl ℂ S.space⟩

/-- The inverse system isomorphism. -/
def symm (e : S ≃ₛ T) : T ≃ₛ S := ⟨e.toIsometry.symm⟩

/-- Composition of system isomorphisms. -/
def trans (e : S ≃ₛ T) (f : T ≃ₛ U) : S ≃ₛ U := ⟨e.toIsometry.trans f.toIsometry⟩

end QSystem.Iso

variable {S T : QSystem}

/-- **Transport a state** along a system isomorphism: `ρ ↦ e ρ e⁻¹`. A genuine `State`,
since `conjStarAlgEquiv` preserves the density-operator property. -/
def State.congr (e : S ≃ₛ T) (ρ : State S) : State T where
  op := e.toIsometry.conjStarAlgEquiv ρ.op
  isDensity := e.toIsometry.conjStarAlgEquiv_isDensityOp_iff.mpr ρ.isDensity

@[simp]
theorem State.congr_op (e : S ≃ₛ T) (ρ : State S) :
    (ρ.congr e).op = e.toIsometry.conjStarAlgEquiv ρ.op := rfl

/-- **Transport a pure state** along a system isomorphism: `ψ ↦ e ψ`. Norm-preserving. -/
def PureState.congr (e : S ≃ₛ T) (ψ : PureState S) : PureState T where
  vec := e.toIsometry ψ.vec
  normalized := by rw [LinearIsometryEquiv.norm_map, ψ.normalized]

@[simp]
theorem PureState.congr_vec (e : S ≃ₛ T) (ψ : PureState S) :
    (ψ.congr e).vec = e.toIsometry ψ.vec := rfl

/-- **Transport an observable** along a system isomorphism. Self-adjointness is preserved
by `conjStarAlgEquiv`. -/
def Observable.congr (e : S ≃ₛ T) (A : Observable S) : Observable T where
  op := e.toIsometry.conjStarAlgEquiv A.op
  selfAdjoint := e.toIsometry.conjStarAlgEquiv_isSelfAdjoint_iff.mpr A.selfAdjoint

@[simp]
theorem Observable.congr_op (e : S ≃ₛ T) (A : Observable S) :
    (A.congr e).op = e.toIsometry.conjStarAlgEquiv A.op := rfl

set_option synthInstance.maxHeartbeats 800000 in
-- `StarHomClass` for `≃⋆ₐ` now resolves through a low-priority generic instance; the default
-- heartbeat budget is too small to find it here.
/-- **Transport an evolution** along a system isomorphism. Unitarity is preserved because
`conjStarAlgEquiv` is a unital ⋆-algebra equivalence (`star`/`*`/`1` preserved). -/
def Evolution.congr (e : S ≃ₛ T) (U : Evolution S) : Evolution T where
  op := e.toIsometry.conjStarAlgEquiv U.op
  unitary := by
    have hU := Unitary.mem_iff.mp U.unitary
    rw [Unitary.mem_iff]
    refine ⟨?_, ?_⟩
    · rw [← map_star, ← map_mul, hU.1, map_one]
    · rw [← map_star, ← map_mul, hU.2, map_one]

@[simp]
theorem Evolution.congr_op (e : S ≃ₛ T) (U : Evolution S) :
    (U.congr e).op = e.toIsometry.conjStarAlgEquiv U.op := rfl

set_option synthInstance.maxHeartbeats 800000 in
-- `StarHomClass` for `≃⋆ₐ` now resolves through a low-priority generic instance; the default
-- heartbeat budget is too small to find it here.
/-- **Transport a measurement** along a system isomorphism. Completeness `∑ Mᵢ† Mᵢ = 1`
is preserved because `conjStarAlgEquiv` is an additive unital ⋆-algebra equivalence. -/
def Measurement.congr {ι : Type*} [Fintype ι] (e : S ≃ₛ T) (m : Measurement ι S) :
    Measurement ι T where
  op i := e.toIsometry.conjStarAlgEquiv (m.op i)
  complete := by
    have step : ∀ i, (adjoint (e.toIsometry.conjStarAlgEquiv (m.op i))).comp
        (e.toIsometry.conjStarAlgEquiv (m.op i))
        = e.toIsometry.conjStarAlgEquiv ((adjoint (m.op i)).comp (m.op i)) := by
      intro i
      have hstar : adjoint (e.toIsometry.conjStarAlgEquiv (m.op i))
          = e.toIsometry.conjStarAlgEquiv (adjoint (m.op i)) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
          ContinuousLinearMap.star_eq_adjoint]
      rw [hstar, ← ContinuousLinearMap.mul_def, ← map_mul, ContinuousLinearMap.mul_def]
    simp_rw [step]
    rw [← map_sum, m.complete, map_one]

@[simp]
theorem Measurement.congr_op {ι : Type*} [Fintype ι] (e : S ≃ₛ T) (m : Measurement ι S)
    (i : ι) : (m.congr e).op i = e.toIsometry.conjStarAlgEquiv (m.op i) := rfl

/-! ## Coherence and invariance under transport

The map from pure states to density operators commutes with transport, and expectation
values are invariant, by the matching `*_conjStarAlgEquiv` lemmas. -/

/-- Transport commutes with passing from a pure state to its density operator:
`|e ψ⟩⟨e ψ| = e |ψ⟩⟨ψ| e⁻¹`. -/
@[simp]
theorem PureState.congr_toState (e : S ≃ₛ T) (ψ : PureState S) :
    (ψ.congr e).toState = ψ.toState.congr e := by
  apply State.ext
  simp only [PureState.toState_op, State.congr_op, PureState.congr_vec,
    InnerProductSpace.rankOne_conjStarAlgEquiv]

/-- **Expectation is invariant under transport** (density operators): a system isomorphism does
not change `Tr(ρ A)`. Via `trace_conjStarAlgEquiv` and multiplicativity of the conjugation. -/
theorem State.expectation_congr (e : S ≃ₛ T) (ρ : State S) (A : Observable S) :
    (ρ.congr e).expectation (A.congr e) = ρ.expectation A := by
  simp only [State.expectation, State.congr_op, Observable.congr_op,
    ← ContinuousLinearMap.mul_def, ← map_mul, ContinuousLinearMap.trace_conjStarAlgEquiv]

/-- **Expectation is invariant under transport** (pure states): reduces to the density
operator case via `|ψ⟩⟨ψ|`. -/
theorem PureState.expectation_congr (e : S ≃ₛ T) (ψ : PureState S) (A : Observable S) :
    (ψ.congr e).expectation (A.congr e) = ψ.expectation A := by
  rw [← expectation_toState, PureState.congr_toState, State.expectation_congr]
  exact expectation_toState ψ A

end AxQM
