/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Interchange
import AxQM.Postulates.Composite
import AxQM.Postulates.PartialTrace
import AxQM.Postulates.SystemIso
import AxQM.Postulates.Evolution
import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# AxQM — the environment-model channel with different input/output spaces (N&C Ex 8.3)

This file formalises **Nielsen–Chuang Exercise 8.3** (the generalization of the
operator-sum derivation of §8.2.3 to *different input and output spaces*).

A principal system `A ⊗ B` in an unknown state `ρ` is brought into contact with an environment
`C ⊗ D` prepared in a standard pure state `|0⟩ = ω`, the two interact by a joint unitary `U`, and
afterwards systems `A` and `D` are discarded, leaving a state `ρ'` on `B ⊗ C`.  The resulting map

  `E(ρ) = ρ' = tr_{A,D}(U (ρ ⊗ |0⟩⟨0|) U†)`

is the **environment-model channel** `envModelChannel ω U`; Exercise 8.3 asks to show it has an
operator-sum representation `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` with `∑ₖ Eₖ† Eₖ = I`, where the `Eₖ` are linear
operators *from* the input space of `A ⊗ B` *to* the output space of `B ⊗ C` (eq. 8.15).

## Contents

* `AxQM.envModelChannel` — the channel `E(ρ)`, built as
  `((U.evolve (ρ ⊗ |0⟩⟨0|)).congr Φ).reducedLeft`, where the transport `Φ = interchangeBCAD` first
  regroups `(A ⊗ B) ⊗ (C ⊗ D)` into `(B ⊗ C) ⊗ (A ⊗ D)` so that `State.reducedLeft` (which traces
  out the *right* factor) discards exactly `A ⊗ D` and keeps `B ⊗ C`.
* `AxQM.envModelChannel_hasOperatorSum` — **the exercise:** the channel `E` has an
  operator-sum representation with operation elements `Eₖ : (A ⊗ B).space →ₗ (B ⊗ C).space`
  satisfying `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` (eq. 8.15) *and* the completeness relation `∑ₖ Eₖ† Eₖ = I`
  (making `E` trace preserving).  The two are witnessed by the *same* family, as N&C requires.

## Proof

The statement of Exercise 8.3 is in `AxQM/NC/Ch8/Exercise8_3.lean`; the declarations are here.
Compare Exercise 8.2 (`AxQM/Postulates/API/MeasurementOperation.lean`).

The whole content is assembled by *instantiating* the operator-sum infrastructure
in `ToMathlib.Analysis.InnerProductSpace.OperatorSum`
(`partialTraceRight_conj_map_rankOne_eq_sum_krausOp` for eq. 8.15,
`sum_adjoint_krausOp_tmulRightVec_comp_krausOp` for eq. 8.14).  The physics work is the *bridge*:
unfolding the definitions (`Evolution.evolve`, `State.tmul`, `PureState.toState`,
`State.congr`, `State.reducedLeft`) down to the raw joint dilation
`W = Φ ∘ U : (A ⊗ B).space ⊗ (C ⊗ D).space →ₗ (B ⊗ C).space ⊗ (A ⊗ D).space` and its
`|ω⟩⟨ω|`-ancilla conjugation, so that the package applies.  The operation elements are then
`Eₖ = ⟨eₖ| (W (· ⊗ ω)) = krausOp (stdOB (A ⊗ D).space) (W ∘ tmulRightVec ω.vec) k`, with `eₖ`
running over a basis of the discarded space `A ⊗ D`.  `W` is an isometry (`Φ` a system
isomorphism, `U` unitary), which is exactly what makes the operation elements complete.
-/

open scoped InnerProductSpace

open LinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {A B C D : QSystem}

/-- **The environment-model channel (Nielsen & Chuang Exercise 8.3).**  A principal system `A ⊗ B`
in state `ρ` and an environment `C ⊗ D` in a standard pure state `ω = |0⟩` interact by the joint
unitary `U`; systems `A` and `D` are then discarded, leaving `B ⊗ C`.  Concretely
`E(ρ) = ((U.evolve (ρ ⊗ |ω⟩⟨ω|)).congr Φ).reducedLeft`, where the system isomorphism
`Φ = QSystem.interchangeBCAD` regroups `(A ⊗ B) ⊗ (C ⊗ D)` into `(B ⊗ C) ⊗ (A ⊗ D)` so that tracing
out the right factor (`State.reducedLeft`) discards exactly `A ⊗ D`. -/
def envModelChannel (ω : PureState (C ⊗ D)) (U : Evolution ((A ⊗ B) ⊗ (C ⊗ D)))
    (ρ : State (A ⊗ B)) : State (B ⊗ C) :=
  ((U.evolve (ρ.tmul ω.toState)).congr (QSystem.interchangeBCAD A B C D)).reducedLeft

set_option maxHeartbeats 400000 in
-- The definitional bridge between the composite-system space `(S ⊗ T).space` (bundled `QSystem`
-- instances) and the raw `TensorProduct` the operator-sum package is stated over is costly to
-- reconcile (the `InnerProductSpace` instances agree definitionally but not syntactically).
/-- **Nielsen & Chuang, Exercise 8.3.**  Discarding subsystems `A` and `D` after a joint unitary
interaction of a principal system `A ⊗ B` (in state `ρ`) with an environment `C ⊗ D` (prepared in a
standard pure state `ω`) yields a channel `E = envModelChannel ω U : State (A ⊗ B) → State (B ⊗ C)`
in operator-sum form: there is a family of operation elements `Eₖ : (A ⊗ B).space →ₗ (B ⊗ C).space`
with

* `E(ρ) = ∑ₖ Eₖ ρ Eₖ†`   (eq. 8.15), and
* `∑ₖ Eₖ† Eₖ = I`         (eq. 8.14 — completeness / trace preservation),

both witnessed by the *same* family.  The operation elements are
`Eₖ = krausOp (stdOB (A ⊗ D).space) (W ∘ tmulRightVec ω.vec)`, with `W = Φ ∘ U` the joint
interaction-then-regrouping map and `Φ = interchangeBCAD`; `W` is an isometry, whence completeness.
Proved by instantiating the operator-sum package
(`partialTraceRight_conj_map_rankOne_eq_sum_krausOp` for the operator sum,
`sum_adjoint_krausOp_tmulRightVec_comp_krausOp` for completeness) after bridging the
definitions (`Evolution.evolve`, `State.tmul`, `PureState.toState`, `State.congr`,
`State.reducedLeft`) down to the raw dilation `W`. -/
theorem envModelChannel_hasOperatorSum (ω : PureState (C ⊗ D))
    (U : Evolution ((A ⊗ B) ⊗ (C ⊗ D))) :
    ∃ (ι : Type) (_ : Fintype ι) (E : ι → ((A ⊗ B).space →ₗ[ℂ] (B ⊗ C).space)),
      (∀ ρ : State (A ⊗ B),
          (↑(envModelChannel ω U ρ).op : (B ⊗ C).space →ₗ[ℂ] (B ⊗ C).space)
            = ∑ k, E k ∘ₗ (↑ρ.op) ∘ₗ LinearMap.adjoint (E k)) ∧
        ∑ k, LinearMap.adjoint (E k) ∘ₗ E k = LinearMap.id := by
  -- The joint dilation: interact by `U`, then regroup `(A⊗B)⊗(C⊗D) → (B⊗C)⊗(A⊗D)` by `Φ`.
  -- Its type `((A⊗B)⊗(C⊗D)).space →ₗ ((B⊗C)⊗(A⊗D)).space` is defeq to the raw tensor form the
  -- operator-sum package expects.
  set W := (QSystem.interchangeBCAD A B C D).toIsometry.toLinearMap ∘ₗ U.op.toLinearMap with hW
  clear_value W
  -- `W` is an isometry: `Φ` a linear isometry equivalence, `U` unitary.
  have he_adj : LinearMap.adjoint (QSystem.interchangeBCAD A B C D).toIsometry.toLinearMap
      ∘ₗ (QSystem.interchangeBCAD A B C D).toIsometry.toLinearMap = LinearMap.id := by
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]; ext x; simp
  have hU : LinearMap.adjoint U.op.toLinearMap ∘ₗ U.op.toLinearMap = LinearMap.id := by
    rw [ContinuousLinearMap.adjoint_toLinearMap, ← ContinuousLinearMap.toLinearMap_comp,
      Evolution.adjoint_comp_self]
    rfl
  have hWiso : LinearMap.adjoint W ∘ₗ W = LinearMap.id := by
    rw [hW, LinearMap.adjoint_comp]
    refine LinearMap.ext fun x => ?_
    have e1 := LinearMap.congr_fun he_adj (U.op.toLinearMap x)
    have e2 := LinearMap.congr_fun hU x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e1 e2 ⊢
    rw [e1, e2]
  -- The operator-sum identity for the explicit operation elements.
  have key_op : ∀ ρ : State (A ⊗ B),
      (↑(envModelChannel ω U ρ).op : (B ⊗ C).space →ₗ[ℂ] (B ⊗ C).space)
        = ∑ k, krausOp (stdOrthonormalBasis ℂ (A ⊗ D).space) (W ∘ₗ tmulRightVec ω.vec) k
            ∘ₗ (↑ρ.op)
            ∘ₗ LinearMap.adjoint
                (krausOp (stdOrthonormalBasis ℂ (A ⊗ D).space) (W ∘ₗ tmulRightVec ω.vec) k) := by
    intro ρ
    -- The adjoint of the joint dilation, in clean coercion form: `W† = U† ∘ Φ⁻¹`.
    have hWadj : LinearMap.adjoint W = U.op.adjoint.toLinearMap
        ∘ₗ (QSystem.interchangeBCAD A B C D).toIsometry.symm.toLinearMap := by
      rw [hW, LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
        ← ContinuousLinearMap.adjoint_toLinearMap]
    -- `State.congr` acts by conjugation by `Φ`; unfold to the clean `.toLinearMap` form.
    have hcongr : (↑(State.congr (QSystem.interchangeBCAD A B C D)
            (U.evolve (ρ.tmul ω.toState))).op :
            ((B ⊗ C) ⊗ (A ⊗ D)).space →ₗ[ℂ] ((B ⊗ C) ⊗ (A ⊗ D)).space)
          = (QSystem.interchangeBCAD A B C D).toIsometry.toLinearMap
              ∘ₗ (↑(U.evolve (ρ.tmul ω.toState)).op)
              ∘ₗ (QSystem.interchangeBCAD A B C D).toIsometry.symm.toLinearMap := by
      rw [State.congr_op, LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap, LinearEquiv.conj_apply]
      rfl
    -- `Evolution.evolve` conjugates by `U`; `tmul`/`toState` give `ρ ⊗ |ω⟩⟨ω|`.
    have hY : (↑(U.evolve (ρ.tmul ω.toState)).op :
            ((A ⊗ B) ⊗ (C ⊗ D)).space →ₗ[ℂ] ((A ⊗ B) ⊗ (C ⊗ D)).space)
          = U.op.toLinearMap
              ∘ₗ TensorProduct.map (↑ρ.op) (InnerProductSpace.rankOne ℂ ω.vec ω.vec).toLinearMap
              ∘ₗ U.op.adjoint.toLinearMap := by
      rw [Evolution.evolve_op, State.tmul_op, PureState.toState_op]
      simp only [ContinuousLinearMap.toLinearMap_comp]
      erw [ContinuousLinearMap.toLinearMap_comp, TensorProduct.toLinearMap_mapL]
      rfl
    -- Bridge the definitions to the raw `|ω⟩⟨ω|`-ancilla conjugation of `W`.
    have hop : (↑(State.congr (QSystem.interchangeBCAD A B C D)
            (U.evolve (ρ.tmul ω.toState))).op :
            ((B ⊗ C) ⊗ (A ⊗ D)).space →ₗ[ℂ] ((B ⊗ C) ⊗ (A ⊗ D)).space)
          = W ∘ₗ TensorProduct.map (↑ρ.op)
              (InnerProductSpace.rankOne ℂ ω.vec ω.vec).toLinearMap ∘ₗ LinearMap.adjoint W := by
      rw [hcongr, hY, hWadj, hW]
      rfl
    unfold envModelChannel
    rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap, hop]
    exact partialTraceRight_conj_map_rankOne_eq_sum_krausOp
      (stdOrthonormalBasis ℂ (A ⊗ D).space) W ω.vec ρ.op.toLinearMap
  have key_complete :
      ∑ k, LinearMap.adjoint (krausOp (stdOrthonormalBasis ℂ (A ⊗ D).space)
              (W ∘ₗ tmulRightVec ω.vec) k)
            ∘ₗ krausOp (stdOrthonormalBasis ℂ (A ⊗ D).space) (W ∘ₗ tmulRightVec ω.vec) k
        = LinearMap.id :=
    sum_adjoint_krausOp_tmulRightVec_comp_krausOp
      (stdOrthonormalBasis ℂ (A ⊗ D).space) W hWiso ω.normalized
  exact ⟨_, _, fun k => krausOp (stdOrthonormalBasis ℂ (A ⊗ D).space)
    (W ∘ₗ tmulRightVec ω.vec) k, key_op, key_complete⟩

end AxQM
