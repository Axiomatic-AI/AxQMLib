/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.UnreadMeasurement
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.PartialTrace
import ToMathlib.Analysis.InnerProductSpace.Adjoint
import ToMathlib.Analysis.InnerProductSpace.PartialTraceChannel

/-!
# Nielsen & Chuang, Exercise 4.32 (unread measurement; no-signalling)

*(N&C p. 187.)*

Show unread measurement gives rho'=P0 rho P0+P1 rho P1 and preserves tr_2.

## The formalisation

The exercise has two claims, formalised at the level N&C's argument actually uses — a *general*
measurement `m` (Postulate 3, `Measurement`) on the second factor of *any* bipartite system `S ⊗ T`,
of which the projective computational-basis measurement of a qubit is the special case (`P₀`, `P₁`
are `M₀`, `M₁`). This is a faithful strengthening: both claims are the general no-signalling content
that N&C invokes here (and again to justify the "principle of implicit measurement"), and neither
adds a hypothesis nor specializes a dimension.

The **unread (non-selective) post-measurement state** `ρ' = Σᵢ Mᵢ ρ Mᵢ†` is
`Measurement.unreadState` (`AxQM/Postulates/API/UnreadMeasurement.lean`).

* **Claim 1 (Eq. (4.40)).** `ρ' = Σᵢ Mᵢ ρ Mᵢ†` is
  `Measurement.unreadState_op_eq_sum_opElement` (the unread state is the sum of the quantum
  operation elements `Eᵢ(ρ) = Mᵢ ρ Mᵢ†`); for a *projective* measurement (`Mᵢ = Pᵢ`, so
  `Mᵢ† = Mᵢ`) this is the literal `ρ' = Σᵢ Pᵢ ρ Pᵢ`, `Measurement.IsProjective.unreadState_op`.
  These are stated in terms of the density operator `State.op` and are in
  `AxQM/Postulates/API/UnreadMeasurement.lean`.

* **Claim 2 (`tr₂(ρ) = tr₂(ρ')`).** Measuring the right (second) factor by an unread
  measurement leaves the reduced state of the left (first) factor unchanged. This is stated for
  the reduced states `State.reducedLeft` (Postulate-6 partial trace) of `ρ` and of the unread state
  of the lifted measurement `Measurement.onRight` (`Nᵢ = 1_S ⊗ Mᵢ`), and is the theorem
  `Measurement.unreadState_reducedLeft_onRight` below.

## Proof of Claim 2

`reducedLeft` is `Tr_T`, and the unread state of `m.onRight S` has operator
`Σᵢ (1 ⊗ Mᵢ) ρ (1 ⊗ Mᵢ†)`. So Claim 2 is exactly the lemma
`LinearMap.partialTraceRight_sum_conj_map_id` — the partial trace over the traced factor is
invariant under a local trace-preserving operator sum on that factor — instantiated at
`Mᵢ = m.op i`, `Nᵢ = Mᵢ†`, whose completeness hypothesis `Σᵢ Mᵢ† Mᵢ = 1` is `m.complete`. The proof
below unfolds `reducedLeft`/`unreadState`/`onRight` to the underlying operators (`State.ext`,
`reducedLeft_op`, `onRight_op`, `krausSumₗ_apply`) and pushes the `→L → →ₗ` coercion through the
sum and the tensor maps. `TensorProduct.adjoint_mapL` is *not* usable here — `onRight`'s `↥S`
coercion of `1 ⊗ Mᵢ` produces an instance mismatch that blocks it — so the adjoint is routed
instead through `LinearMap.adjoint` (moving it across the coercion with the library lemma
`ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace`) and `TensorProduct.adjoint_map`, and
the lemma is then applied.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S T : QSystem}

namespace Measurement

/-- **Nielsen–Chuang Exercise 4.32, Claim 2 (the reduced state is preserved; no-signalling).**
Measuring the second (right) factor of a bipartite system `S ⊗ T` by an *unread* (non-selective)
measurement leaves the reduced density matrix of the first (left) factor unchanged:
`tr₂(ρ) = tr₂(ρ')`, i.e. `(ρ').reducedLeft = ρ.reducedLeft` where `ρ' = (m.onRight S).unreadState ρ`
has operator `Σᵢ (1 ⊗ Mᵢ) ρ (1 ⊗ Mᵢ†)`.

This is the general statement of which N&C's two-qubit computational-basis case is a special
instance: a trace-preserving operation on the measured subsystem cannot affect the marginal of the
other subsystem. It reduces to the lemma `LinearMap.partialTraceRight_sum_conj_map_id` (the
partial trace over `T` is invariant under the local operator sum `Σᵢ (1 ⊗ Mᵢ) · (1 ⊗ Mᵢ†)`), whose
completeness hypothesis `Σᵢ Mᵢ† Mᵢ = 1` is `m.complete`. -/
theorem unreadState_reducedLeft_onRight (m : Measurement ι T) (ρ : State (S ⊗ T)) :
    ((m.onRight S).unreadState ρ).reducedLeft = ρ.reducedLeft := by
  -- `TensorProduct.adjoint_mapL` cannot take the adjoint of `onRight`'s `1 ⊗ Mᵢ` (its `↥S` coercion
  -- produces an instance mismatch that blocks the rewrite); the adjoint is moved across the
  -- coercion by the library lemma `ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace` and
  -- split with `TensorProduct.adjoint_map`.
  -- Completeness `∑ᵢ Mᵢ† Mᵢ = 1` as a `LinearMap` identity, with `Mᵢ† = LinearMap.adjoint Mᵢ`.
  have hMN : ∑ i, LinearMap.adjoint (↑(m.op i) : T.space →ₗ[ℂ] T.space) ∘ₗ
      (↑(m.op i) : T.space →ₗ[ℂ] T.space) = LinearMap.id := by
    have h := congrArg (fun f : T.space →L[ℂ] T.space => (↑f : T.space →ₗ[ℂ] T.space)) m.complete
    simpa only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace, ContinuousLinearMap.toLinearMap_one,
      Module.End.one_eq_id] using h
  -- The two measurement operators of `m.onRight S`, `1 ⊗ Mᵢ` and its adjoint, in the
  -- `TensorProduct.map`/`LinearMap` form the lemma expects.
  have hop : ∀ i, (↑((m.onRight S).op i) : (S ⊗ T).space →ₗ[ℂ] (S ⊗ T).space)
      = TensorProduct.map LinearMap.id (↑(m.op i) : T.space →ₗ[ℂ] T.space) := fun i => by
    rw [onRight_op, TensorProduct.toLinearMap_mapL]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id]; rfl
  have hadjop : ∀ i, (↑(ContinuousLinearMap.adjoint ((m.onRight S).op i)) :
        (S ⊗ T).space →ₗ[ℂ] (S ⊗ T).space)
      = TensorProduct.map LinearMap.id
          (LinearMap.adjoint (↑(m.op i) : T.space →ₗ[ℂ] T.space)) := fun i => by
    rw [ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace, hop]
    refine (TensorProduct.adjoint_map _ _).trans ?_
    rw [LinearMap.adjoint_id]
  have key : (↑((m.onRight S).unreadState ρ).op : (S ⊗ T).space →ₗ[ℂ] (S ⊗ T).space)
      = ∑ i, TensorProduct.map LinearMap.id (↑(m.op i) : T.space →ₗ[ℂ] T.space) ∘ₗ
          (↑ρ.op : (S ⊗ T).space →ₗ[ℂ] (S ⊗ T).space) ∘ₗ
          TensorProduct.map LinearMap.id
            (LinearMap.adjoint (↑(m.op i) : T.space →ₗ[ℂ] T.space)) := by
    rw [unreadState_op, krausSumₗ_apply, ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp, hop, hadjop]
    rfl
  apply State.ext
  rw [State.reducedLeft_op, State.reducedLeft_op, key]
  congr 1
  exact LinearMap.partialTraceRight_sum_conj_map_id _ _ _ hMN _

end Measurement

end AxQM
