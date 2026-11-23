/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EnsemblePurification

/-!
# Nielsen & Chuang, Exercise 2.82 (purification of `ρ` via a reference `R`; measuring `R`
recovers the ensemble)

Purification of rho via reference R; measurement of R recovers ensemble.

## Part (1) — the ensemble purification

In `AxQM/Postulates/API/EnsemblePurification.lean`:

* `AxQM.Ensemble.purifyVec` — the purification vector `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`, with
  `|i⟩` the standard orthonormal basis of the reference `EuclideanSpace ℂ (Fin e.card)`.
* `AxQM.Ensemble.purify` — the purification as a `PureState` on `S ⊗ QSystem.ofModel
  (EuclideanSpace ℂ (Fin e.card))`.
* `AxQM.Ensemble.purify_isPurification` — `|AR⟩` purifies `ρ`
  (`TensorProduct.IsPurification`).
* `AxQM.Ensemble.purify_reducedLeft` — **the exercise's part (1)**: tracing out the
  reference recovers `ρ`, i.e. `e.purify.toState.reducedLeft = e.toState`.

The essential point (versus the canonical spectral purification `State.purify`) is that the
reference basis is indexed by the *ensemble* index `i` and the ensemble states `|ψᵢ⟩` need not be
orthonormal; only the reference vectors `|i⟩` are. This is what lets a measurement of `R` in the
`|i⟩` basis recover *this* ensemble in parts (2)/(3).

## Part (2) — measuring the reference recovers the ensemble

Also in `AxQM/Postulates/API/EnsemblePurification.lean` (measuring `R` in the `|i⟩` basis
is the composite measurement `I_A ⊗ |i⟩⟨i|`, whose reference system is again `EuclideanSpace`):

* `AxQM.Ensemble.refMeasurement` — the reference measurement `Rᵢ = I_A ⊗ |i⟩⟨i|`, built by
  lifting the projective measurement of the reference `EuclideanSpace` to the composite via
  `AxQM.Measurement.onRight` (in
  `AxQM/Postulates/API/CompositeMeasurement.lean`).
* `AxQM.Ensemble.bornProb_refMeasurement_purify` — **part (2), probability**: outcome `i`
  occurs with probability exactly `pᵢ`, `e.refMeasurement.bornProb e.purify.toState i = e.prob i`
  (holds for every `i`, no positivity hypothesis).
* `AxQM.Ensemble.postMeasurement_refMeasurement_purify` — the *joint* post-measurement
  state of `S ⊗ R` conditioned on the (possible) outcome `i` is the product `|ψᵢ ⊗ i⟩⟨ψᵢ ⊗ i|`.
* `AxQM.Ensemble.postMeasurement_refMeasurement_purify_reducedLeft` — **part (2),
  state**: conditioned on the (possible) outcome `i`, the reduced state of `A` is `|ψᵢ⟩⟨ψᵢ|`, i.e.
  `(e.refMeasurement.postMeasurement e.purify.toState i hp).reducedLeft = (e.states i).toState`.

## Part (3) — measuring *any* purification's reference recovers the ensemble

Also in `AxQM/Postulates/API/EnsemblePurification.lean`. The recovery mechanism is proved
once for an **arbitrary** orthonormal basis `b` of the reference and any pure state `φ` with vector
`∑ᵢ √pᵢ |ψᵢ⟩ ⊗ b i`; part (2)'s standard-basis `refMeasurement_*` lemmas are one-line corollaries of
this family (`b := |i⟩`, `φ := e.purify`), so the proof lives in exactly one place:

* `AxQM.Ensemble.op_ofOrthonormalBasis_onRight_apply` /
  `AxQM.Ensemble.postOp_ofOrthonormalBasis_onRight` — the arbitrary-basis key identity and
  post-measurement operator (`refMeasurement_op_purifyVec` / `postOp_refMeasurement_purify` are
  their `b = |i⟩` instances). The reference basis pure state `|bᵢ⟩` is the named
  `Ensemble.basisState b i`.
* `AxQM.Ensemble.bornProb_ofOrthonormalBasis_onRight` — outcome `i` has probability `pᵢ`.
* `AxQM.Ensemble.postMeasurement_ofOrthonormalBasis_onRight` /
  `AxQM.Ensemble.postMeasurement_ofOrthonormalBasis_onRight_reducedLeft` — the joint
  post-measurement state is `|ψᵢ ⊗ bᵢ⟩⟨ψᵢ ⊗ bᵢ|`, and tracing out `R` leaves `A` in `|ψᵢ⟩⟨ψᵢ|`.

* `AxQM.Ensemble.exists_orthonormalBasis_refMeasurement_recovers_ensemble` — **the
  exercise's part (3)**: for *any* purification `φ` of `ρ` to `S ⊗ R` there is an orthonormal basis
  `b` of `R` such that measuring `R` in `b` yields outcome `i` with probability `pᵢ` and
  post-measurement `A`-state `|ψᵢ⟩⟨ψᵢ|`. The basis is `b i = U |i⟩`, the standard basis rotated by
  the reference unitary `U` relating `φ` to `e.purify`. That unitary is the **freedom in
  purifications** (Exercise 2.81); it is obtained at the level of state vectors
  from the Mathlib lemma `TensorProduct.exists_mem_unitary_mapL_id_eq` (the vector form of
  `PureState.exists_evolution_tmul_id_evolvePure_eq`, on which the statement of Exercise 2.81 in
  `AxQM/NC/Ch2/Exercise2_81.lean` is built).
-/
