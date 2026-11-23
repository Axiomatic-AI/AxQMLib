/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Ensemble
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.Composite
import AxQM.Postulates.PartialTraceTensor
import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import ToMathlib.Analysis.InnerProductSpace.PurificationFreedom

/-!
# AxQM — purification of an ensemble's density operator

Nielsen–Chuang **Exercise 2.82(1)** (and the analogous construction of eq. (2.207)): given an
ensemble `{pᵢ, |ψᵢ⟩}` of a system `S` generating `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, and a reference system `R`
with orthonormal basis `|i⟩`, the vector

  `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`

is a **purification** of `ρ`: tracing out `R` recovers `ρ` as the left marginal. Here `R` is the
concrete model space `EuclideanSpace ℂ (Fin e.card)` with its standard basis, wrapped through the
§3.2 `QSystem.ofModel` constructor exactly as the canonical purification `State.purify` names its
ancilla.

Unlike `State.purify` — whose reference is a *copy of `S`* and whose Schmidt basis is `ρ`'s
eigenbasis — this **ensemble purification** uses the ensemble's *own* states `|ψᵢ⟩` (which need
**not** be orthonormal) and a reference of dimension `e.card`. The partial trace still collapses to
`ρ` because only the reference vectors `|i⟩` need be orthonormal: in
`LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt` the off-diagonal cross terms vanish
from orthonormality of `|i⟩` alone, giving `∑ᵢ (√pᵢ)² |ψᵢ⟩⟨ψᵢ| = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ| = ρ`. Keeping the
reference basis indexed by the *ensemble* index `i` is what lets a later measurement of `R` recover
this very ensemble (Exercise 2.82(2)/(3)).

## Main definitions

* `AxQM.Ensemble.purifyVec` — the raw purification vector `∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`.
* `AxQM.Ensemble.purify` — the purification as a `PureState` on
  `S ⊗ ofModel (EuclideanSpace ℂ (Fin e.card))`; unit norm is inherited from
  `TensorProduct.norm_eq_one_of_isPurification`.

## Main results

* `AxQM.Ensemble.purify_isPurification` — `|AR⟩` purifies `ρ`
  (`TensorProduct.IsPurification`).
* `AxQM.Ensemble.purify_reducedLeft` — **Exercise 2.82(1)**: the left
  marginal of `|AR⟩⟨AR|` is `ρ`, i.e. `e.purify.toState.reducedLeft = e.toState`.
* The `*_ofOrthonormalBasis_onRight` family — **Exercise 2.82(2)/(3)** engine: measuring the
  reference in *any* orthonormal basis `b` recovers the ensemble whenever
  `φ.vec = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ b i`.
  Its standard-basis case (`b = |i⟩`) is Exercise 2.82(2) (the `refMeasurement_*` corollaries) and
  its rotated-basis case is Exercise 2.82(3)
  (`exists_orthonormalBasis_refMeasurement_recovers_ensemble`).

These are the statements of N&C Exercise 2.82 (see also `AxQM/NC/Ch2/Exercise2_82.lean`).
-/

open scoped InnerProductSpace TensorProduct
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- The **ensemble purification vector** `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` (Nielsen–Chuang Exercise
2.82(1)): the subnormalized ensemble states `√pᵢ |ψᵢ⟩` tensored against the standard orthonormal
basis `|i⟩` of the reference `EuclideanSpace ℂ (Fin e.card)`. -/
def purifyVec (e : Ensemble S) :
    (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space :=
  ∑ i, (Real.sqrt (e.prob i) : ℂ) •
    ((e.states i).vec ⊗ₜ[ℂ] (EuclideanSpace.basisFun (Fin e.card) ℂ) i)

/-- **The ensemble purification vector purifies `ρ`**: the right-partial-trace of `|AR⟩⟨AR|`
recovers the ensemble's density operator `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`. Orthonormality of the reference
basis `|i⟩` (not of the ensemble states) collapses the cross terms via
`LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt`, leaving `∑ᵢ (√pᵢ)² |ψᵢ⟩⟨ψᵢ|`, and
`(√pᵢ)² = pᵢ` turns this into `ρ`. -/
theorem isPurification_purifyVec (e : Ensemble S) :
    TensorProduct.IsPurification e.toState.op e.purifyVec := by
  have hpt := LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
      (fun i => Real.sqrt (e.prob i)) (fun i => (e.states i).vec)
      (fun i => (EuclideanSpace.basisFun (Fin e.card) ℂ) i)
      (EuclideanSpace.basisFun (Fin e.card) ℂ).orthonormal (Ψ := e.purifyVec) rfl
  unfold TensorProduct.IsPurification
  rw [hpt, e.toState_op, ContinuousLinearMap.toLinearMap_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.toLinearMap_smul, PureState.toState_op]
  congr 1
  norm_cast
  exact congrArg _ (Real.sq_sqrt (e.prob_nonneg i))

/-- **Ensemble purification** (Nielsen–Chuang Exercise 2.82(1), eq. (2.207)): the pure state on the
composite `S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))` whose vector is `∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`.
Unit norm is `TensorProduct.norm_eq_one_of_isPurification` applied to `isPurification_purifyVec`. -/
def purify (e : Ensemble S) :
    PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))) where
  vec := e.purifyVec
  normalized :=
    TensorProduct.norm_eq_one_of_isPurification e.toState.isDensity e.isPurification_purifyVec

@[simp]
theorem purify_vec (e : Ensemble S) : e.purify.vec = e.purifyVec := rfl

/-- **Exercise 2.82(1), explicit form.** The ensemble purification vector as the explicit sum
`∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` over the standard reference basis — the `φ.vec = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ b i` hypothesis
the arbitrary-basis recovery family consumes at `b = |i⟩`, `φ = e.purify`. (`purify_vec` only
unfolds to the `purifyVec` def name; this is its propositional, citable form.) -/
theorem purify_vec_sum (e : Ensemble S) :
    e.purify.vec = ∑ i, (Real.sqrt (e.prob i) : ℂ)
      • ((e.states i).vec ⊗ₜ[ℂ] (EuclideanSpace.basisFun (Fin e.card) ℂ) i) := by
  rw [purify_vec]; rfl

/-- **The ensemble purification is a purification**: the right-partial-trace of
`|e.purify⟩⟨e.purify|` recovers `ρ.op`. The bridge to `TensorProduct.IsPurification`. -/
theorem purify_isPurification (e : Ensemble S) :
    TensorProduct.IsPurification e.toState.op e.purify.vec :=
  e.isPurification_purifyVec

/-- **Exercise 2.82(1): the ensemble purification has `ρ` as its left marginal.** Tracing out the
reference `R` of `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` recovers the ensemble's density operator:
`e.purify.toState.reducedLeft = e.toState`. This is the grounded (postulate-level) form of
`isPurification_purifyVec`, mirroring `State.purify_reducedLeft_eq`. -/
theorem purify_reducedLeft (e : Ensemble S) :
    e.purify.toState.reducedLeft = e.toState := by
  ext1
  rw [State.reducedLeft_op, PureState.toState_op]
  exact (congrArg LinearMap.toContinuousLinearMap e.purify_isPurification).trans
    (ContinuousLinearMap.toLinearMap_toContinuousLinearMap _)

/-! ### The reference marginal is the Gram operator

Tracing out system `A` from the ensemble purification `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` leaves the
reference in the **Gram operator** `ρ_R = ∑ᵢⱼ √pᵢ √pⱼ ⟪ψⱼ, ψᵢ⟫ |i⟩⟨j|`, whose matrix in the
standard basis `|i⟩` is the (subnormalized) Gram matrix of the ensemble states. Its diagonal is the
weight distribution `p`, and it is diagonal **iff** the `|ψᵢ⟩` are orthogonal — the reference-side
computation behind Nielsen & Chuang's proof of the equality condition in Theorem 11.10. -/

/-- **The reference marginal of the ensemble purification is the Gram operator.** Tracing out `A`
from `|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` gives the reference density operator

`ρ_R = ∑ᵢ ∑ⱼ √pᵢ √pⱼ ⟪ψⱼ, ψᵢ⟫ · |i⟩⟨j|`,

the Gram operator of the (subnormalized) ensemble states in the standard reference basis. The
off-diagonal entry `(i, j)` carries the overlap `⟪ψⱼ, ψᵢ⟫`, so `ρ_R` is diagonal exactly when the
ensemble states are pairwise orthogonal — the crux of the equality condition in the entropy-of-a-
mixture bound (N&C Theorem 11.10).

Proof: expand `|AR⟩⟨AR|` bilinearly (`rankOne_sum_smul_sum_smul`); the partial trace over the left
factor is linear, and on each pure-tensor rank-one term
`LinearMap.partialTraceLeft_rankOne_tmul` collapses the `A`-slot into the overlap `⟪ψⱼ, ψᵢ⟫`,
leaving `|i⟩⟨j|` on the reference. -/
theorem purify_reducedRight_op (e : Ensemble S) :
    e.purify.toState.reducedRight.op
      = ∑ i, ∑ j, ((Real.sqrt (e.prob i) : ℂ) * (Real.sqrt (e.prob j) : ℂ)
            * inner ℂ (e.states j).vec (e.states i).vec) •
          InnerProductSpace.rankOne ℂ ((EuclideanSpace.basisFun (Fin e.card) ℂ) i)
            ((EuclideanSpace.basisFun (Fin e.card) ℂ) j) := by
  apply ContinuousLinearMap.coe_injective
  rw [State.reducedRight_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op]
  -- `erw` bridges the composite-space instance diamond `(S ⊗ R).space` vs `S.space ⊗ R.space`
  -- (identical up to `isDefEq`) so the abstract partial-trace lemma matches the composite rank-one.
  erw [LinearMap.partialTraceLeft_rankOne_sum_smul_tmul (stdOrthonormalBasis ℂ S.space)
      (fun i => (Real.sqrt (e.prob i) : ℂ)) (fun i => (e.states i).vec)
      (fun i => (EuclideanSpace.basisFun (Fin e.card) ℂ) i) (Ψ := e.purify.vec) e.purify_vec_sum]
  simp only [Complex.conj_ofReal, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_smul]
  rfl

/-! ### Measuring the reference in a basis (Exercise 2.82(2) and (3))

Measuring the reference `R` of a purification in an orthonormal basis `b` of `R` is the composite
measurement `I_A ⊗ |bᵢ⟩⟨bᵢ|` (`Measurement.ofOrthonormalBasis b |>.onRight S`). The
`*_ofOrthonormalBasis_onRight` family below is the reusable engine: for **any** orthonormal basis
`b` and **any** pure state `φ` whose vector is `∑ᵢ √pᵢ |ψᵢ⟩ ⊗ b i`, measuring `R` in `b` yields
outcome `i` with probability `pᵢ` (`bornProb_ofOrthonormalBasis_onRight`) and collapses `A` to
`|ψᵢ⟩⟨ψᵢ|` (`postMeasurement_ofOrthonormalBasis_onRight_reducedLeft`).

* **Exercise 2.82(2)** is the standard-basis case `b = |i⟩`, `φ = e.purify` — the reference
  measurement `Ensemble.refMeasurement` and the corollaries `refMeasurement_op_purifyVec` /
  `bornProb_refMeasurement_purify` / `postMeasurement_refMeasurement_purify[_reducedLeft]`, each a
  one-line instantiation of the general lemma (`e.purify.vec = e.purifyVec = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`
  supplies `hφ` by `rfl`).
* **Exercise 2.82(3)** feeds the *rotated* basis `b i = U |i⟩` from the freedom in purifications
  (`exists_orthonormalBasis_refMeasurement_recovers_ensemble`, below). -/

/-- The **reference basis pure state** `|bᵢ⟩`: the `i`-th vector of an orthonormal basis `b` of the
reference `R = ofModel (EuclideanSpace ℂ (Fin e.card))`, as a `PureState`. It is the
post-measurement state of `R` after outcome `i`, and the right factor of `A`'s recovered product
state. The standard-basis case `b = |i⟩` is `refBasisState`. -/
def basisState (e : Ensemble S)
    (b : OrthonormalBasis (Fin e.card) ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    (i : Fin e.card) : PureState (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))) where
  vec := b i
  normalized := b.orthonormal.norm_eq_one i

@[simp]
theorem basisState_vec (e : Ensemble S)
    (b : OrthonormalBasis (Fin e.card) ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    (i : Fin e.card) : (e.basisState b i).vec = b i := rfl

/-- The **reference basis pure state** `|i⟩` for the standard basis — the `b = |i⟩` case of
`basisState`. -/
def refBasisState (e : Ensemble S) (i : Fin e.card) :
    PureState (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))) :=
  e.basisState (EuclideanSpace.basisFun (Fin e.card) ℂ) i

@[simp]
theorem refBasisState_vec (e : Ensemble S) (i : Fin e.card) :
    (e.refBasisState i).vec = (EuclideanSpace.basisFun (Fin e.card) ℂ) i := rfl

/-- The **reference measurement** `Rᵢ = I_A ⊗ |i⟩⟨i|` (Nielsen–Chuang Exercise 2.82(2)): measure the
reference `R` in its standard basis `|i⟩`. Built as the projective measurement
(`Measurement.ofOrthonormalBasis`) of the reference `EuclideanSpace ℂ (Fin e.card)`, lifted to the
composite `S ⊗ R` on the right factor by `Measurement.onRight`. -/
def refMeasurement (e : Ensemble S) :
    Measurement (Fin e.card) (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))) :=
  (Measurement.ofOrthonormalBasis (EuclideanSpace.basisFun (Fin e.card) ℂ)).onRight S

@[simp]
theorem refMeasurement_op (e : Ensemble S) (i : Fin e.card) :
    e.refMeasurement.op i
      = TensorProduct.mapL (1 : S →L[ℂ] S)
          (InnerProductSpace.rankOne ℂ ((EuclideanSpace.basisFun (Fin e.card) ℂ) i)
            ((EuclideanSpace.basisFun (Fin e.card) ℂ) i)) :=
  rfl

/-- **Measuring the reference in an arbitrary orthonormal basis** collapses a purification vector
`φ.vec = ∑ⱼ √pⱼ |ψⱼ⟩ ⊗ b j` onto its `i`-th term. The measurement `I_A ⊗ |bᵢ⟩⟨bᵢ|` selects
`√pᵢ |ψᵢ⟩ ⊗ bᵢ`; orthonormality of `b` kills every cross term `j ≠ i`. The key identity for both
Exercise 2.82(2) (`b = |i⟩`) and (3) (`b i = U |i⟩`). -/
theorem op_ofOrthonormalBasis_onRight_apply (e : Ensemble S)
    (b : OrthonormalBasis (Fin e.card) ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    (φ : PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))))
    (hφ : φ.vec = ∑ j, (Real.sqrt (e.prob j) : ℂ) • ((e.states j).vec ⊗ₜ[ℂ] b j))
    (i : Fin e.card) :
    ((Measurement.ofOrthonormalBasis b).onRight S).op i φ.vec
      = (Real.sqrt (e.prob i) : ℂ) • ((e.states i).vec ⊗ₜ[ℂ] b i) := by
  -- `erw` first drops `I_A ⊗ |bᵢ⟩⟨bᵢ|` to the raw `TensorProduct.map`, where `map_sum`/`map_tmul`
  -- apply without the composite-space instance diamond.
  rw [Measurement.onRight_op, Measurement.ofOrthonormalBasis_op]
  erw [TensorProduct.mapL_apply]
  rw [hφ, map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · -- `|bᵢ⟩⟨bᵢ|` fixes the `i`-th term (`⟨bᵢ|bᵢ⟩ = 1`).
    rw [map_smul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe, one_apply_eq_self, InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal i i, ite_eq_left rfl, one_smul]
  · -- Cross terms `j ≠ i` vanish: `⟨bᵢ|bⱼ⟩ = 0`.
    intro j _ hj
    rw [map_smul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal i j, ite_eq_right (Ne.symm hj), zero_smul,
      TensorProduct.tmul_zero, smul_zero]

/-- **The post-measurement operation factorizes** for a reference measurement in an arbitrary
orthonormal basis `b`. If `φ` has vector `∑ⱼ √pⱼ |ψⱼ⟩ ⊗ b j`, the un-normalized post-measurement
operator for outcome `i` is `Eᵢ(|φ⟩⟨φ|) = pᵢ · |ψᵢ ⊗ bᵢ⟩⟨ψᵢ ⊗ bᵢ|`. The shared step for
the Born probability and the collapsed state. -/
theorem postOp_ofOrthonormalBasis_onRight (e : Ensemble S)
    (b : OrthonormalBasis (Fin e.card) ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    (φ : PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))))
    (hφ : φ.vec = ∑ j, (Real.sqrt (e.prob j) : ℂ) • ((e.states j).vec ⊗ₜ[ℂ] b j))
    (i : Fin e.card) :
    ContinuousLinearMap.postOp ((Measurement.ofOrthonormalBasis b).onRight S).op φ.toState.op i
      = (e.prob i : ℂ) • ((e.states i).tmul (e.basisState b i)).toState.op := by
  unfold ContinuousLinearMap.postOp
  rw [PureState.toState_op, InnerProductSpace.rankOne_comp,
    ContinuousLinearMap.adjoint_adjoint, InnerProductSpace.comp_rankOne,
    op_ofOrthonormalBasis_onRight_apply e b φ hφ i]
  erw [InnerProductSpace.rankOne_real_sqrt_smul_self (e.prob_nonneg i)]
  rfl

/-- **Exercise 2.82(2)/(3), Born probability (arbitrary basis).** For `φ` with vector
`∑ⱼ √pⱼ |ψⱼ⟩ ⊗ b j`, measuring the reference in the orthonormal basis `b` yields outcome `i` with
probability exactly `pᵢ` — no positivity hypothesis needed. -/
theorem bornProb_ofOrthonormalBasis_onRight (e : Ensemble S)
    (b : OrthonormalBasis (Fin e.card) ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    (φ : PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))))
    (hφ : φ.vec = ∑ j, (Real.sqrt (e.prob j) : ℂ) • ((e.states j).vec ⊗ₜ[ℂ] b j))
    (i : Fin e.card) :
    ((Measurement.ofOrthonormalBasis b).onRight S).bornProb φ.toState i = e.prob i := by
  rw [Measurement.bornProb_eq_re_trace_postOp, postOp_ofOrthonormalBasis_onRight e b φ hφ,
    ContinuousLinearMap.toLinearMap_smul, map_smul, State.trace_op_eq_one, smul_eq_mul, mul_one]
  exact Complex.ofReal_re _

/-- **Exercise 2.82(2)/(3), joint post-measurement state (arbitrary basis).** Conditioned on the
(possible) outcome `i` of measuring the reference in the orthonormal basis `b`, the post-measurement
state of the whole composite `S ⊗ R` is the product `|ψᵢ ⊗ bᵢ⟩⟨ψᵢ ⊗ bᵢ|`. -/
theorem postMeasurement_ofOrthonormalBasis_onRight (e : Ensemble S)
    (b : OrthonormalBasis (Fin e.card) ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    (φ : PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))))
    (hφ : φ.vec = ∑ j, (Real.sqrt (e.prob j) : ℂ) • ((e.states j).vec ⊗ₜ[ℂ] b j))
    (i : Fin e.card)
    (hp : ((Measurement.ofOrthonormalBasis b).onRight S).bornProb φ.toState i ≠ 0) :
    ((Measurement.ofOrthonormalBasis b).onRight S).postMeasurement φ.toState i hp
      = ((e.states i).tmul (e.basisState b i)).toState := by
  have hprob : e.prob i ≠ 0 := (bornProb_ofOrthonormalBasis_onRight e b φ hφ i) ▸ hp
  have hre := bornProb_ofOrthonormalBasis_onRight e b φ hφ i
  rw [Measurement.bornProb_eq_re_trace_postOp] at hre
  apply State.ext
  rw [Measurement.postMeasurement_op]
  unfold ContinuousLinearMap.postState
  rw [hre, postOp_ofOrthonormalBasis_onRight e b φ hφ, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hprob), one_smul]

/-- **Exercise 2.82(2)/(3), post-measurement state of `A` (arbitrary basis).** Conditioned on the
(possible) outcome `i` of measuring the reference in the orthonormal basis `b`, the reduced state of
system `A` is the ensemble pure state `|ψᵢ⟩⟨ψᵢ|`. Tracing out `R` from the joint product state
`|ψᵢ ⊗ bᵢ⟩⟨ψᵢ ⊗ bᵢ|` leaves `|ψᵢ⟩⟨ψᵢ|`. -/
theorem postMeasurement_ofOrthonormalBasis_onRight_reducedLeft (e : Ensemble S)
    (b : OrthonormalBasis (Fin e.card) ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    (φ : PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))))
    (hφ : φ.vec = ∑ j, (Real.sqrt (e.prob j) : ℂ) • ((e.states j).vec ⊗ₜ[ℂ] b j))
    (i : Fin e.card)
    (hp : ((Measurement.ofOrthonormalBasis b).onRight S).bornProb φ.toState i ≠ 0) :
    (((Measurement.ofOrthonormalBasis b).onRight S).postMeasurement φ.toState i hp).reducedLeft
      = (e.states i).toState := by
  rw [postMeasurement_ofOrthonormalBasis_onRight e b φ hφ, PureState.toState_tmul,
    State.reducedLeft_tmul]

/-! #### Exercise 2.82(2): the standard reference basis `|i⟩`

The standard-basis instances (`b = |i⟩`, `φ = e.purify`) of the arbitrary-basis family above:
`purify_vec_sum` (`e.purify.vec = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`) supplies the `hφ` hypothesis. -/

/-- **Exercise 2.82(2): the reference measurement collapses `|AR⟩` onto its `i`-th term** —
`I_A ⊗ |i⟩⟨i|` applied to `|AR⟩ = ∑ⱼ √pⱼ |ψⱼ⟩ ⊗ |j⟩` selects `√pᵢ |ψᵢ⟩ ⊗ |i⟩`. The `b = |i⟩` case of
`op_ofOrthonormalBasis_onRight_apply`. -/
theorem refMeasurement_op_purifyVec (e : Ensemble S) (i : Fin e.card) :
    e.refMeasurement.op i e.purifyVec
      = (Real.sqrt (e.prob i) : ℂ)
          • ((e.states i).vec ⊗ₜ[ℂ] (EuclideanSpace.basisFun (Fin e.card) ℂ) i) :=
  op_ofOrthonormalBasis_onRight_apply e (EuclideanSpace.basisFun (Fin e.card) ℂ) e.purify
    e.purify_vec_sum i

/-- **Exercise 2.82(2): the post-measurement operation factorizes** —
`Eᵢ(ρ_AR) = pᵢ |ψᵢ ⊗ i⟩⟨ψᵢ ⊗ i|`. The `b = |i⟩` case of `postOp_ofOrthonormalBasis_onRight`. -/
theorem postOp_refMeasurement_purify (e : Ensemble S) (i : Fin e.card) :
    ContinuousLinearMap.postOp e.refMeasurement.op e.purify.toState.op i
      = (e.prob i : ℂ) • ((e.states i).tmul (e.refBasisState i)).toState.op :=
  postOp_ofOrthonormalBasis_onRight e (EuclideanSpace.basisFun (Fin e.card) ℂ) e.purify
    e.purify_vec_sum i

/-- **Exercise 2.82(2), Born probability**: measuring `R` in the `|i⟩` basis yields outcome `i` with
probability exactly `pᵢ` (every `i`, no positivity hypothesis). The `b = |i⟩` case of
`bornProb_ofOrthonormalBasis_onRight`. -/
theorem bornProb_refMeasurement_purify (e : Ensemble S) (i : Fin e.card) :
    e.refMeasurement.bornProb e.purify.toState i = e.prob i :=
  bornProb_ofOrthonormalBasis_onRight e (EuclideanSpace.basisFun (Fin e.card) ℂ) e.purify
    e.purify_vec_sum i

/-- **Exercise 2.82(2), joint post-measurement state**: conditioned on the (possible) outcome `i`,
the whole composite `S ⊗ R` collapses to `|ψᵢ ⊗ i⟩⟨ψᵢ ⊗ i|`. The `b = |i⟩` case of
`postMeasurement_ofOrthonormalBasis_onRight`. -/
theorem postMeasurement_refMeasurement_purify (e : Ensemble S) (i : Fin e.card)
    (hp : e.refMeasurement.bornProb e.purify.toState i ≠ 0) :
    e.refMeasurement.postMeasurement e.purify.toState i hp
      = ((e.states i).tmul (e.refBasisState i)).toState :=
  postMeasurement_ofOrthonormalBasis_onRight e (EuclideanSpace.basisFun (Fin e.card) ℂ) e.purify
    e.purify_vec_sum i hp

/-- **Exercise 2.82(2), post-measurement state of `A`**: conditioned on the (possible) outcome `i`,
the reduced state of `A` is exactly `|ψᵢ⟩⟨ψᵢ|`. The `b = |i⟩` case of
`postMeasurement_ofOrthonormalBasis_onRight_reducedLeft`. -/
theorem postMeasurement_refMeasurement_purify_reducedLeft (e : Ensemble S) (i : Fin e.card)
    (hp : e.refMeasurement.bornProb e.purify.toState i ≠ 0) :
    (e.refMeasurement.postMeasurement e.purify.toState i hp).reducedLeft
      = (e.states i).toState :=
  postMeasurement_ofOrthonormalBasis_onRight_reducedLeft e
    (EuclideanSpace.basisFun (Fin e.card) ℂ) e.purify e.purify_vec_sum i hp

/-! #### Exercise 2.82(3): every purification's reference can be measured to recover the ensemble

Part (2) measured the reference of the *canonical* ensemble purification `e.purify` in its
*standard* basis `|i⟩`. Part (3) starts from an **arbitrary** purification `|AR⟩` (`φ`) of `ρ`. By
the freedom in purifications (Exercise 2.81), `|AR⟩ = (I_A ⊗ U) e.purify` for a unitary `U` on the
reference `R`; measuring `R` in the *rotated* basis `|i'⟩ := U |i⟩` then recovers the ensemble, via
the arbitrary-basis family above at `b i = U |i⟩`. -/

/-- **Exercise 2.82(3): every purification's reference can be measured to recover the ensemble.**
Let `|AR⟩` (`φ`) be *any* purification of `ρ` to `S ⊗ R`, `R = ofModel (EuclideanSpace ℂ (Fin
e.card))` — a pure state of `S ⊗ R` with `Tr_R |AR⟩⟨AR| = ρ` (`φ.toState.reducedLeft = e.toState`).
Then there is an orthonormal basis `b` of `R` such that the projective measurement of `R` in `b`
(the composite `I_A ⊗ |bᵢ⟩⟨bᵢ|`) yields outcome `i` with probability `pᵢ` and collapses `A` to
`|ψᵢ⟩⟨ψᵢ|`.

The basis is the standard basis `|i⟩` rotated by the reference unitary `U` relating `φ` to the
canonical ensemble purification `e.purify` (the vector form of Exercise 2.81, freedom in
purifications, `TensorProduct.exists_mem_unitary_mapL_id_eq`): `b i = U |i⟩`. Then
`φ.vec = (I_A ⊗ U) e.purifyVec = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ U |i⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ b i`, so the arbitrary-basis
recovery lemmas (`bornProb_ofOrthonormalBasis_onRight`,
`postMeasurement_ofOrthonormalBasis_onRight_reducedLeft`) apply. The reference unitary is obtained
at the level of state vectors (the statement `PureState.exists_evolution_tmul_id_evolvePure_eq` of
Exercise 2.81 builds on the same Mathlib lemma). -/
theorem exists_orthonormalBasis_refMeasurement_recovers_ensemble (e : Ensemble S)
    (φ : PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))))
    (hφ : φ.toState.reducedLeft = e.toState) :
    ∃ b : OrthonormalBasis (Fin e.card) ℂ
        (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space,
      (∀ i, ((Measurement.ofOrthonormalBasis b).onRight S).bornProb φ.toState i = e.prob i) ∧
        ∀ i (hp : ((Measurement.ofOrthonormalBasis b).onRight S).bornProb φ.toState i ≠ 0),
          (((Measurement.ofOrthonormalBasis b).onRight S).postMeasurement
              φ.toState i hp).reducedLeft = (e.states i).toState := by
  -- Freedom in purifications (vector form): `(I_A ⊗ U) e.purify.vec = φ.vec` for a unitary `U`.
  obtain ⟨Uop, hUmem, hUeq⟩ := TensorProduct.exists_mem_unitary_mapL_id_eq
    (stdOrthonormalBasis ℂ (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space)
    e.purify.vec φ.vec (by
      have hop := congrArg State.op (e.purify_reducedLeft.trans hφ.symm)
      rw [State.reducedLeft_op, State.reducedLeft_op, PureState.toState_op,
        PureState.toState_op] at hop
      exact LinearMap.toContinuousLinearMap.injective hop)
  -- The isometry equivalence of `U` on the reference `R.space`.
  set L : (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space
      ≃ₗᵢ[ℂ] (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space :=
    Unitary.linearIsometryEquiv ⟨Uop, hUmem⟩ with hLdef
  have hLpt : ∀ x, L x = Uop x := by
    intro x
    rw [hLdef]
    rfl
  -- The reference standard basis `|i⟩`, typed at the reference system's space `R.space` (defeq to
  -- `EuclideanSpace`, but syntactically so) so its vectors match the domain of `Uop`/`mapL` and the
  -- distribution `map_sum` below applies. The rotated basis is `b i = U |i⟩` (`bR.map L`).
  set bR : OrthonormalBasis (Fin e.card) ℂ
      (QSystem.ofModel (EuclideanSpace ℂ (Fin e.card))).space :=
    EuclideanSpace.basisFun (Fin e.card) ℂ
  refine ⟨bR.map L, ?_⟩
  have hbi : ∀ i, (bR.map L) i = Uop (bR i) := fun i => by
    rw [OrthonormalBasis.map_apply]; exact hLpt _
  -- `φ.vec = (I_A ⊗ U) e.purify.vec = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ b i`.
  have hvec : φ.vec = ∑ i, (Real.sqrt (e.prob i) : ℂ)
      • ((e.states i).vec ⊗ₜ[ℂ] (bR.map L) i) := by
    -- `purify_vec_sum` is stated over the standard basis in `EuclideanSpace`; here it types against
    -- the `R.space`-typed `bR i` definitionally (`bR := EuclideanSpace.basisFun` by `set`), giving
    -- `map_sum` below a sum whose reference vectors match the domain of `Uop`/`mapL`.
    have hpv : e.purify.vec = ∑ i, (Real.sqrt (e.prob i) : ℂ)
        • ((e.states i).vec ⊗ₜ[ℂ] bR i) := e.purify_vec_sum
    rw [← hUeq]
    -- `erw` (before the sum is exposed) drops `I_A ⊗ U` to the raw `TensorProduct.map`; with the
    -- reference vectors in `R.space`, `map_sum`/`map_smul`/`map_tmul` then apply cleanly.
    erw [TensorProduct.mapL_apply]
    rw [hpv, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe, one_apply_eq_self, hbi]
  exact ⟨fun i => bornProb_ofOrthonormalBasis_onRight e _ φ hvec i,
    fun i hp => postMeasurement_ofOrthonormalBasis_onRight_reducedLeft e _ φ hvec i hp⟩

end Ensemble

end AxQM
