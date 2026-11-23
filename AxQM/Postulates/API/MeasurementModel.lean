/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.ProjectiveMeasurement
import AxQM.Postulates.API.GeneralMeasurementEnvironment
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.Composite
import AxQM.Postulates.PartialTrace
import ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation
import ToMathlib.Analysis.InnerProductSpace.RankOneProjector
import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AxQM — the measurement model of a set of quantum operations (N&C Exercise 8.9)

The **measurement model** of Nielsen–Chuang Exercise 8.9.
Given a set of quantum operations `{Eₘ}` whose sum `∑ₘ Eₘ` is trace preserving, presented flatly by
a family of operation elements `E : ι → (Q →L Q)` (the `E_{mk}` of the exercise) together with a
labelling `out : ι → M` recording which outcome each element belongs to (`out (m,k) = m`), and an
environment `Env` with an orthonormal basis `b : OrthonormalBasis ι ℂ Env` in one-to-one
correspondence with the operation-element indices and a standard unit state `e₀`, this file
constructs the two physical objects the exercise measures:

* `Measurement.ofOrthonormalBasisFiber b out` — the **environment measurement** with block
  projectors `Pₘ = ∑_{out σ = m} |b σ⟩⟨b σ|` (Nielsen–Chuang's `Pₘ ≡ ∑ₖ |m,k⟩⟨m,k|`). This is a
  genuine projective measurement (`Measurement.isProjective_ofOrthonormalBasisFiber`): each `Pₘ` is
  an orthogonal projector (`InnerProductSpace.orthonormalProjector` of an orthonormal family) and
  the `Pₘ` resolve the identity because the fibres of `out` partition the basis.
* `measurementModelEvolution b he₀ E hE` — the **joint unitary** `U` (Nielsen–Chuang eq. (8.40)),
  packaged as an `Evolution (Q ⊗ Env)`. On the standard-ancilla slice it acts as the Stinespring
  dilation `V₀` assembled from the Kraus family, `U (ψ ⊗ e₀) = ∑_σ (E σ ψ) ⊗ (b σ)`
  (`measurementModelEvolution_op_tmul`). It exists as a *unitary* because the trace preservation of
  `∑ₘ Eₘ`, `∑_σ (E σ)† (E σ) = 1`, makes `V₀` an isometry, which extends to a unitary of the joint
  space (N&C Exercise 2.67 / Box 8.1).

Building on that construction, this file proves the substance of Exercise 8.9 — that
measuring `Pₘ` after `U` gives outcome `m` with probability `tr(Eₘ ρ)` and post-measurement state
`Eₘ(ρ)/tr(Eₘ(ρ))`:

* `measurementModelInducedOp E out ρ m` — the **induced operation element** `Eₘ(ρ) = ∑_{out σ = m}
  E_σ ρ E_σ†` on the principal system, collecting the operation elements labelled `m`.
* `measurementModelEnvOp_eq_inducedOp` — the **induced-operation identity**
  `tr_E(Pₘ U (ρ ⊗ |e₀⟩⟨e₀|) U† Pₘ) = Eₘ(ρ)`, obtained by instantiating Exercise 8.7's general
  system–environment induced operation `generalMeasurementEnvOp` at the model's lifted measurement
  `Pₘ ⊗ 1`, unitary `U`, and standard environment state `|e₀⟩⟨e₀|`, and evaluating the projected
  partial trace with the projected environment operator-sum lemma
  `LinearMap.partialTraceRight_conj_sum_proj_eq_sum_krausOp`.
* `measurementModel_bornProb_eq_trace` — **probability:** `p(m) = tr(Eₘ ρ)`, and
* `measurementModel_reducedLeft_postMeasurement_op` — **post-measurement state:** the principal
  system's reduced state after a possible outcome `m` is `Eₘ(ρ)/tr(Eₘ(ρ))`.

The statement of Exercise 8.9, for states, measurements and evolutions, is in
`AxQM/NC/Ch8/Exercise8_9.lean`.

## Construction of the unitary

The unitary reuses the converse-dilation package
(`ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation`):
`LinearMap.exists_unitary_krausDilation`
supplies the unitary extension of the assembled dilation `V₀ = krausDilation b E` (an isometry by
completeness), and `Evolution.ofLinearIsometryEquiv` promotes it to an `Evolution`. The
completeness hypothesis is stated in the physical `ContinuousLinearMap` form `∑_σ (E σ)† (E σ) = 1`
and bridged to the `LinearMap` form that package expects by the general lemma
`ContinuousLinearMap.sum_adjoint_comp_toLinearMap_eq_id`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (System–environment models; Box 8.1; Exercise 8.9).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The environment's block-projective measurement `Pₘ` -/

variable {ι M : Type*} [Fintype ι] [Fintype M] [DecidableEq M] {S : QSystem}

/-- **The block-projective measurement grouped by a labelling** `out : ι → M` of an orthonormal
basis `b` of `S` (Nielsen–Chuang Exercise 8.9's environment measurement `Pₘ ≡ ∑ₖ |m,k⟩⟨m,k|`).
Outcome `m` has measurement operator the orthogonal projector
`Pₘ = ∑_{σ : out σ = m} |b σ⟩⟨b σ|` (`InnerProductSpace.orthonormalProjector` of the sub-family of
basis vectors labelled `m`).

Completeness `∑ₘ Pₘ† Pₘ = 1` holds because each `Pₘ` is a star projection (a self-adjoint
idempotent, `InnerProductSpace.isStarProjection_orthonormalProjector`), so `Pₘ† Pₘ = Pₘ`, and the
fibres of `out` partition the basis (`Finset.sum_fiberwise`), so `∑ₘ Pₘ = ∑_σ |b σ⟩⟨b σ| = 1` is
the resolution of the identity (`OrthonormalBasis.sum_rankOne_eq_id`). -/
def Measurement.ofOrthonormalBasisFiber (b : OrthonormalBasis ι ℂ S) (out : ι → M) :
    Measurement M S where
  op m := orthonormalProjector ℂ (⇑b) (Finset.univ.filter (fun σ => out σ = m))
  complete := by
    set P : Finset ι → (S →L[ℂ] S) := orthonormalProjector ℂ (⇑b) with hP
    have hsq : ∀ s : Finset ι, (adjoint (P s)).comp (P s) = P s := by
      intro s
      have hsp : IsStarProjection (P s) :=
        hP ▸ isStarProjection_orthonormalProjector b.orthonormal s
      rw [← ContinuousLinearMap.star_eq_adjoint, hsp.isSelfAdjoint.star_eq,
        ← ContinuousLinearMap.mul_def]
      exact hsp.isIdempotentElem
    calc ∑ m, (adjoint (P (Finset.univ.filter (fun σ => out σ = m)))).comp
            (P (Finset.univ.filter (fun σ => out σ = m)))
        = ∑ m, P (Finset.univ.filter (fun σ => out σ = m)) :=
          Finset.sum_congr rfl fun m _ => hsq _
      _ = ∑ σ, rankOne ℂ (b σ) (b σ) := by
          rw [hP]; exact Finset.sum_fiberwise Finset.univ out (fun σ => rankOne ℂ (b σ) (b σ))
      _ = 1 := by rw [b.sum_rankOne_eq_id, ← ContinuousLinearMap.one_def]

@[simp]
theorem Measurement.ofOrthonormalBasisFiber_op (b : OrthonormalBasis ι ℂ S) (out : ι → M) (m : M) :
    (Measurement.ofOrthonormalBasisFiber b out).op m
      = orthonormalProjector ℂ (⇑b) (Finset.univ.filter (fun σ => out σ = m)) := rfl

/-- The environment measurement `Measurement.ofOrthonormalBasisFiber b out` is **projective** (von
Neumann): each block operator `Pₘ` is an orthogonal projector
(`InnerProductSpace.isStarProjection_orthonormalProjector`), which is exactly the defining condition
`Measurement.IsProjective`. -/
theorem Measurement.isProjective_ofOrthonormalBasisFiber (b : OrthonormalBasis ι ℂ S)
    (out : ι → M) : (Measurement.ofOrthonormalBasisFiber b out).IsProjective := fun m =>
  isStarProjection_orthonormalProjector b.orthonormal (Finset.univ.filter (fun σ => out σ = m))

/-! ### The two-outcome measurement `{P, 1 − P}` of an orthogonal projector -/

/-- **The two-outcome von Neumann measurement `{P, 1 − P}` of an orthogonal projector** `P`
(`hP : IsStarProjection P`): outcome `true` has measurement operator `P` and outcome `false` has
`1 − P`. Completeness `∑_b Mᵦ† Mᵦ = 1` holds because both `P` and `1 − P` are star projections
(`IsStarProjection.one_sub`), so `Mᵦ† Mᵦ = Mᵦ` and `P + (1 − P) = 1`. This is the faithful reading
of "measure whether the state lies in the subspace `range P`", and gives a `Measurement` from an
arbitrary projector — the projector-indexed sibling of `Measurement.ofOrthonormalBasisFiber`. -/
def Measurement.ofStarProjection (P : S.space →L[ℂ] S.space) (hP : IsStarProjection P) :
    Measurement Bool S where
  op b := cond b P (1 - P)
  complete := by
    have key : ∀ Q : S.space →L[ℂ] S.space, IsStarProjection Q →
        (adjoint Q).comp Q = Q := fun Q hQ => by
      rw [hQ.isSelfAdjoint.adjoint_eq, ← ContinuousLinearMap.mul_def]
      exact hQ.isIdempotentElem
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, key _ hP, key _ hP.one_sub]
    abel

@[simp]
theorem Measurement.ofStarProjection_op_true (P : S.space →L[ℂ] S.space)
    (hP : IsStarProjection P) : (Measurement.ofStarProjection P hP).op true = P := rfl

@[simp]
theorem Measurement.ofStarProjection_op_false (P : S.space →L[ℂ] S.space)
    (hP : IsStarProjection P) : (Measurement.ofStarProjection P hP).op false = 1 - P := rfl

/-- The measurement `Measurement.ofStarProjection P hP` is **projective** (von Neumann): both
outcome operators `P` and `1 − P` are star projections. -/
theorem Measurement.isProjective_ofStarProjection (P : S.space →L[ℂ] S.space)
    (hP : IsStarProjection P) : (Measurement.ofStarProjection P hP).IsProjective := by
  rintro (_ | _)
  · exact hP.one_sub
  · exact hP

/-- **Born-rule bridge for `{P, 1 − P}`**: on any state `τ`, the probability of outcome `true`
(landing in `range P`) is `re tr(P τ)`. Proof: `bornProb = re tr(P† P τ)`
(`bornProb_eq_re_trace_postOp`, `trace_postOp`), and `P† P = P` since `P` is a self-adjoint
idempotent. -/
theorem Measurement.bornProb_ofStarProjection_true (P : S.space →L[ℂ] S.space)
    (hP : IsStarProjection P) (τ : State S) :
    (Measurement.ofStarProjection P hP).bornProb τ true
      = RCLike.re ((LinearMap.trace ℂ S.space)
          ((P.comp τ.op : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) := by
  have hPP : P.comp P = P := by rw [← ContinuousLinearMap.mul_def]; exact hP.isIdempotentElem
  rw [Measurement.bornProb_eq_re_trace_postOp, ContinuousLinearMap.trace_postOp,
    Measurement.ofStarProjection_op_true, hP.isSelfAdjoint.adjoint_eq,
    ← ContinuousLinearMap.comp_assoc, hPP]

/-! ### The joint unitary of the measurement model -/

variable {Q Env : QSystem}

/-- **The joint unitary of the measurement model** (Nielsen–Chuang Exercise 8.9, eq. (8.40)). From
a family of operation elements `E : ι → (Q →L Q)` for a trace-preserving `∑ₘ Eₘ`
(`hE : ∑_σ (E σ)† (E σ) = 1`), an orthonormal environment basis `b` in one-to-one correspondence
with the indices, and a standard unit environment state `e₀`, the joint dynamics is the unitary `U`
acting as `U (ψ ⊗ e₀) = ∑_σ (E σ ψ) ⊗ (b σ)` (`measurementModelEvolution_op_tmul`), packaged as an
`Evolution (Q ⊗ Env)`.

It is genuinely unitary: the Stinespring dilation `V₀ = krausDilation b E` is an isometry (by the
completeness `hE`), and an isometry defined on the standard-ancilla slice extends to a unitary of
the joint space (N&C Exercise 2.67; the block-matrix freedom of Box 8.1). Obtained from
`LinearMap.exists_unitary_krausDilation` (the unitary extension) promoted to an
`Evolution` by `Evolution.ofLinearIsometryEquiv`. -/
def measurementModelEvolution (b : OrthonormalBasis ι ℂ Env) {e₀ : Env.space} (he₀ : ‖e₀‖ = 1)
    (E : ι → (Q →L[ℂ] Q)) (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1) :
    Evolution (Q ⊗ Env) :=
  Evolution.ofLinearIsometryEquiv
    (LinearMap.exists_unitary_krausDilation b (fun σ => (E σ).toLinearMap)
      (ContinuousLinearMap.sum_adjoint_comp_toLinearMap_eq_id E hE) he₀).choose

/-- **The joint unitary on the standard-ancilla slice** (Nielsen–Chuang Exercise 8.9, eq. (8.40)):
`U (ψ ⊗ e₀) = ∑_σ (E σ ψ) ⊗ (b σ)`. This is the defining action `V₀` of the measurement model — the
Stinespring dilation assembled from the Kraus family — and the key identity the induced-operation
computation is built on. Immediate from the defining property of the unitary extension
(`LinearMap.exists_unitary_krausDilation`) and `LinearMap.krausDilation_apply`. -/
theorem measurementModelEvolution_op_tmul (b : OrthonormalBasis ι ℂ Env) {e₀ : Env.space}
    (he₀ : ‖e₀‖ = 1) (E : ι → (Q →L[ℂ] Q)) (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1) (ψ : Q) :
    (measurementModelEvolution b he₀ E hE).op (ψ ⊗ₜ[ℂ] e₀) = ∑ σ, E σ ψ ⊗ₜ[ℂ] b σ := by
  have hex := LinearMap.exists_unitary_krausDilation b (fun σ => (E σ).toLinearMap)
    (ContinuousLinearMap.sum_adjoint_comp_toLinearMap_eq_id E hE) he₀
  -- Name the isometry at the *bundled* `(Q ⊗ Env).space` type via a `let` (rather than an inline
  -- ascription, which does not stick): `measurementModelEvolution` unfolds to
  -- `Evolution.ofLinearIsometryEquiv hex.choose`, but `hex.choose`'s own natural type carries the
  -- *generic* `Q.space ⊗[ℂ] Env.space` instances, so `rw`'s syntactic pattern matching against
  -- `Evolution.ofLinearIsometryEquiv_op_apply`'s bundled-`S.space` pattern cannot fire directly on
  -- the unfolded definition. A `let`-bound name declared at the bundled type is `zeta`-transparent,
  -- so the following `rfl` (checked at full elaboration transparency, unlike `rw`) can still bridge
  -- it back to `hex.choose`.
  let L₀ : (Q ⊗ Env).space ≃ₗᵢ[ℂ] (Q ⊗ Env).space := hex.choose
  -- The argument `ψ ⊗ₜ[ℂ] e₀` is itself typed at the *generic* `Q.space ⊗[ℂ] Env.space`, so `rw`'s
  -- pattern for `Evolution.ofLinearIsometryEquiv_op_apply` (needing a syntactically bundled
  -- argument) cannot fire on it either; instantiate the lemma directly (an ordinary application,
  -- checked up to full defeq) instead of `rw`-matching it.
  have hop_apply := Evolution.ofLinearIsometryEquiv_op_apply L₀ (ψ ⊗ₜ[ℂ] e₀)
  rw [show measurementModelEvolution b he₀ E hE = Evolution.ofLinearIsometryEquiv L₀ from rfl,
    hop_apply]
  have hspec := hex.choose_spec ψ
  rw [LinearMap.krausDilation_apply] at hspec
  simp only [ContinuousLinearMap.coe_coe] at hspec
  exact hspec

/-! ### The induced operation and the measurement-model identities

With the two physical objects of the model in hand — the environment block-projective measurement
`Pₘ` (`Measurement.ofOrthonormalBasisFiber`) and the joint unitary `U` (`measurementModelEvolution`)
— this section discharges what Exercise 8.9 asks to *show*: performing `U` on `ρ ⊗ |e₀⟩⟨e₀|` and
then measuring `Pₘ` on the environment induces the operation `Eₘ(ρ) = ∑_{out σ = m} E_σ ρ E_σ†`,
with outcome probability `tr(Eₘ ρ)` and post-measurement principal state `Eₘ(ρ)/tr(Eₘ ρ)`.

The induced operation is obtained by *instantiating* Exercise 8.7's general system–environment
machinery (`generalMeasurementEnvOp`, `bornProb_eq_trace_generalMeasurementEnvOp`) at the model's
lifted measurement `Pₘ ⊗ 1` (`Measurement.onRight`), the model unitary `U`, and the standard
environment state `|e₀⟩⟨e₀|`, then evaluating the resulting partial trace with the projected
environment operator-sum lemma `LinearMap.partialTraceRight_conj_sum_proj_eq_sum_krausOp`. -/

/-- **The `m`-th induced operation element of the measurement model** (Nielsen–Chuang Exercise 8.9):
`Eₘ(ρ) = ∑_{out σ = m} E_σ ρ E_σ†`, the quantum operation `Eₘ` of the labelled Kraus family applied
to the principal state `ρ`, collecting exactly the operation elements `E_σ` whose outcome label is
`m` (N&C's `Eₘ(ρ) = ∑ₖ E_{mk} ρ E_{mk}†`). -/
def measurementModelInducedOp (E : ι → (Q →L[ℂ] Q)) (out : ι → M) (ρ : State Q) (m : M) :
    Q →L[ℂ] Q :=
  ∑ σ ∈ Finset.univ.filter (fun σ => out σ = m), (E σ).comp (ρ.op.comp (adjoint (E σ)))

/-- **The induced-operation identity of the measurement model** (Nielsen–Chuang Exercise 8.9): the
general system–environment induced operation of Exercise 8.7 (`generalMeasurementEnvOp`), evaluated
at the model's lifted environment measurement `Pₘ ⊗ 1` (`Measurement.ofOrthonormalBasisFiber b out`
on the right, `Measurement.onRight`), its joint unitary `U = measurementModelEvolution`, and the
standard environment state `|e₀⟩⟨e₀|`, equals the `m`-th induced operation element `Eₘ(ρ)`:

  `tr_E(Pₘ U (ρ ⊗ |e₀⟩⟨e₀|) U† Pₘ) = ∑_{out σ = m} E_σ ρ E_σ†`.

Proof: rewrite the Exercise 8.2 operation element of the lifted (self-adjoint) measurement `Pₘ ⊗ 1`
on the evolved state into the projector-conjugated ancilla form
`P_S (U (ρ ⊗ |e₀⟩⟨e₀|) U†) P_S`, with `P_S = ∑_{out σ = m} embedRight b σ ∘ₗ restrictRight b σ` the
environment block projector (`hPm`, `hMsa`); switch the partial trace to the basis `b`
(`LinearMap.partialTraceRight_eq_of_basis`), then apply the projected-and-ancilla
operator-sum lemma `LinearMap.partialTraceRight_conj_sum_proj_map_rankOne_eq_sum_krausOp`, whose
elements `krausOp b (U.op ∘ (·⊗e₀)) σ = E_σ` are read off from
`measurementModelEvolution_op_tmul`/`LinearMap.krausOp_krausDilation`. The underlying operator of
the unitary is pinned to a single representative `U₀` throughout so the composite-system space
`(Q ⊗ Env).space` and the plain tensor `Q.space ⊗ Env.space` never diverge under `rw`. -/
theorem measurementModelEnvOp_eq_inducedOp (b : OrthonormalBasis ι ℂ Env) {e₀ : Env.space}
    (he₀ : ‖e₀‖ = 1) (E : ι → (Q →L[ℂ] Q)) (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1)
    (out : ι → M) (ρ : State Q) (m : M) :
    generalMeasurementEnvOp ((Measurement.ofOrthonormalBasisFiber b out).onRight Q)
        (measurementModelEvolution b he₀ E hE) (⟨e₀, he₀⟩ : PureState Env).toState ρ m
      = measurementModelInducedOp E out ρ m := by
  -- Pin one representative `U₀` of the unitary's underlying operator so the composite-system
  -- space `(Q ⊗ Env).space` and the raw tensor `Q.space ⊗ Env.space` never diverge under `rw`.
  set U₀ : Q.space ⊗[ℂ] Env.space →ₗ[ℂ] Q.space ⊗[ℂ] Env.space :=
    (measurementModelEvolution b he₀ E hE).op.toLinearMap with hU₀
  clear_value U₀
  -- The lifted environment measurement `Pₘ ⊗ 1` is the block projector
  -- `P_S = ∑_{out σ = m} embedRight b σ ∘ₗ restrictRight b σ`.
  have hPm : (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).op m).toLinearMap
      = ∑ σ ∈ Finset.univ.filter (fun σ => out σ = m),
          LinearMap.embedRight b σ ∘ₗ LinearMap.restrictRight b σ := by
    rw [Measurement.onRight_op, Measurement.ofOrthonormalBasisFiber_op,
        TensorProduct.toLinearMap_mapL, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
        InnerProductSpace.orthonormalProjector, ContinuousLinearMap.toLinearMap_sum]
    simp only [LinearMap.embedRight_comp_restrictRight_eq_map_rankOne,
      ← TensorProduct.mapBilinear_apply, map_sum]
    rfl
  -- The lifted measurement operator `Pₘ ⊗ 1` is self-adjoint (a real, self-adjoint projector):
  -- its underlying operator is the block projector, whose Hermiticity is the lemma
  -- `LinearMap.adjoint_sum_embedRight_comp_restrictRight` (bridged over the mixed composite space
  -- to the plain tensor by `exact`/defeq). `ContinuousLinearMap.adjoint_toLinearMap` is now the
  -- upstream lemma in the opposite orientation; `_of_completeSpace` keeps the original orientation
  -- (`ToMathlib.Analysis.InnerProductSpace.Adjoint`).
  have hMsa : adjoint (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).op m)
      = ((Measurement.ofOrthonormalBasisFiber b out).onRight Q).op m := by
    refine ContinuousLinearMap.coe_injective ?_
    rw [ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace, hPm]
    exact LinearMap.adjoint_sum_embedRight_comp_restrictRight b _
  -- The underlying linear map of `U.op†` is the linear-map adjoint of the pinned representative
  -- `U₀`.
  have hUadj : (adjoint (measurementModelEvolution b he₀ E hE).op).toLinearMap
      = LinearMap.adjoint U₀ := by
    rw [hU₀]
    exact ContinuousLinearMap.adjoint_toLinearMap _
  -- The Stinespring dilation `V₀ = U.op ∘ (·⊗e₀) = krausDilation b E`, so `krausOp b V₀ σ = E_σ`.
  have hUV : U₀ ∘ₗ LinearMap.tmulRightVec e₀
      = LinearMap.krausDilation b (fun σ => (E σ).toLinearMap) := by
    rw [hU₀]
    refine LinearMap.ext fun ψ => ?_
    change (measurementModelEvolution b he₀ E hE).op (ψ ⊗ₜ[ℂ] e₀)
        = LinearMap.krausDilation b (fun σ => (E σ).toLinearMap) ψ
    rw [measurementModelEvolution_op_tmul, LinearMap.krausDilation_apply]
    simp only [ContinuousLinearMap.coe_coe]
    rfl
  -- Pin the generic-typed operation element of the lifted measurement on the evolved state via a
  -- `let` (rather than an inline ascription, which does not stick, or unfolding
  -- `generalMeasurementEnvOp` directly, whose own definition-site type ascription similarly does
  -- not survive delta-unfolding): `Xgeneric`'s *declared* type is the plain tensor, so both the
  -- later `LinearMap.partialTraceRight_eq_of_basis` rewrite and `hbridge` below can fire by
  -- ordinary syntactic matching against this name, with `rfl`/`show` (full transparency, not `rw`'s
  -- restricted matching) doing the actual bundled-vs-generic bridging.
  let Xgeneric : Q.space ⊗[ℂ] Env.space →ₗ[ℂ] Q.space ⊗[ℂ] Env.space :=
    (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).opElement
        ((measurementModelEvolution b he₀ E hE).evolve
          (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m).toLinearMap
  have hgen : generalMeasurementEnvOp ((Measurement.ofOrthonormalBasisFiber b out).onRight Q)
      (measurementModelEvolution b he₀ E hE) (⟨e₀, he₀⟩ : PureState Env).toState ρ m
    = (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ Env.space) Xgeneric).toContinuousLinearMap
    := rfl
  -- The Exercise 8.2 operation element of the lifted measurement on the evolved state, as a
  -- projector-conjugated ancilla dilation `P_S (U (ρ ⊗ |e₀⟩⟨e₀|) U†) P_S`. `.toLinearMap` is
  -- distributed *fully*, over the still-entirely-bundled `(Q ⊗ Env).space` composite, *before*
  -- `State.tmul_op` ever introduces the generic-instanced `TensorProduct.mapL ρ.op σ.op` term:
  -- doing
  -- the generic swap first would leave it sitting next to the still-bundled `adjoint U.op` inside a
  -- `∘L`/`∘ₗ` node whose own implicit instance args were already fixed (bundled) when that node was
  -- built, blocking any further `ContinuousLinearMap.toLinearMap_comp` match on that node. Once
  -- fully
  -- distributed, every atomic bundled leaf is isolated (no `.comp` sibling left to conflict with),
  -- so
  -- `State.tmul_op`/`PureState.toState_op`/`TensorProduct.toLinearMap_mapL`/`hUadj`/`hPm`/`← hU₀`
  -- can
  -- each rewrite its own leaf in place by ordinary syntactic matching.
  have hbridge : Xgeneric
      = (∑ σ ∈ Finset.univ.filter (fun σ => out σ = m),
            LinearMap.embedRight b σ ∘ₗ LinearMap.restrictRight b σ) ∘ₗ
          (U₀ ∘ₗ
            TensorProduct.map ρ.op.toLinearMap (InnerProductSpace.rankOne ℂ e₀ e₀).toLinearMap ∘ₗ
            LinearMap.adjoint U₀) ∘ₗ
          (∑ σ ∈ Finset.univ.filter (fun σ => out σ = m),
            LinearMap.embedRight b σ ∘ₗ LinearMap.restrictRight b σ) := by
    change (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).opElement
        ((measurementModelEvolution b he₀ E hE).evolve
          (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m).toLinearMap = _
    rw [Measurement.opElement_eq_postOp, ContinuousLinearMap.postOp, hMsa, Evolution.evolve_op]
    simp only [ContinuousLinearMap.toLinearMap_comp]
    rw [State.tmul_op, PureState.toState_op, TensorProduct.toLinearMap_mapL, hUadj, hPm, ← hU₀]
    rfl
  -- The projected environment operator-sum lemma, with `W = U₀` supplied explicitly.
  have hfork := LinearMap.partialTraceRight_conj_sum_proj_map_rankOne_eq_sum_krausOp
    b U₀ e₀ ρ.op.toLinearMap (Finset.univ.filter (fun σ => out σ = m))
  refine ContinuousLinearMap.coe_injective ?_
  rw [hgen, LinearMap.coe_toContinuousLinearMap,
      LinearMap.partialTraceRight_eq_of_basis (stdOrthonormalBasis ℂ Env.space) b, hbridge]
  refine hfork.trans ?_
  simp only [hUV, LinearMap.krausOp_krausDilation, measurementModelInducedOp,
    ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace]

/-- **Nielsen & Chuang, Exercise 8.9 (outcome probability).** Performing `U` on `ρ ⊗ |e₀⟩⟨e₀|` and
then measuring the environment block projector `Pₘ` gives outcome `m` with probability the trace of
the induced operation element, `p(m) = tr(Eₘ ρ)`. Stated as the complex equality
`(p(m) : ℂ) = tr(Eₘ ρ)`, which records both that the trace is real and that it equals the Born
probability. Immediate from Exercise 8.7's `bornProb_eq_trace_generalMeasurementEnvOp` and the
induced-operation identity `measurementModelEnvOp_eq_inducedOp`. -/
theorem measurementModel_bornProb_eq_trace (b : OrthonormalBasis ι ℂ Env) {e₀ : Env.space}
    (he₀ : ‖e₀‖ = 1) (E : ι → (Q →L[ℂ] Q)) (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1)
    (out : ι → M) (ρ : State Q) (m : M) :
    (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).bornProb
        ((measurementModelEvolution b he₀ E hE).evolve
          (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m : ℂ)
      = LinearMap.trace ℂ Q.space
          (measurementModelInducedOp E out ρ m : Q.space →ₗ[ℂ] Q.space) := by
  rw [bornProb_eq_trace_generalMeasurementEnvOp, measurementModelEnvOp_eq_inducedOp]

/-- **Nielsen & Chuang, Exercise 8.9 (post-measurement state).** The corresponding post-measurement
state of the *principal* system — the left marginal (`State.reducedLeft`, tracing out the
environment) of the normalized post-measurement joint state `M.postMeasurement …` — is the induced
operation element normalized by its trace, `Eₘ(ρ)/tr(Eₘ ρ)` (N&C's `Eₘ(ρ)/tr(Eₘ(ρ))`), whenever the
outcome is possible (`hp : p(m) ≠ 0`). Proof: the reduced post-measurement operator is
`(p(m) : ℂ)⁻¹ • Eₘ(ρ)` — pushing the `p(m)⁻¹` scale of the collapse
(`postMeasurement_op_eq_bornProb_smul_opElement`) through the (linear) partial trace to recover the
induced operation `generalMeasurementEnvOp = Eₘ(ρ)` (`measurementModelEnvOp_eq_inducedOp`) — and
`p(m) = tr(Eₘ ρ)` (`measurementModel_bornProb_eq_trace`). -/
theorem measurementModel_reducedLeft_postMeasurement_op (b : OrthonormalBasis ι ℂ Env)
    {e₀ : Env.space} (he₀ : ‖e₀‖ = 1) (E : ι → (Q →L[ℂ] Q))
    (hE : ∑ σ, (adjoint (E σ)).comp (E σ) = 1) (out : ι → M) (ρ : State Q) (m : M)
    (hp : ((Measurement.ofOrthonormalBasisFiber b out).onRight Q).bornProb
      ((measurementModelEvolution b he₀ E hE).evolve
        (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m ≠ 0) :
    (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).postMeasurement
        ((measurementModelEvolution b he₀ E hE).evolve
          (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m hp).reducedLeft.op
      = (LinearMap.trace ℂ Q.space (measurementModelInducedOp E out ρ m : Q.space →ₗ[ℂ] Q.space))⁻¹
          • measurementModelInducedOp E out ρ m := by
  have hgen : (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).postMeasurement
        ((measurementModelEvolution b he₀ E hE).evolve
          (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m hp).reducedLeft.op
      = (((Measurement.ofOrthonormalBasisFiber b out).onRight Q).bornProb
          ((measurementModelEvolution b he₀ E hE).evolve
            (ρ ⊗ (⟨e₀, he₀⟩ : PureState Env).toState)) m : ℂ)⁻¹
          • generalMeasurementEnvOp ((Measurement.ofOrthonormalBasisFiber b out).onRight Q)
              (measurementModelEvolution b he₀ E hE) (⟨e₀, he₀⟩ : PureState Env).toState ρ m := by
    refine ContinuousLinearMap.coe_injective ?_
    rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap,
        Measurement.postMeasurement_op_eq_bornProb_smul_opElement,
            ContinuousLinearMap.toLinearMap_smul,
        generalMeasurementEnvOp, ContinuousLinearMap.toLinearMap_smul,
            LinearMap.coe_toContinuousLinearMap]
    exact LinearMap.partialTraceRight_smul _ _ _
  rw [hgen, measurementModelEnvOp_eq_inducedOp, measurementModel_bornProb_eq_trace]

end AxQM
