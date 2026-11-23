/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementOperation
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# AxQM — reduced operation of a general measurement on system + environment (N&C Ex 8.7)

The reduced operation behind **Nielsen–Chuang Exercise 8.7**. In §8.2.4 a principal system
`Q` (state `ρ`) is adjoined to an environment `E` (state `σ`), the pair interacts via a unitary `U`,
and a measurement is performed on the *combined* system `Q ⊗ E`. Where N&C's worked derivation
(eqs. (8.29)–(8.35)) uses a **projective** measurement `{Pₘ}`, Exercise 8.7 replaces it with a
**general** measurement `{Mₘ}` (`∑ₘ Mₘ† Mₘ = 1`, our `Measurement`) and asks for

* the **quantum operation** `Eₘ` induced on the principal system, in operator-sum form; and
* that the outcome **probabilities** are `tr[Eₘ(ρ)]`.

This file introduces the induced operation, settles the probability claim, and gives the
operator-sum representation (both of Exercise 8.7's asks).

## The induced operation

Tracing out the environment after the interaction and the (unnormalized) measurement of outcome `m`
gives the map on the principal system

  `Eₘ(ρ) = tr_E( Mₘ (U (ρ ⊗ σ) U†) Mₘ† )`   (N&C eq. (8.32), generalized from `Pₘ` to `Mₘ`),

whose normalization `Eₘ(ρ)/tr[Eₘ(ρ)]` is the final state of `Q` alone and whose trace `tr[Eₘ(ρ)]`
is the probability of outcome `m`. Here the inner conjugation is the Exercise 8.2 operation element
`Measurement.opElement M (U.evolve (ρ ⊗ σ)) m = Mₘ (U (ρ ⊗ σ) U†) Mₘ†` of the *lifted* measurement,
and `tr_E` is the partial trace over the right (environment) factor — exactly the partial
trace used by `State.reducedLeft`.

## Contents

* `generalMeasurementEnvOp` — the induced operation `Eₘ(ρ) = tr_E(Mₘ (U (ρ ⊗ σ) U†) Mₘ†)`, as a
  `Q →L[ℂ] Q`.
* `bornProb_eq_trace_generalMeasurementEnvOp` — **Exercise 8.7 (probabilities):** the outcome
  probability equals the trace of the induced operation, `(p(m) : ℂ) = tr[Eₘ(ρ)]`. Stated as the
  complex equality (so the trace is real and equals the Born probability), for the general
  measurement `M` on the post-interaction joint state `U.evolve (ρ ⊗ σ)`.
* `generalMeasurementEnvKrausOp` — the operation elements `Eⱼₖ = ⟨eₖ| Mₘ U |wⱼ⟩` (N&C's
  `Eⱼₖ = √qⱼ ⟨eₖ| Mₘ U |j⟩` of Eq. (8.35), the weights absorbed into `wⱼ`).
* `generalMeasurementEnvOp_eq_sum_krausOp` — **Exercise 8.7 (operator-sum representation):** for an
  ensemble decomposition `σ = ∑ⱼ |wⱼ⟩⟨wⱼ|`, `Eₘ(ρ) = ∑ⱼ ∑ₖ Eⱼₖ ρ Eⱼₖ†` (N&C Eqs. (8.33)–(8.35)).
* `generalMeasurementEnvOp_exists_operatorSum` — the existence form: `Eₘ` admits *some* operator-sum
  representation `Eₘ(ρ) = ∑ᵢ Fᵢ ρ Fᵢ†` (the decomposition supplied by positivity of `σ.op`).

The statement of Exercise 8.7 (the induced outcome distribution and the normalized final state)
is in `AxQM/NC/Ch8/Exercise8_7.lean`.

## Design notes

* **Generality.** `Q`, `E`, `ρ`, `σ`, `U`, `M` are all arbitrary — an arbitrary
  environment state `σ` (not a pure/standard state), an arbitrary unitary interaction, and an
  arbitrary *general* measurement (`Measurement`, whose completeness `∑ₘ Mₘ† Mₘ = 1` is precisely
  N&C's "measurement operators `{Mₘ}`"). Replacing N&C's projectors `Pₘ` by general `Mₘ` is exactly
  the exercise; nothing is specialized to the projective case. `Eₘ(ρ)` is the *unnormalized* reduced
  operation, matching N&C's `Eₘ(ρ) ≡ tr_E(Pₘ U(ρ ⊗ σ)U† Pₘ)` with `Pₘ ↦ Mₘ`, so its trace is
  literally the outcome probability (not a surrogate).
* **Why the operation is defined via `opElement`.** The middle factor `Mₘ (U (ρ ⊗ σ) U†) Mₘ†` is the
  Exercise 8.2 operation element of the lifted general measurement on the evolved joint state, so
  `generalMeasurementEnvOp` is the partial trace of that already-grounded object. This makes the
  probability proof a two-step bridge: the trace of a partial trace is the full trace
  (`LinearMap.trace_partialTraceRight`), and the full trace of `Mₘ τ Mₘ†` is the Born probability
  (`Measurement.bornProb_eq_trace_opElement`, Exercise 8.2).
* **Proof shape.** `bornProb_eq_trace_generalMeasurementEnvOp` rewrites the Born probability of the
  lifted measurement on `U.evolve (ρ ⊗ σ)` to `tr((Q ⊗ E)) (Mₘ τ Mₘ†)` (Exercise 8.2), unfolds
  `generalMeasurementEnvOp`, and collapses `tr_Q (tr_E(·)) = tr_{Q ⊗ E}(·)` via
  `LinearMap.trace_partialTraceRight`; the two traces agree definitionally because
  `(Q ⊗ E).space` is `Q.space ⊗[ℂ] E.space`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {Q E : QSystem}

/-- **The induced quantum operation of a general measurement on system + environment** (Nielsen–
Chuang Exercise 8.7, eq. (8.32) with the projectors `Pₘ` replaced by general measurement operators
`Mₘ`):

  `Eₘ(ρ) = tr_E( Mₘ (U (ρ ⊗ σ) U†) Mₘ† )`,

the map on the principal system `Q` obtained by preparing the joint state `ρ ⊗ σ`, applying the
system–environment interaction `U`, measuring the combined system with outcome `m`, and tracing out
the environment `E`. The inner conjugation is the Exercise 8.2 operation element
`Measurement.opElement M (U.evolve (ρ ⊗ σ)) m = Mₘ (U (ρ ⊗ σ) U†) Mₘ†`; `tr_E` is the partial trace
over the right (environment) factor. Its trace is the outcome probability
(`bornProb_eq_trace_generalMeasurementEnvOp`) and its normalization `Eₘ(ρ)/tr[Eₘ(ρ)]` is the final
state of `Q` alone. Defined as the partial trace of a raw operator. -/
def generalMeasurementEnvOp (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) : Q →L[ℂ] Q :=
  (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ E.space)
    ((M.opElement (U.evolve (ρ ⊗ σ)) m).toLinearMap
      : Q.space ⊗[ℂ] E.space →ₗ[ℂ] Q.space ⊗[ℂ] E.space)).toContinuousLinearMap

/-- **Nielsen & Chuang, Exercise 8.7 (probabilities).** The probability of outcome `m` — the Born
probability of the general measurement `M` on the post-interaction joint state `U.evolve (ρ ⊗ σ)` —
equals the trace of the induced operation:

  `(p(m) : ℂ) = tr[Eₘ(ρ)]`.

Stated as the complex equality (which records both that `tr[Eₘ(ρ)]` is real and that it equals the
Born probability), for an arbitrary system, environment, state, environment state, interaction, and
outcome. Proof: `Measurement.bornProb_eq_trace_opElement` (Exercise 8.2) rewrites `(p(m) : ℂ)` to
the full trace `tr_{Q ⊗ E}(Mₘ (U (ρ ⊗ σ) U†) Mₘ†)`, and `LinearMap.trace_partialTraceRight`
collapses `tr[Eₘ(ρ)] = tr_Q(tr_E(·))` to that same full trace (the two spaces agree
definitionally). -/
theorem bornProb_eq_trace_generalMeasurementEnvOp (M : Measurement ι (Q ⊗ E))
    (U : Evolution (Q ⊗ E)) (σ : State E) (ρ : State Q) (m : ι) :
    (M.bornProb (U.evolve (ρ ⊗ σ)) m : ℂ)
      = LinearMap.trace ℂ Q.space (generalMeasurementEnvOp M U σ ρ m : Q.space →ₗ[ℂ] Q.space) := by
  rw [Measurement.bornProb_eq_trace_opElement, generalMeasurementEnvOp,
    LinearMap.coe_toContinuousLinearMap]
  erw [LinearMap.trace_partialTraceRight]
  rfl

/-- **The operation elements of Exercise 8.7's operator-sum representation.** Given an ensemble
decomposition `σ = ∑ⱼ |wⱼ⟩⟨wⱼ|` of the environment state (the ensemble weights `√qⱼ` absorbed into
the vectors `wⱼ`, so `wⱼ = √qⱼ |j⟩` in N&C's notation) and the fixed environment orthonormal basis
`{eₖ}` (`stdOrthonormalBasis ℂ E.space`), the `(j, k)`-th operation element is

  `Eⱼₖ = ⟨eₖ| Mₘ U |wⱼ⟩`,

Nielsen–Chuang's `Eⱼₖ = √qⱼ ⟨eₖ| Mₘ U |j⟩` of Eq. (8.35), generalized from the projectors `Pₘ` to
the general measurement operators `Mₘ`. Concretely it is the `k`-th Kraus operator
(`LinearMap.krausOp`) of the dilation `(Mₘ U) ∘ (· ⊗ wⱼ) : Q.space →ₗ Q.space ⊗ E.space`, i.e. apply
`Mₘ U` to the input tensored with `wⱼ` and contract the environment factor against `eₖ`.
A raw operator built from the measurement and the evolution. -/
def generalMeasurementEnvKrausOp (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    {κ : Type*} (w : κ → E.space) (m : ι) (j : κ)
    (k : Fin (Module.finrank ℂ E.space)) : Q.space →ₗ[ℂ] Q.space :=
  LinearMap.krausOp (stdOrthonormalBasis ℂ E.space)
    (((M.op m).comp U.op).toLinearMap ∘ₗ LinearMap.tmulRightVec (w j)) k

/-- **Nielsen & Chuang, Exercise 8.7 (operator-sum representation).** Given an ensemble
decomposition `σ = ∑ⱼ |wⱼ⟩⟨wⱼ|` of the environment state (hypothesis `hσ`; N&C's `σ = ∑ⱼ qⱼ |j⟩⟨j|`
with the weights absorbed, `wⱼ = √qⱼ |j⟩`), the induced operation `Eₘ` has the operator-sum
representation

  `Eₘ(ρ) = ∑ⱼ ∑ₖ Eⱼₖ ρ Eⱼₖ†`,   `Eⱼₖ = ⟨eₖ| Mₘ U |wⱼ⟩`   (N&C Eqs. (8.33)–(8.35), `Pₘ ↦ Mₘ`),

the operation elements being `generalMeasurementEnvKrausOp`. This is N&C's first ask; combined with
`bornProb_eq_trace_generalMeasurementEnvOp` (the trace identity `p(m) = tr[Eₘ(ρ)]`, the second ask)
it settles Exercise 8.7 for the given decomposition. Stated at the `Q.space →ₗ[ℂ] Q.space` level
(the coercion of the operation, applied to the density operator `ρ.op`).

Proof: `Eₘ(ρ) = tr_E(W (ρ ⊗ σ) W†)` with `W = Mₘ U`; substitute the decomposition of `σ` and apply
the general environment-model lemma
`LinearMap.partialTraceRight_conj_map_sum_rankOne_eq_sum_krausOp`
(itself the pure-state case `partialTraceRight_conj_map_rankOne_eq_sum_krausOp` distributed over the
rank-one terms). The bridge rewrites the Exercise 8.2 operation element `Mₘ (U (ρ ⊗ σ) U†) Mₘ†` into
the conjugation form `W (ρ ⊗ σ) W†` via `opElement`, `evolve`, and `State.tmul_op`. -/
theorem generalMeasurementEnvOp_eq_sum_krausOp (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) {κ : Type*} [Fintype κ] (w : κ → E.space)
    (hσ : (σ.op : E.space →ₗ[ℂ] E.space)
      = ∑ j, ((InnerProductSpace.rankOne ℂ (w j) (w j)).toLinearMap : E.space →ₗ[ℂ] E.space)) :
    (generalMeasurementEnvOp M U σ ρ m : Q.space →ₗ[ℂ] Q.space)
      = ∑ j, ∑ k, generalMeasurementEnvKrausOp M U w m j k ∘ₗ (ρ.op : Q.space →ₗ[ℂ] Q.space)
          ∘ₗ LinearMap.adjoint (generalMeasurementEnvKrausOp M U w m j k) := by
  have hop : M.opElement (U.evolve (ρ ⊗ σ)) m
      = ((M.op m).comp U.op).comp ((ρ ⊗ σ).op.comp
          (ContinuousLinearMap.adjoint ((M.op m).comp U.op))) := by
    simp only [Measurement.opElement_eq_postOp, ContinuousLinearMap.postOp, Evolution.evolve_op,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
  have hbridge : (M.opElement (U.evolve (ρ ⊗ σ)) m).toLinearMap
      = ((M.op m).comp U.op).toLinearMap ∘ₗ TensorProduct.map ρ.op σ.op
          ∘ₗ LinearMap.adjoint ((M.op m).comp U.op).toLinearMap := by
    rw [hop, ContinuousLinearMap.toLinearMap_comp ((M.op m).comp U.op),
      ContinuousLinearMap.toLinearMap_comp (ρ ⊗ σ).op,
      State.tmul_op, TensorProduct.toLinearMap_mapL, ContinuousLinearMap.adjoint_toLinearMap]
    rfl
  rw [generalMeasurementEnvOp, LinearMap.coe_toContinuousLinearMap, hbridge, hσ]
  exact LinearMap.partialTraceRight_conj_map_sum_rankOne_eq_sum_krausOp _ _ w _

/-- **Nielsen & Chuang, Exercise 8.7 (existence of an operator-sum representation).** The induced
operation `Eₘ` of a general measurement on system + environment *admits* an operator-sum
representation `Eₘ(ρ) = ∑ᵢ Fᵢ ρ Fᵢ†` on the principal system alone — the direct reading of N&C's
"find operator-sum representations for the corresponding quantum operations `Eₘ`". No ensemble
decomposition of `σ` need be supplied: it is produced from the positivity of the density operator
`σ.op` (`ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`), showing the hypothesis of
`generalMeasurementEnvOp_eq_sum_krausOp` is always dischargeable, so the representation is never
vacuous. The operation elements are `generalMeasurementEnvKrausOp` for the chosen decomposition,
reindexed from the double sum `∑ⱼ ∑ₖ` to a single sum over the product index. -/
theorem generalMeasurementEnvOp_exists_operatorSum (M : Measurement ι (Q ⊗ E))
    (U : Evolution (Q ⊗ E)) (σ : State E) (ρ : State Q) (m : ι) :
    ∃ (κ : Type) (_ : Fintype κ) (F : κ → Q.space →ₗ[ℂ] Q.space),
      (generalMeasurementEnvOp M U σ ρ m : Q.space →ₗ[ℂ] Q.space)
        = ∑ i, F i ∘ₗ (ρ.op : Q.space →ₗ[ℂ] Q.space) ∘ₗ LinearMap.adjoint (F i) := by
  obtain ⟨n, u, hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp σ.isPositive_op
  have hσ : (σ.op : E.space →ₗ[ℂ] E.space)
      = ∑ j, ((InnerProductSpace.rankOne ℂ (u j) (u j)).toLinearMap : E.space →ₗ[ℂ] E.space) := by
    rw [hu]
    simp only [ContinuousLinearMap.toLinearMap_sum]
  exact ⟨Fin n × Fin (Module.finrank ℂ E.space), inferInstance,
    fun p => generalMeasurementEnvKrausOp M U u m p.1 p.2, by
      rw [generalMeasurementEnvOp_eq_sum_krausOp M U σ ρ m u hσ, Fintype.sum_prod_type]⟩

end AxQM
