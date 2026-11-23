/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GeneralMeasurementEnvironment

/-!
# Nielsen & Chuang, Exercise 8.7 (general measurement on system + environment)

*(N&C p. 364.)*

Find operator-sum reps for E_m from general measurement {M_m} on system+environment; probs tr[E(ρ)].

In N&C §8.2.4 the principal system `Q` (state `ρ`) is adjoined to an
environment `E` (state `σ`), the pair interacts via a unitary `U`, and the combined system is
measured; tracing out `E` after outcome `m` gives the induced operation
`Eₘ(ρ) = tr_E(Mₘ (U (ρ ⊗ σ) U†) Mₘ†)` (eq. (8.32) with N&C's projectors `Pₘ` replaced by the
general measurement operators `Mₘ`). Its normalization `Eₘ(ρ)/tr[Eₘ(ρ)]` is the final state of `Q`
alone and its trace `tr[Eₘ(ρ)]` is the probability of outcome `m`.

## Related declarations

The exercise's two asks use the partial trace, operator conjugation and the operator trace:
`Eₘ(ρ) = tr_E(Mₘ (U (ρ ⊗ σ) U†) Mₘ†)` and "probabilities are `tr[Eₘ(ρ)]`" (compare Exercise 8.2's
`Measurement.opElement`). The induced operation and the probability identity are in
`AxQM/Postulates/API/GeneralMeasurementEnvironment.lean`; the induced outcome distribution and the
normalized final state, stated for states, measurements and evolutions, are in this file.

In `AxQM/Postulates/API/GeneralMeasurementEnvironment.lean`:

* `AxQM.generalMeasurementEnvOp` — the induced operation
  `Eₘ(ρ) = tr_E(Mₘ (U (ρ ⊗ σ) U†) Mₘ†)`, as a `Q →L[ℂ] Q`.
* `AxQM.bornProb_eq_trace_generalMeasurementEnvOp` — **the probability ask:**
  `(p(m) : ℂ) = tr[Eₘ(ρ)]`, for the general measurement `M` on the post-interaction joint state.
* `AxQM.generalMeasurementEnvKrausOp` / `generalMeasurementEnvOp_eq_sum_krausOp` — **the
  operator-sum ask:** the operation elements `Eⱼₖ = ⟨eₖ| Mₘ U |wⱼ⟩` and the representation
  `Eₘ(ρ) = ∑ⱼₖ Eⱼₖ ρ Eⱼₖ†` for an ensemble decomposition `σ = ∑ⱼ |wⱼ⟩⟨wⱼ|` (N&C's
  `Eⱼₖ = √qⱼ ⟨eₖ| Mₘ U |j⟩`, Eqs. (8.33)–(8.35)), with
  `generalMeasurementEnvOp_exists_operatorSum` the existence form.

## The formalisation in this file

* `generalMeasurementProb` — the outcome probability `p(m)`, the Born probability
  (`Measurement.bornProb`, Postulate 3) of the general measurement `M` on the post-interaction joint
  state `U.evolve (ρ ⊗ σ)`. It is *definitionally* the `M.bornProb …` that
  `bornProb_eq_trace_generalMeasurementEnvOp` equates to `tr[Eₘ(ρ)]`, so that theorem
  delivers N&C's `p(m) = tr[Eₘ(ρ)]` for this probability.
* `generalMeasurementInducedState` — **the induced operation's normalized output**
  `Eₘ(ρ)/tr[Eₘ(ρ)]`: the final state of the principal system `Q` after outcome `m`, as the marginal
  (`State.reducedLeft`, tracing out the environment) of the normalized post-measurement joint state
  `M.postMeasurement (U.evolve (ρ ⊗ σ)) m` (Postulate 4). A genuine `State Q`.
* `generalMeasurementProb_sum_eq_one` — the induced outcome probabilities form a distribution,
  `∑ₘ p(m) = 1` (the family `{Eₘ}` is collectively trace-preserving), with
  `generalMeasurementProb_nonneg` / `generalMeasurementProb_le_one` bounding each in `[0,1]`.

## Notes

* **Contents.** Both of Exercise 8.7's asks, plus the physics reading. *Second ask (probabilities):*
  `p(m) = tr[Eₘ(ρ)]` (`bornProb_eq_trace_generalMeasurementEnvOp`). *First ask (operator-sum
  representation):* `Eₘ(ρ) = ∑ⱼₖ Eⱼₖ ρ Eⱼₖ†` with `Eⱼₖ = √qⱼ ⟨eₖ| Mₘ U |j⟩`
  (`generalMeasurementEnvKrausOp` / `generalMeasurementEnvOp_eq_sum_krausOp`, N&C's generalization
  of Eqs. (8.33)–(8.35) from projectors `Pₘ` to general operators `Mₘ`), using the environment's
  ensemble decomposition `σ = ∑ⱼ qⱼ |j⟩⟨j|` (weights absorbed into the vectors) via the general
  environment-model lemma `LinearMap.partialTraceRight_conj_map_sum_rankOne_eq_sum_krausOp` — the
  mixed-state generalization of `..._rankOne_eq_sum_krausOp`. That the decomposition always exists
  (positivity of `σ.op`) is `generalMeasurementEnvOp_exists_operatorSum`. *Statement for states
  (this file):* the outcome distribution and the normalized final state.
* **Generality.** `Q`, `E`, `ρ`, `σ`, `U`, `M` are arbitrary: an arbitrary
  environment state, an arbitrary unitary interaction, and an arbitrary *general* measurement
  (`Measurement`, whose completeness `∑ₘ Mₘ† Mₘ = 1` is exactly N&C's "measurement operators
  `{Mₘ}`"). This is N&C's projective derivation with `Pₘ ↦ Mₘ`, not a specialization.
* **The normalized-state statement.** As in Problem 8.2, modelling the induced operation through
  its *normalized* output keeps this statement inside the `State`/`Measurement`/`Evolution` API
  (`postMeasurement`, `reducedLeft`, `bornProb`, `evolve`, `⊗`). The *unnormalized* `Eₘ(ρ)` and the
  probability-as-trace identity are in `generalMeasurementEnvOp` above.
-/

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {Q E : QSystem}

/-- **The induced outcome probability** `p(m)` of Exercise 8.7: the Born probability
(`Measurement.bornProb`, Postulate 3) of the general measurement `M` on the post-interaction joint
state `U.evolve (ρ ⊗ σ)`. It is definitionally the `M.bornProb …` that
`bornProb_eq_trace_generalMeasurementEnvOp` equates to `tr[Eₘ(ρ)]` (N&C's `p(m) = tr[Eₘ(ρ)]`). -/
def generalMeasurementProb (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) : ℝ :=
  M.bornProb (U.evolve (ρ ⊗ σ)) m

/-- **The induced operation's normalized output** `Eₘ(ρ)/tr[Eₘ(ρ)]` (Exercise 8.7): the final state
of the principal system `Q` after the general measurement of the combined system yields a possible
outcome `m` (`hp : p(m) ≠ 0`). It is the left marginal (`State.reducedLeft`, tracing out the
environment `E`) of the normalized post-measurement joint state
`M.postMeasurement (U.evolve (ρ ⊗ σ)) m` (Postulate 4), i.e. `Eₘ(ρ)/tr[Eₘ(ρ)]` — a genuine
`State Q`. -/
def generalMeasurementInducedState (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) (hp : generalMeasurementProb M U σ ρ m ≠ 0) : State Q :=
  (M.postMeasurement (U.evolve (ρ ⊗ σ)) m hp).reducedLeft

/-- **The induced family `{Eₘ}` is collectively trace-preserving:** the induced outcome
probabilities sum to one, `∑ₘ p(m) = 1`. The Born-rule normalization (`sum_bornProb_eq_one`) for the
general measurement on the post-interaction joint state — the family of induced operations is a
complete measurement process on the principal system. -/
theorem generalMeasurementProb_sum_eq_one (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) : ∑ m, generalMeasurementProb M U σ ρ m = 1 :=
  M.sum_bornProb_eq_one _

/-- Each induced outcome probability is non-negative. -/
theorem generalMeasurementProb_nonneg (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) : 0 ≤ generalMeasurementProb M U σ ρ m :=
  M.bornProb_nonneg _ _

/-- Each induced outcome probability is at most one. -/
theorem generalMeasurementProb_le_one (M : Measurement ι (Q ⊗ E)) (U : Evolution (Q ⊗ E))
    (σ : State E) (ρ : State Q) (m : ι) : generalMeasurementProb M U σ ρ m ≤ 1 :=
  M.bornProb_le_one _ _

end AxQM
