/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementModel

/-!
# Nielsen & Chuang, Exercise 8.9 (Measurement model)

*(N&C p. 366.)*

Construct measurement model: U with projectors P_m gives outcome m with prob tr(E_m(ρ)) and
post-state.

The exercise *constructs* a specific system–environment measurement realizing a given
trace-preserving family of quantum operations and then computes its outcome statistics. The
operator `U` of eq. (8.40) is assembled from the **operation elements** `Eₘₖ` (a family of
operators `Q →L[ℂ] Q`), the projectors `Pₘ = ∑ₖ |m, k⟩⟨m, k|` are rank-one operator sums, and the
two asks are the operator identities `p(m) = tr(Eₘ(ρ))` and `Eₘ(ρ) = ∑ₖ Eₘₖ ρ Eₘₖ†`. The model is
*parametrised by the Kraus family and an environment basis*, unlike Exercise 8.7 whose measurement
and unitary are abstract. The formalisation is in `AxQM/Postulates/API/MeasurementModel.lean`, with
the dilation mathematics in `ToMathlib/`. Compare Exercises 8.2 and 8.8.

## The formalisation

**The model and the two "show" claims**
(`AxQM/Postulates/API/MeasurementModel.lean`):

* `AxQM.Measurement.ofOrthonormalBasisFiber b out` — **the environment projectors `Pₘ`**
  (`Pₘ = ∑_{out σ = m} |b σ⟩⟨b σ|`, N&C's `Pₘ ≡ ∑ₖ |m, k⟩⟨m, k|`), a genuine `Measurement`, shown to
  be **projective** by `Measurement.isProjective_ofOrthonormalBasisFiber` (each `Pₘ` is an
  orthogonal projector). The labelling `out : ι → M` (which outcome each operation-element index
  belongs to) is strictly more general than N&C's product index `|m, k⟩`.
* `AxQM.measurementModelEvolution b he₀ E hE` — **the joint unitary `U`** of eq. (8.40),
  packaged as an `Evolution (Q ⊗ Env)`, with `measurementModelEvolution_op_tmul` its defining action
  `U (ψ ⊗ e₀) = ∑_σ (Eσ ψ) ⊗ (b σ)`. It is a *genuine unitary* (not merely the Stinespring
  isometry): trace preservation `∑_σ Eσ† Eσ = 1` makes the dilation an isometry, which extends to a
  unitary of the joint space (the "earlier construction" / Box 8.1).
* `AxQM.measurementModelInducedOp E out ρ m` — **the induced operation element**
  `Eₘ(ρ) = ∑_{out σ = m} Eσ ρ Eσ†`, and `measurementModelEnvOp_eq_inducedOp` the identity that
  Exercise 8.7's system–environment induced operation at this model *is* `Eₘ(ρ)`:
  `tr_E(Pₘ U (ρ ⊗ |e₀⟩⟨e₀|) U† Pₘ) = ∑_{out σ = m} Eσ ρ Eσ†`.
* `AxQM.measurementModel_bornProb_eq_trace` — **the probability ask:** measuring `Pₘ` after
  `U` gives outcome `m` with probability `p(m) = tr(Eₘ(ρ))` (as the complex equality
  `(p(m) : ℂ) = tr(Eₘ(ρ))`).
* `AxQM.measurementModel_reducedLeft_postMeasurement_op` — **the post-measurement-state ask
  (N&C's `Eₘ(ρ)/tr(Eₘ(ρ))`):** the reduced state of the principal system after outcome `m` is
  `tr(Eₘ(ρ))⁻¹ • Eₘ(ρ)`.

**Supporting mathematics** (`ToMathlib/Analysis/InnerProductSpace/`):

* `LinearMap.krausDilation` / `krausOp_krausDilation` / `adjoint_krausDilation_comp_self` /
  `LinearMap.exists_unitary_krausDilation` (`OperatorSumDilation.lean`) — the Stinespring dilation
  `V₀ = ∑_σ embedRightᵦ σ ∘ Eσ` assembled from a Kraus family, its operation-element recovery, the
  isometry ⟺ completeness equivalence, and the extension to a **unitary** of the joint space.
* `LinearMap.partialTraceRight_conj_sum_proj_eq_sum_krausOp` and
  `partialTraceRight_conj_sum_proj_map_rankOne_eq_sum_krausOp` (`OperatorSum.lean`) — the
  **projected environment operator-sum**: measuring the block projector `P_S` then discarding the
  environment recovers `∑_{σ ∈ S} krausOpᵦ V σ ρ (…)†` — the bridge from `tr_E(Pₘ … Pₘ)` to the
  operator sum `Eₘ(ρ)`.
* `ContinuousLinearMap.sum_adjoint_comp_toLinearMap_eq_id` — the `ContinuousLinearMap`→`LinearMap`
  bridge for the completeness hypothesis `∑_σ Eσ† Eσ = 1`.

## Design notes

* **Generality.** `Q`, `Env`, `ρ`, `e₀`, `E`, `out` are arbitrary: an arbitrary
  principal system and environment, an arbitrary trace-preserving Kraus family (completeness
  `∑_σ Eσ† Eσ = 1` is exactly "`∑ₘ Eₘ` is trace-preserving"), and an arbitrary outcome labelling.
  The evolution is a genuine unitary and the measurement a genuine projective measurement, so both
  of N&C's "show" claims are the literal `p(m) = tr(Eₘ(ρ))` and `Eₘ(ρ)/tr(Eₘ(ρ))` — a faithful,
  unweakened rendering of the exercise. The `out : ι → M` outcome map generalises N&C's uniform
  `|m, k⟩` product index (no fixed per-outcome `k`-range is assumed).
* **Reuse of Exercise 8.7.** The outcome statistics are obtained by *instantiating* Exercise 8.7's
  general system–environment machinery (`generalMeasurementEnvOp`,
  `bornProb_eq_trace_generalMeasurementEnvOp`) at this model's lifted measurement `Pₘ ⊗ 1`, unitary
  `U`, and standard environment state `|e₀⟩⟨e₀|`, so the already-proven Born-probability = trace
  bridge is not re-derived. See the module docstring of `AxQM/Postulates/API/MeasurementModel.lean`
  for the full argument.
-/
