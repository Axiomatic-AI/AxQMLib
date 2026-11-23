/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TraceDistance
import AxQM.Postulates.API.RandomUnitaryChannel
import AxQM.Postulates.SystemIso
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.Composite

/-!
# AxQM.Postulates.API — probabilistic mixtures of states

Nielsen & Chuang repeatedly form the **probabilistic mixture** `∑ᵢ pᵢ ρᵢ` of a family of
states `{ρᵢ}` weighted by a probability distribution `{pᵢ}` — the density operator describing
"prepare `ρᵢ` with probability `pᵢ`" (e.g. the mixtures of Theorem 9.3, the joint convexity
`(9.50)`, and the convexity exercises 9.8–9.13). This file defines `State.mix`: it takes
a probability distribution and a family of states and returns the mixed `State`, its density
operator property discharged by the convex-combination closure `isDensityOp_sum_prob_smul`.

Statements about mixtures (such as the Chapter 9 distance results) can then name `State.mix` in
place of a hypothesis `ρ.op = ∑ᵢ pᵢ ρᵢ.op` on density operators.

## Main definitions

* `State.mix` — the mixed state `∑ᵢ pᵢ ρᵢ` (N&C mixtures).

## Main statements

* `State.mix_op` — the density operator of a mixture, `(mix p hp hsum ρ).op = ∑ᵢ pᵢ ρᵢ.op`.
* `State.op_traceNorm_eq_one` — a state's density operator has trace norm one, `‖ρ.op‖₁ = 1`.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **probabilistic mixture** `∑ᵢ pᵢ ρᵢ` of a finite family of states `ρ : ι → State S`
weighted by a probability distribution `p : ι → ℝ` (`0 ≤ pᵢ` and `∑ᵢ pᵢ = 1`): the state whose
density operator is the convex combination `∑ᵢ (pᵢ : ℂ) • ρᵢ.op`.

Its density-operator
property (positive, trace one) is the `n`-ary convex-combination closure
`isDensityOp_sum_prob_smul` applied to the `ρᵢ.isDensity`. The distance results of
N&C Chapter 9 name `mix` rather than an `.op = ∑ …` hypothesis. -/
noncomputable def State.mix {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) : State S where
  op := ∑ i, (p i : ℂ) • (ρ i).op
  isDensity := isDensityOp_sum_prob_smul (fun i => (ρ i).isDensity) hp hsum

/-- The **density operator of a mixture**: that of
`∑ᵢ pᵢ ρᵢ` is the convex combination `∑ᵢ (pᵢ : ℂ) • ρᵢ.op`. Definitional (`rfl`);
it is used to reason about `State.mix` through its operator. -/
@[simp]
theorem State.mix_op {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).op = ∑ i, (p i : ℂ) • (ρ i).op := rfl

/-- The **mixture of a constant family is that state**: mixing a single state `σ` with *any*
probability distribution `p` returns `σ`. Since `∑ᵢ pᵢ = 1`, the convex combination collapses,
`∑ᵢ (pᵢ : ℂ) • σ.op = (∑ᵢ pᵢ) • σ.op = σ.op`. This is the algebraic fact that reduces a
convexity-in-one-argument statement to the joint form (e.g. N&C `(9.51)`, Exercise 9.8, from
joint convexity `(9.50)` by taking the second family constant) and appears in fixed-point
mixing arguments (Exercises 9.9–9.13). -/
@[simp]
theorem State.mix_const {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (σ : State S) :
    State.mix p hp hsum (fun _ => σ) = σ := by
  ext
  simp only [State.mix_op, ← Finset.sum_smul, ← Complex.ofReal_sum, hsum, Complex.ofReal_one,
    one_smul]

/-- **A mixture whose positive-weight components all equal a fixed state is that state.** If every
component `ρⱼ` carrying positive weight (`pⱼ > 0`) equals `σ`, then `∑ⱼ pⱼ ρⱼ = σ`; the zero-weight
components are irrelevant since they drop out of the convex combination. The collapse is the same
`∑ⱼ (pⱼ : ℂ) • σ.op = (∑ⱼ pⱼ) • σ.op = σ.op` used by `State.mix_const`, which is the
literally-constant-family special case (`h := fun _ _ => rfl`). Reusable across mixing/convexity
arguments; in particular it supplies the equality direction of the strict-concavity of the entropy
(N&C Exercise 11.18): a mixture equals its (faithful) value exactly when its positive-weight
components coincide. -/
theorem State.mix_eq_of_forall_pos_eq {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) (σ : State S)
    (h : ∀ j, 0 < p j → ρ j = σ) : State.mix p hp hsum ρ = σ := by
  apply State.ext
  have hcollapse : ∑ j, (p j : ℂ) • (ρ j).op = ∑ j, (p j : ℂ) • σ.op :=
    Finset.sum_congr rfl fun j _ => by
      rcases eq_or_lt_of_le (hp j) with h0 | hpj
      · simp [← h0]
      · rw [h j hpj]
  rw [State.mix_op, hcollapse, ← Finset.sum_smul, ← Complex.ofReal_sum, hsum,
    Complex.ofReal_one, one_smul]

/-- The **binary probabilistic mixture** `p ρ + (1 − p) σ` of two states, weighted by a single
probability `p ∈ [0, 1]`: the state whose density operator is the convex combination
`(p : ℂ) • ρ.op + (1 − p : ℂ) • σ.op`. The two-outcome special case of `State.mix` — "prepare `ρ`
with probability `p`, else `σ`" — which N&C's channel-mixing exercises repeatedly form: the mixing
operation `E(ρ) = p ρ₀ + (1 − p) E'(ρ)` of Exercise 9.11, the depolarizing channel `p I/2 + (1−p) ρ`
(Exercise 9.12), and the bit-flip channel (Exercise 9.13). Its density-operator property is the
binary convexity of the density set `ContinuousLinearMap.IsDensityOp.convex_combination`. -/
noncomputable def State.mixPair {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : State S) : State S where
  op := (p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op
  isDensity :=
    ρ.isDensity.convex_combination σ.isDensity (Complex.zero_le_real.mpr hp0)
      (Complex.zero_le_real.mpr (by linarith : (0 : ℝ) ≤ 1 - p)) (by push_cast; ring)

/-- The **density operator of a binary mixture**: that of
`p ρ + (1 − p) σ` is `(p : ℂ) • ρ.op + (1 − p : ℂ) • σ.op`. Definitional (`rfl`); it is used
to reason about `State.mixPair` through its operator. -/
@[simp]
theorem State.mixPair_op {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : State S) :
    (State.mixPair hp0 hp1 ρ σ).op = (p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op := rfl

/-- **A two-point mixture is strictly positive when its right operand is.** If the right operand `σ`
of `mixPair` has a strictly positive density operator and its weight `1 − p` is positive (`p < 1`),
then `(mixPair hp0 hp1 ρ σ).op = p • ρ.op + (1 − p) • σ.op` is strictly positive: a nonnegative
summand `p • ρ.op` (`ρ.op ≥ 0`, `p ≥ 0`) plus the strictly positive `(1 − p) • σ.op`. The
regularisation workhorse — mixing an arbitrary state towards a strictly positive reference (e.g. the
maximally mixed state) with positive weight makes it faithful. -/
theorem State.isStrictlyPositive_mixPair_op {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp1' : p < 1)
    {ρ σ : State S} (hσ : IsStrictlyPositive σ.op) :
    IsStrictlyPositive (State.mixPair hp0 hp1 ρ σ).op := by
  rw [State.mixPair_op]
  exact IsStrictlyPositive.nonneg_add
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ρ.isDensity.isPositive.smul_of_nonneg (by exact_mod_cast hp0)))
    (IsStrictlyPositive.smul (by exact_mod_cast (by linarith : (0 : ℝ) < 1 - p)) hσ)

/-- **Mixing a state with itself yields that state**: `mixPair p ρ ρ = ρ` for any weight
`p ∈ [0, 1]`. The convex combination collapses,
`(p : ℂ) • ρ.op + (1 − p : ℂ) • ρ.op = ((p + (1 − p)) : ℂ) • ρ.op = ρ.op`. The binary-mixture
analogue of `State.mix_const`; it lets a mixture-of-perturbations argument recognise the
unperturbed term (e.g. reducing a trace-distance convexity bound
`D(mixPair p ρ τ, ρ) = D(mixPair p ρ τ, mixPair p ρ ρ)` to the joint form). -/
@[simp]
theorem State.mixPair_self {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : State S) :
    State.mixPair hp0 hp1 ρ ρ = ρ := by
  apply State.ext
  rw [State.mixPair_op, ← add_smul]
  have hc : (p : ℂ) + ((1 - p : ℝ) : ℂ) = 1 := by push_cast; ring
  rw [hc, one_smul]

/-- **Joint convexity of the trace distance for binary mixtures**: for a common weight `p ∈ [0, 1]`,
`D(p ρ₁ + (1−p) σ₁, p ρ₂ + (1−p) σ₂) ≤ p D(ρ₁, ρ₂) + (1−p) D(σ₁, σ₂)`. The two-outcome instance of
the joint convexity `(9.50)` (`State.traceDistance_mix_jointly_convex`), proved directly here by the
trace-norm triangle inequality: writing the difference of the two mixtures as
`p (ρ₁.op − ρ₂.op) + (1−p) (σ₁.op − σ₂.op)`, subadditivity (`traceNorm_add_le`) and absolute
homogeneity (`traceNorm_smul`, with `p, 1−p ≥ 0`) bound its trace norm by the weighted sum, and
halving gives the trace-distance form. This is the reusable convexity step behind the strict
contractivity of a channel mixing in a fixed state (Exercise 9.11). -/
theorem State.traceDistance_mixPair_jointly_convex {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ₁ σ₁ ρ₂ σ₂ : State S) :
    (State.mixPair hp0 hp1 ρ₁ σ₁).traceDistance (State.mixPair hp0 hp1 ρ₂ σ₂)
      ≤ p * ρ₁.traceDistance ρ₂ + (1 - p) * σ₁.traceDistance σ₂ := by
  rw [State.traceDistance_eq, State.mixPair_op, State.mixPair_op]
  have hdiff :
      ((p : ℂ) • ρ₁.op + ((1 - p : ℝ) : ℂ) • σ₁.op)
          - ((p : ℂ) • ρ₂.op + ((1 - p : ℝ) : ℂ) • σ₂.op)
        = (p : ℂ) • (ρ₁.op - ρ₂.op) + ((1 - p : ℝ) : ℂ) • (σ₁.op - σ₂.op) := by
    rw [smul_sub, smul_sub]; abel
  rw [hdiff]
  have hbound := ContinuousLinearMap.traceNorm_add_le
    ((p : ℂ) • (ρ₁.op - ρ₂.op)) (((1 - p : ℝ) : ℂ) • (σ₁.op - σ₂.op))
  rw [ContinuousLinearMap.traceNorm_smul, ContinuousLinearMap.traceNorm_smul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hp0,
    Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p)] at hbound
  rw [State.traceDistance_eq, State.traceDistance_eq]
  linarith [hbound]

/-- The **trace norm of a state's density operator is one**, `‖ρ.op‖₁ = 1`. A density
operator is positive, so its trace norm equals the real part of its trace
(`ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive`), which is `1`
(`State.trace_op_eq_one`). The normalization fact behind the classical-distance term of the
strong-convexity bound (N&C Theorem 9.3). -/
theorem State.op_traceNorm_eq_one (ρ : State S) : ρ.op.traceNorm = 1 := by
  rw [ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive ρ.isPositive_op,
    ρ.trace_op_eq_one]
  simp

/-- **Transport of a finite mixture is the mixture of the transports**: carrying the mixture
`∑ᵢ pᵢ ρᵢ` along a system isomorphism `e` gives `∑ᵢ pᵢ (e ρᵢ e⁻¹)`. The conjugation
`conjStarAlgEquiv` implementing `State.congr` is `ℂ`-linear, so it commutes with the convex
combination defining `State.mix` (the `State.congr` companion of `State.reducedLeft_mix` /
`State.reducedRight_mix`). -/
theorem State.congr_mix {T : QSystem} {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) (e : S ≃ₛ T) :
    (State.mix p hp hsum ρ).congr e = State.mix p hp hsum (fun i => (ρ i).congr e) := by
  apply State.ext
  rw [State.congr_op, State.mix_op, State.mix_op]
  simp only [map_sum, map_smul, State.congr_op]

/-- **A unitary evolution distributes over a finite mixture**: applying `U` to the mixture
`∑ᵢ pᵢ ρᵢ` gives the mixture `∑ᵢ pᵢ (U ρᵢ U†)` of the evolved components. The conjugation
`conjStarAlgEquiv` implementing `Evolution.evolve` is `ℂ`-linear, so it commutes with the convex
combination defining `State.mix` — the `Evolution.evolve` companion of `State.congr_mix` /
`State.reducedLeft_mix`. -/
theorem State.evolve_mix {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) (U : Evolution S) :
    U.evolve (State.mix p hp hsum ρ) = State.mix p hp hsum (fun i => U.evolve (ρ i)) := by
  apply State.ext
  rw [Evolution.evolve_op_conjStarAlgEquiv, State.mix_op, State.mix_op]
  simp only [map_sum, map_smul, Evolution.evolve_op_conjStarAlgEquiv]

/-- **Tensoring a fixed state onto a finite mixture distributes**:
`(∑ᵢ pᵢ ρᵢ) ⊗ σ = ∑ᵢ pᵢ (ρᵢ ⊗ σ)`. The tensor-product map `TensorProduct.mapL` is linear in its
left argument (`TensorProduct.mapL_sum_left` / `TensorProduct.mapL_smul_left`), so it commutes with
the convex combination defining `State.mix` — the `State.tmul` companion of `State.congr_mix`. -/
theorem State.mix_tmul {T : QSystem} {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) (σ : State T) :
    (State.mix p hp hsum ρ).tmul σ = State.mix p hp hsum (fun i => (ρ i).tmul σ) := by
  apply State.ext
  rw [State.tmul_op, State.mix_op, State.mix_op, TensorProduct.mapL_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [State.tmul_op]
  exact TensorProduct.mapL_smul_left _ _ _

/-- **Tensoring a fixed state onto a finite mixture on the LEFT distributes**:
`σ ⊗ (∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ (σ ⊗ ρᵢ)`. The left-factor companion of `State.mix_tmul`, via the
right-argument linearity of `TensorProduct.mapL` (`TensorProduct.mapL_sum_right` /
`TensorProduct.mapL_smul_right`). -/
theorem State.tmul_mix {T : QSystem} {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (σ : State T) (ρ : ι → State S) :
    σ.tmul (State.mix p hp hsum ρ) = State.mix p hp hsum (fun i => σ.tmul (ρ i)) := by
  apply State.ext
  rw [State.tmul_op, State.mix_op, State.mix_op, TensorProduct.mapL_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [State.tmul_op]
  exact TensorProduct.mapL_smul_right _ _ _

/-- **The action of a random-unitary channel as a probabilistic mixture.** A `RandomUnitaryChannel`
acts as the `State.mix` of its unitary conjugations `Uₖ ρ Uₖ†`:
`C.apply ρ = mix C.prob _ _ (fun k => (C.unitary k).evolve ρ)`. A general, citable fact about every
`RandomUnitaryChannel` (not pinching-specific). It lands here — rather than next to
`RandomUnitaryChannel.apply_op` — because it names `State.mix`, which is defined in this file, and
`Mixture` imports `RandomUnitaryChannel`, so the reverse import would be a cycle. -/
theorem RandomUnitaryChannel.apply_eq_mix (C : RandomUnitaryChannel S) (ρ : State S) :
    C.apply ρ = State.mix C.prob C.prob_nonneg C.sum_prob (fun k => (C.unitary k).evolve ρ) := by
  apply State.ext
  rw [RandomUnitaryChannel.apply_op, State.mix_op]

end AxQM
