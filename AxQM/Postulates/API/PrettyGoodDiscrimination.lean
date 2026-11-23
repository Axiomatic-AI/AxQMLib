/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SquareRootMeasurement
import AxQM.Postulates.API.SameNonzeroSpectrum
import AxQM.Postulates.API.Affinity
import ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurement
import ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurementError
import ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurementAmplitude
import ToMathlib.Analysis.InnerProductSpace.CommuteSqrtSubadditive
import ToMathlib.Analysis.InnerProductSpace.RotfeldTraceSqrt

/-!
# The pretty-good (square-root) discrimination measurement of a family of states

Given a finite family of quantum states `ρ : ι → State S`, the **pretty-good (square-root)
measurement** is the canonical measurement one uses to *identify which `ρ i` a system is in*.  With
total operator `S₀ = ∑ⱼ ρⱼ.op`, its effect at outcome `some i` is the conjugation
`Eᵢ = S₀⁻¹ᐟ² · ρᵢ.op · S₀⁻¹ᐟ²` (the density-operator pretty-good POVM), realised as a postulate
`Measurement (Option ι) S` via the square-root bridge `Measurement.ofPOVM`; the `none` outcome is
the "inconclusive" junk element `1 − ∑ᵢ Eᵢ`.

This is the **mixed-state** discrimination measurement: unlike the pure-state `distinguishingPOVM`
(which needs linearly independent state *vectors*), it applies to arbitrary density operators, so it
is the object a mixed-state ensemble-discrimination error bound is stated over.  It is exactly the
measurement N&C's Problem 5.5 identification clause calls for — distinguishing the near-orthogonal
coset reduced states `σ_K^{⊗m}` of the candidate hidden subgroups — where the pure-state POVM does
not apply (the reduced states are mixed).

## What this file provides

* `AxQM.State.prettyGoodMeasurement` — the density-operator pretty-good measurement of a
  finite family of states `ρ : ι → State S`, as a `Measurement (Option ι) S`.
* `AxQM.State.prettyGoodMeasurement_bornProb_some` — its Born rule at a genuine outcome
  `some i`: `p(some i | τ) = re tr(S₀⁻¹ᐟ² · ρᵢ.op · S₀⁻¹ᐟ² · τ.op)`.  Taking `τ = ρ i` gives the
  identification **success** probability; `τ = ρ j` (`j ≠ i`) the **confusion** probability.
* `AxQM.State.prettyGoodMeasurement_bornProb_none` — the inconclusive probability.
* `AxQM.State.prettyGoodMeasurement_bornProb_self_eq` — the **Barnum–Knill amplitude
  form** of the success probability, `p(some i | ρ i) = re tr(Xᵢ²)` with the self-adjoint amplitude
  `Xᵢ = √ρᵢ · S₀⁻¹ᐟ² · √ρᵢ`.  This exhibits the success as the Hilbert–Schmidt norm² of `Xᵢ` (so
  it is `≥ 0`) and is the starting point of the pretty-good-measurement error analysis (the deficit
  `1 − re tr(Xᵢ²)` is bounded, message by message, by the off-diagonal overlaps).
* `AxQM.State.one_sub_prettyGoodMeasurement_bornProb_self_le` — the **per-state error reduction**:
  the identification deficit is bounded by a single physical trace,
  `1 − p(some i | ρ i) ≤ 2·(1 − re tr(√ρᵢ · S₀⁻¹ᐟ² · ρᵢ))`.  It is the *discrimination* analogue of
  the HSW channel-coding bound `State.one_sub_re_trace_prettyGood_le`: the frame reduction
  `InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le` (the `√Γ`-diagonal reduction
  `1 − re tr(σ E) ≤ 2·∑ λ(1 − α)`) instantiated for pure discrimination — generalized inverse square
  root `T = S₀⁻¹ᐟ²`, spectral family `φ = ρᵢ.eigenbasis`, effect frame `ψₖ = √λₖ • eₖ`, and no
  typical restriction (`J = univ`).  Because `re tr(√ρᵢ S₀⁻¹ᐟ² ρᵢ) → 1` as the states become
  orthogonal, this reduces the identification error to an off-diagonal deficit; bounding that
  deficit by the pairwise-affinity sum is the Ettinger–Høyer–Knill step.
* `AxQM.State.prettyGoodMeasurement_bornProb_some_comm` — **symmetry** of the confusion
  matrix: `p(some j ∣ ρ i) = p(some i ∣ ρ j)`, by cyclicity of the confusion trace
  `re tr(S₀⁻¹ᐟ² ρⱼ S₀⁻¹ᐟ² ρᵢ)`.
* `AxQM.State.prettyGoodMeasurement_bornProb_some_sq_le` — a **Cauchy–Schwarz bound** on
  the confusion probabilities: `p(some j ∣ ρ i)² ≤ p(some i ∣ ρ i)·p(some j ∣ ρ j)`, from the
  Hilbert–Schmidt pairing of the amplitude operators `√ρᵢ`-conjugated by `S₀⁻¹ᐟ²`.  Both are
  reusable structural facts feeding the per-pair analysis of the identification clause.

The construction composes the square-root-measurement bridge `Measurement.ofPOVM`
(`Postulates.API.SquareRootMeasurement`) and the pretty-good POVM
(`ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurement`).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Problem 5.5 (Non-Abelian hidden subgroups), Box 12.5.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **The pretty-good (square-root) discrimination measurement of a finite family of states**
`ρ : ι → State S`.  With total operator `S₀ = ∑ⱼ ρⱼ.op`, this is the square-root measurement
realising the density-operator pretty-good POVM whose effect at outcome `some i` is the conjugation
`Eᵢ = S₀⁻¹ᐟ² · ρᵢ.op · S₀⁻¹ᐟ²` and whose `none` effect is the inconclusive `1 − ∑ᵢ Eᵢ`.

Built as `Measurement.ofPOVM (POVM.prettyGood (fun i ↦ ρᵢ.op) _)`: each `ρᵢ.op` is positive
(`State.isPositive_op`), so `POVM.prettyGood` produces a genuine POVM, and `Measurement.ofPOVM`
turns it into a postulate `Measurement` by taking operator square roots of the effects.  This is the
mixed-state analogue of `distinguishingPOVM`, the discrimination measurement N&C's Problem 5.5
identification clause is stated over. -/
def State.prettyGoodMeasurement (ρ : ι → State S) : Measurement (Option ι) S :=
  Measurement.ofPOVM (POVM.prettyGood (fun i => (ρ i).op)
    (fun i => (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ i).isPositive_op))

/-- **Born rule of the pretty-good discrimination measurement at a genuine outcome** `some i`.  For
a family `ρ : ι → State S` with total operator `S₀ = ∑ⱼ ρⱼ.op`, measuring
`State.prettyGoodMeasurement ρ` on a state `τ` returns outcome `some i` with probability

`p(some i | τ) = re tr(S₀⁻¹ᐟ² · ρᵢ.op · S₀⁻¹ᐟ² · τ.op)`.

Taking `τ = ρ i` gives the **success** probability of correctly identifying `ρ i`; taking `τ = ρ j`
with `j ≠ i` gives the **confusion** probability.  Immediate from the square-root-measurement Born
rule `Measurement.ofPOVM_bornProb_eq_re_trace` and the pretty-good effect formula
`POVM.prettyGood_elements_some`. -/
theorem State.prettyGoodMeasurement_bornProb_some (ρ : ι → State S) (τ : State S) (i : ι) :
    (State.prettyGoodMeasurement ρ).bornProb τ (some i)
      = RCLike.re ((LinearMap.trace ℂ S.space)
          ((((∑ j, (ρ j).op).genInvSqrt * (ρ i).op * (∑ j, (ρ j).op).genInvSqrt).comp τ.op) :
            S.space →ₗ[ℂ] S.space)) := by
  rw [State.prettyGoodMeasurement, Measurement.ofPOVM_bornProb_eq_re_trace]
  simp only [POVM.prettyGood_elements_some]

/-- **Born rule of the pretty-good discrimination measurement at the inconclusive outcome** `none`.
For a family `ρ : ι → State S` with total operator `S₀ = ∑ⱼ ρⱼ.op`, the "junk"/inconclusive
probability is

`p(none | τ) = re tr((1 − ∑ᵢ S₀⁻¹ᐟ² · ρᵢ.op · S₀⁻¹ᐟ²) · τ.op)`.

Immediate from `Measurement.ofPOVM_bornProb_eq_re_trace` and the pretty-good junk-effect formula
`POVM.prettyGood_elements_none`. -/
theorem State.prettyGoodMeasurement_bornProb_none (ρ : ι → State S) (τ : State S) :
    (State.prettyGoodMeasurement ρ).bornProb τ none
      = RCLike.re ((LinearMap.trace ℂ S.space)
          (((1 - ∑ i, (∑ j, (ρ j).op).genInvSqrt * (ρ i).op * (∑ j, (ρ j).op).genInvSqrt).comp
              τ.op : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) := by
  rw [State.prettyGoodMeasurement, Measurement.ofPOVM_bornProb_eq_re_trace]
  simp only [POVM.prettyGood_elements_none]

/-- **The Barnum–Knill amplitude form of the identification success probability.**  For a family
`ρ : ι → State S` with total operator `S₀ = ∑ⱼ ρⱼ.op`, the probability that the pretty-good
discrimination measurement correctly identifies `ρ i` is the Hilbert–Schmidt norm² of the
self-adjoint **amplitude operator** `Xᵢ = √ρᵢ · S₀⁻¹ᐟ² · √ρᵢ`:

`p(some i | ρ i) = re tr(Xᵢ · Xᵢ)`.

Since `Xᵢ` is self-adjoint, `re tr(Xᵢ²) = ‖Xᵢ‖²_HS ≥ 0`.  This is the starting point of the
pretty-good-measurement (square-root measurement) error analysis: the deficit `1 − re tr(Xᵢ²)` is
what the discrimination error bound controls.

The identity is `re tr(S₀⁻¹ᐟ² ρᵢ S₀⁻¹ᐟ² · ρᵢ) = re tr(Xᵢ²)`, obtained by inserting `√ρᵢ · √ρᵢ = ρᵢ`
(`cfc_real_sqrt_mul_self_of_nonneg`) and cycling the trace (`LinearMap.trace_mul_comm`):
`Xᵢ² = √ρᵢ S₀⁻¹ᐟ² (√ρᵢ √ρᵢ) S₀⁻¹ᐟ² √ρᵢ = √ρᵢ S₀⁻¹ᐟ² ρᵢ S₀⁻¹ᐟ² √ρᵢ`, and cycling the leading `√ρᵢ`
to the right recombines `√ρᵢ √ρᵢ = ρᵢ`. -/
theorem State.prettyGoodMeasurement_bornProb_self_eq (ρ : ι → State S) (i : ι) :
    (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      = RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (ρ i).op * (∑ j, (ρ j).op).genInvSqrt * cfc Real.sqrt (ρ i).op
              * (cfc Real.sqrt (ρ i).op * (∑ j, (ρ j).op).genInvSqrt * cfc Real.sqrt (ρ i).op) :
            S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) := by
  rw [State.prettyGoodMeasurement_bornProb_some]
  congr 1
  set W := (∑ j, (ρ j).op).genInvSqrt with hW
  set r := cfc Real.sqrt (ρ i).op with hr
  have hrr : r * r = (ρ i).op :=
    cfc_real_sqrt_mul_self_of_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ i).isPositive_op)
  -- The amplitude square rearranges to `r · (W · ρᵢ · W · r)` (assoc + `r · r = ρᵢ`).
  have hsq : (r * W * r * (r * W * r) : S.space →L[ℂ] S.space)
      = r * (W * (ρ i).op * W * r) := by
    rw [← hrr]; simp only [mul_assoc]
  rw [hsq, ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
      ← ContinuousLinearMap.toLinearMap_mul]
  -- `tr(r · (W ρᵢ W r)) = tr((W ρᵢ W r) · r) = tr(W ρᵢ W · (r · r)) = tr(W ρᵢ W ρᵢ)`.
  rw [show (W * (ρ i).op * W * r) * r = W * (ρ i).op * W * (ρ i).op by rw [mul_assoc, hrr]]
  -- The left side `(W ρᵢ W).comp ρᵢ` is the same product as `W ρᵢ W ρᵢ`.
  rw [← ContinuousLinearMap.mul_def]

/-- **Per-state error reduction of the pretty-good discrimination measurement** (Nielsen & Chuang,
Problem 5.5, the *discrimination* analogue of the HSW channel-coding bound
`State.one_sub_re_trace_prettyGood_le`).  For a finite family `ρ : ι → State S` with total operator
`S₀ = ∑ⱼ ρⱼ.op`, the deficit of the probability of correctly identifying `ρ i` with the pretty-good
measurement is bounded by a single physical trace:

`1 − p(some i ∣ ρ i) ≤ 2·(1 − re tr(√ρᵢ · S₀⁻¹ᐟ² · ρᵢ))`.

This is the frame reduction `InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le`
(`1 − re tr(σ·T·(∑_{j∈J}|ψⱼ⟩⟨ψⱼ|)·T) ≤ 2·∑_{k∈J} λₖ(1 − re⟨ψₖ, T φₖ⟩) + ∑_{k∉J} λₖ`) specialised to
the *pure discrimination* setting: generalized inverse square root `T = S₀⁻¹ᐟ²` (self-adjoint,
`ContinuousLinearMap.isSelfAdjoint_genInvSqrt`), spectral family `φₖ = ρᵢ.eigenbasis k` with weights
`λₖ = ρᵢ.eigenvalueDist k`, effect frame `ψₖ = √λₖ • φₖ` — so that `∑ₖ|ψₖ⟩⟨ψₖ| = ρᵢ.op` (each
`|ψₖ⟩⟨ψₖ| = λₖ|φₖ⟩⟨φₖ|`, `InnerProductSpace.rankOne_real_sqrt_smul_self`, summed by
`State.op_eq_sum_eigenvalueDist_rankOne`), making the frame operator
`T·(∑ₖ|ψₖ⟩⟨ψₖ|)·T = S₀⁻¹ᐟ²·ρᵢ·S₀⁻¹ᐟ²` the pretty-good effect for `i` and the trace the success
probability `p(some i ∣ ρ i)` (`prettyGoodMeasurement_bornProb_some`, trace cyclicity) — and no
typical restriction, `J = univ` (so the atypical tail `∑_{k∉J} λₖ` vanishes).

The frame RHS `2·∑ₖ λₖ(1 − re⟨ψₖ, S₀⁻¹ᐟ² φₖ⟩)` collapses to `2·(1 − re tr(√ρᵢ S₀⁻¹ᐟ² ρᵢ))`: since
`∑ₖ λₖ = 1` (`State.eigenvalueDist_sum_eq_one`) and `re⟨√λₖ φₖ, S₀⁻¹ᐟ² φₖ⟩ = √λₖ re⟨φₖ, S₀⁻¹ᐟ² φₖ⟩`,
the sum is `1 − ∑ₖ λₖ√λₖ re⟨φₖ, S₀⁻¹ᐟ² φₖ⟩`, and `∑ₖ λₖ√λₖ re⟨φₖ, S₀⁻¹ᐟ² φₖ⟩ = re tr(√ρᵢ S₀⁻¹ᐟ² ρᵢ)`
(spectral resolution of `ρᵢ`, `√ρᵢ` self-adjoint with `√ρᵢ φₖ = √λₖ φₖ`, and
`InnerProductSpace.trace_comp_sum_smul_rankOne_self`).

Because `re tr(√ρᵢ S₀⁻¹ᐟ² ρᵢ) → 1` as the states become perfectly distinguishable (it is `tr ρᵢ = 1`
when `S₀ = ρᵢ` on the support of `ρᵢ`), this bounds the identification error by an off-diagonal
deficit; bounding that deficit by the pairwise-affinity sum `∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` is
the remaining Ettinger–Høyer–Knill step of Problem 5.5's identification clause. -/
theorem State.one_sub_prettyGoodMeasurement_bornProb_self_le (ρ : ι → State S) (i : ι) :
    1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      ≤ 2 * (1 - RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (ρ i).op * (∑ j, (ρ j).op).genInvSqrt * (ρ i).op :
            S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space))) := by
  classical
  have hSnn : (0 : S.space →L[ℂ] S.space) ≤ ∑ j, (ρ j).op :=
    Finset.sum_nonneg fun j _ =>
      (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ j).isPositive_op
  have hWsa : IsSelfAdjoint (∑ j, (ρ j).op).genInvSqrt :=
    ContinuousLinearMap.isSelfAdjoint_genInvSqrt hSnn
  set W : S.space →L[ℂ] S.space := (∑ j, (ρ j).op).genInvSqrt with hWdef
  -- The frame reduction, instantiated at `T = W`, `φ = eigenbasis`, `ψ = √λ • eigenbasis`,
  -- `J = univ`.
  have hframe := InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le
    (E := S.space) W hWsa (fun k => (ρ i).eigenbasis k)
    (fun k => (Real.sqrt ((ρ i).eigenvalueDist k) : ℂ) • (ρ i).eigenbasis k)
    (ρ i).eigenvalueDist Finset.univ
    (fun k => (ρ i).eigenvalueDist_nonneg k) (ρ i).eigenvalueDist_sum_eq_one
  -- Both rank-one sums in the frame LHS are `ρᵢ.op`: the state sum by the spectral resolution, the
  -- effect frame because `|√λₖ φₖ⟩⟨√λₖ φₖ| = λₖ|φₖ⟩⟨φₖ|`.
  have hstate : (∑ k, ((ρ i).eigenvalueDist k : ℂ)
      • (InnerProductSpace.rankOne ℂ ((ρ i).eigenbasis k)) ((ρ i).eigenbasis k)) = (ρ i).op :=
    ((ρ i).op_eq_sum_eigenvalueDist_rankOne).symm
  have heff : (∑ j, (InnerProductSpace.rankOne ℂ
        ((Real.sqrt ((ρ i).eigenvalueDist j) : ℂ) • (ρ i).eigenbasis j))
        ((Real.sqrt ((ρ i).eigenvalueDist j) : ℂ) • (ρ i).eigenbasis j)) = (ρ i).op := by
    rw [(ρ i).op_eq_sum_eigenvalueDist_rankOne]
    exact Finset.sum_congr rfl fun j _ =>
      InnerProductSpace.rankOne_real_sqrt_smul_self ((ρ i).eigenvalueDist_nonneg j) _
  rw [hstate, heff] at hframe
  -- Turn the frame LHS operator `ρᵢ ∘ (W ∘ (ρᵢ ∘ W))` into the product `ρᵢ · (W · ρᵢ · W)`.
  have hLHSop : (ρ i).op.comp (W.comp ((ρ i).op.comp W))
      = (ρ i).op * (W * (ρ i).op * W) := by
    simp only [← ContinuousLinearMap.mul_def, mul_assoc]
  rw [hLHSop] at hframe
  -- Identify the frame-LHS trace with the identification success probability (trace cyclicity).
  have hborn : (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      = RCLike.re ((LinearMap.trace ℂ S.space)
          ((ρ i).op * (W * (ρ i).op * W) : S.space →L[ℂ] S.space)) := by
    rw [State.prettyGoodMeasurement_bornProb_some, ← hWdef]
    congr 1
    rw [show (W * (ρ i).op * W).comp (ρ i).op = (W * (ρ i).op * W) * (ρ i).op from
        (ContinuousLinearMap.mul_def _ _).symm,
      ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
          ← ContinuousLinearMap.toLinearMap_mul]
  rw [← hborn] at hframe
  -- The diagonal overlap of the scaled frame vector `ψₖ = √λₖ φₖ`.
  have hpsi : ∀ k, RCLike.re (inner ℂ ((Real.sqrt ((ρ i).eigenvalueDist k) : ℂ)
        • (ρ i).eigenbasis k) (W ((ρ i).eigenbasis k)))
      = Real.sqrt ((ρ i).eigenvalueDist k)
        * RCLike.re (inner ℂ ((ρ i).eigenbasis k) (W ((ρ i).eigenbasis k))) := by
    intro k
    rw [inner_smul_left, Complex.conj_ofReal]
    simp
  -- The success trace `re tr(√ρᵢ W ρᵢ)` in eigenbasis-diagonal form.
  have hcell : ∀ m, inner ℂ ((ρ i).eigenbasis m)
        ((cfc Real.sqrt (ρ i).op * W) ((ρ i).eigenbasis m))
      = (Real.sqrt ((ρ i).eigenvalueDist m) : ℂ)
        * inner ℂ ((ρ i).eigenbasis m) (W ((ρ i).eigenbasis m)) := by
    intro m
    have heig : (ρ i).op ((ρ i).eigenbasis m)
        = ((ρ i).eigenvalueDist m : ℂ) • (ρ i).eigenbasis m := (ρ i).op_apply_eigenbasis m
    have hsqrt : cfc Real.sqrt (ρ i).op ((ρ i).eigenbasis m)
        = (Real.sqrt ((ρ i).eigenvalueDist m) : ℂ) • (ρ i).eigenbasis m :=
      IsSelfAdjoint.cfc_apply_smul_of_apply_eq_smul ((ρ i).isPositive_op.isSelfAdjoint) rfl
        (Real.continuous_sqrt.continuousOn) heig
    rw [mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_left (cfc Real.sqrt (ρ i).op),
      ContinuousLinearMap.adjoint_cfc_real_sqrt, hsqrt, inner_smul_left, Complex.conj_ofReal]
  have htrace : RCLike.re ((LinearMap.trace ℂ S.space)
        ((cfc Real.sqrt (ρ i).op * W * (ρ i).op : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space))
      = ∑ k, (ρ i).eigenvalueDist k * Real.sqrt ((ρ i).eigenvalueDist k)
            * RCLike.re (inner ℂ ((ρ i).eigenbasis k) (W ((ρ i).eigenbasis k))) := by
    rw [show (cfc Real.sqrt (ρ i).op * W * (ρ i).op)
        = (cfc Real.sqrt (ρ i).op * W).comp (ρ i).op from
          (ContinuousLinearMap.mul_def _ _).symm]
    -- Freeze the left factor so the spectral resolution only touches the `.comp` argument.
    set A : S.space →L[ℂ] S.space := cfc Real.sqrt (ρ i).op * W with hA
    rw [(ρ i).op_eq_sum_eigenvalueDist_rankOne,
      InnerProductSpace.trace_comp_sum_smul_rankOne_self, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA, hcell, ← mul_assoc, ← Complex.ofReal_mul]
    simp
  -- The frame-RHS `∑ λₖ(1 − re⟨ψₖ, W φₖ⟩)` equals `1 − re tr(√ρᵢ W ρᵢ)`.
  have hsum : ∑ k, (ρ i).eigenvalueDist k * (1 - RCLike.re (inner ℂ
        ((Real.sqrt ((ρ i).eigenvalueDist k) : ℂ) • (ρ i).eigenbasis k) (W ((ρ i).eigenbasis k))))
      = 1 - ∑ k, (ρ i).eigenvalueDist k * Real.sqrt ((ρ i).eigenvalueDist k)
              * RCLike.re (inner ℂ ((ρ i).eigenbasis k) (W ((ρ i).eigenbasis k))) := by
    have h1 : ∀ k, (ρ i).eigenvalueDist k * (1 - RCLike.re (inner ℂ
          ((Real.sqrt ((ρ i).eigenvalueDist k) : ℂ) • (ρ i).eigenbasis k) (W ((ρ i).eigenbasis k))))
        = (ρ i).eigenvalueDist k - (ρ i).eigenvalueDist k * Real.sqrt ((ρ i).eigenvalueDist k)
              * RCLike.re (inner ℂ ((ρ i).eigenbasis k) (W ((ρ i).eigenbasis k))) := by
      intro k; rw [hpsi k, mul_one_sub, ← mul_assoc]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, (ρ i).eigenvalueDist_sum_eq_one]
  -- Assemble: the frame RHS equals `2·(1 − re tr(√ρᵢ W ρᵢ))`.
  refine hframe.trans_eq ?_
  rw [Finset.compl_univ, Finset.sum_empty, add_zero, htrace, hsum]

/-- **The pretty-good discrimination error is bounded by the affinity to the total state**
(Nielsen & Chuang, Problem 5.5).  For a finite family `ρ : ι → State S` with total operator
`S₀ = ∑ⱼ ρⱼ.op`, the probability of failing to identify `ρ i` with the pretty-good measurement is
bounded by an *affinity deficit*:

`1 − p(some i ∣ ρ i) ≤ 2·(re tr(√S₀ · √ρᵢ) − 1)`.

It composes the per-state error reduction `State.one_sub_prettyGoodMeasurement_bornProb_self_le`
(`1 − p ≤ 2(1 − re tr(√ρᵢ · S₀⁻¹ᐟ² · ρᵢ))`) with the **Barnum–Knill success-amplitude lower bound**
`two_mul_re_trace_sub_re_trace_cfc_sqrt_mul_le_re_trace_genInvSqrt` (in `ContinuousLinearMap`,
`2·re tr(ρᵢ) − re tr(√S₀ · √ρᵢ) ≤ re tr(√ρᵢ · S₀⁻¹ᐟ² · ρᵢ)`, using `ρᵢ.op ≤ S₀`), and simplifies
`re tr(ρᵢ.op) = 1` (`State.trace_op_eq_one`).  This eliminates the generalized inverse square root:
the identification error is now a single closed-form trace of `√ρᵢ` against the total `√S₀`, whose
deficit `re tr(√S₀ · √ρᵢ) − re tr(ρᵢ) → 0` as `S₀` collapses onto `ρᵢ`'s support (perfect
distinguishability).  The remaining Ettinger–Høyer–Knill step decomposes `re tr(√S₀ · √ρᵢ) − 1`
into the pairwise-affinity sum `∑_{j≠i} re tr(√ρᵢ · √ρⱼ)` = `∑_{j≠i} State.affinity (ρ i) (ρ j)`. -/
theorem State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt
    (ρ : ι → State S) (i : ι) :
    1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      ≤ 2 * (RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
            : S.space →ₗ[ℂ] S.space)) - 1) := by
  have hρnn : (0 : S.space →L[ℂ] S.space) ≤ (ρ i).op :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ i).isPositive_op
  -- `ρᵢ.op ≤ S₀ = ∑ⱼ ρⱼ.op` (the other summands are positive).
  have hρS : (ρ i).op ≤ ∑ j, (ρ j).op :=
    Finset.single_le_sum
      (f := fun j => (ρ j).op)
      (fun j _ => (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ j).isPositive_op)
      (Finset.mem_univ i)
  have hamp :=
    ContinuousLinearMap.two_mul_re_trace_sub_re_trace_cfc_sqrt_mul_le_re_trace_genInvSqrt
      hρnn hρS
  have htr1 : RCLike.re ((LinearMap.trace ℂ S.space) ((ρ i).op : S.space →ₗ[ℂ] S.space)) = 1 := by
    rw [(ρ i).trace_op_eq_one]; simp
  rw [htr1] at hamp
  have h1432 := State.one_sub_prettyGoodMeasurement_bornProb_self_le ρ i
  linarith

/-- **The summed Barnum–Knill affinity-sum discrimination error bound** (Nielsen & Chuang,
Problem 5.5).  For a finite family of states `ρ : ι → State S`, the *total* pretty-good
identification error — the sum over the family of the per-state deficits `1 − p(some i ∣ ρ i)` —
is bounded by twice the off-diagonal **pairwise-affinity sum**:

`∑ᵢ (1 − p(some i ∣ ρ i)) ≤ 2·∑ᵢ ∑_{j ≠ i} A(ρ i, ρ j)`.

This is the reusable **mixed-state discrimination** form of the error bound the identification
clause consumes: the discrimination error is controlled by the pairwise quantum affinities
`A(ρ i, ρ j) = re tr(√ρᵢ √ρⱼ)` (`State.affinity`), exactly the quantity whose exponentially-small
`m`-copy value `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = (|K ∩ K'|/√(|K||K'|))^m` this problem's coset reduced
states enjoy.  Unlike a union bound over pairwise trace distances, the affinity **sum** stays small
because it is dominated by the few nearby subgroups — the mechanism behind the *linear* sample
count `m = 4 log₂|G| + 2`.

The proof sums the per-state reduction
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt`
(`1 − p(some i ∣ ρ i) ≤ 2·(re tr(√S₀ · √ρᵢ) − 1)`, `S₀ = ∑ⱼ ρⱼ.op`) over `i`; the total amplitude
`∑ᵢ re tr(√S₀ · √ρᵢ) = re tr(√S₀ · ∑ᵢ √ρᵢ)` is then bounded by the pairwise-affinity double sum
`∑ᵢⱼ re tr(√ρᵢ √ρⱼ)` via the Hilbert–Schmidt Cauchy–Schwarz operator kernel
`ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_sum_cfc_sqrt_le`, and the diagonal terms
`re tr(ρᵢ) = A(ρ i, ρ i) = 1` (`State.affinity_self`) cancel the `−1`'s, leaving the off-diagonal
sum.  Stated over `State.prettyGoodMeasurement` / `State.affinity`. -/
theorem State.sum_one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity
    [DecidableEq ι] (ρ : ι → State S) :
    ∑ i, (1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i))
      ≤ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, (ρ i).affinity (ρ j) := by
  classical
  have hApos : ∀ i, (0 : S.space →L[ℂ] S.space) ≤ (ρ i).op :=
    fun i => (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ i).isPositive_op
  -- Sum the per-state error reduction over `i`.
  have hstep1 : ∑ i, (1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i))
      ≤ ∑ i, 2 * (RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
            : S.space →ₗ[ℂ] S.space)) - 1) :=
    Finset.sum_le_sum fun i _ =>
      State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt ρ i
  refine hstep1.trans ?_
  -- The total amplitude `∑ᵢ re tr(√S₀ √ρᵢ) = re tr(√S₀ · ∑ᵢ √ρᵢ)`.
  have hmulsum : RCLike.re ((LinearMap.trace ℂ S.space)
        ((cfc Real.sqrt (∑ j, (ρ j).op) * ∑ i, cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
          : S.space →ₗ[ℂ] S.space))
      = ∑ i, RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
            : S.space →ₗ[ℂ] S.space)) := by
    rw [Finset.mul_sum, ContinuousLinearMap.toLinearMap_sum, map_sum, map_sum]
  -- Cauchy–Schwarz operator kernel: the total amplitude is `≤` the affinity double sum.
  have hkey : ∑ i, RCLike.re ((LinearMap.trace ℂ S.space)
        ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
          : S.space →ₗ[ℂ] S.space))
      ≤ ∑ i, ∑ j, (ρ i).affinity (ρ j) := by
    rw [← hmulsum]
    exact ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_sum_cfc_sqrt_le (fun i => (ρ i).op) hApos
  -- Off-diagonal `∑_{j≠i} = ∑ⱼ − (diagonal)`, and the diagonal affinity is `1`.
  have hgoal : (2 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.erase i, (ρ i).affinity (ρ j)
      = 2 * ((∑ i, ∑ j, (ρ i).affinity (ρ j)) - ∑ i, (ρ i).affinity (ρ i)) := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_erase_eq_sub (Finset.mem_univ i),
      Finset.sum_sub_distrib]
  have hlhs : ∑ i, 2 * (RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
            : S.space →ₗ[ℂ] S.space)) - 1)
      = 2 * ((∑ i, RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
            : S.space →ₗ[ℂ] S.space))) - ∑ i, (ρ i).affinity (ρ i)) := by
    have hone : ∀ i, (2 : ℝ) * (RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
            : S.space →ₗ[ℂ] S.space)) - 1)
        = 2 * (RCLike.re ((LinearMap.trace ℂ S.space)
          ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
            : S.space →ₗ[ℂ] S.space)) - (ρ i).affinity (ρ i)) :=
      fun i => by rw [(ρ i).affinity_self]
    rw [Finset.sum_congr rfl fun i _ => hone i, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hgoal, hlhs]
  linarith [hkey]

/-- **The paired-trace inequality** for a finite family `ρ : ι → State S` at index `i`: the
Hilbert–Schmidt trace of `√ρᵢ` against the *total* `√S₀` (`S₀ = ∑ⱼ ρⱼ.op`) is at most the affinity
sum `∑ⱼ A(ρ i, ρ j)` (`A = State.affinity`):

`re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ A(ρ i, ρ j)`.

This is the single Ettinger–Høyer–Knill operator ingredient of the *per-state* pretty-good
discrimination bound
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired`.  It is a
predicate on the total operator `√S₀`, which is *not* a `State` (its trace is the family size, not
`1`), so it is packaged as the named hypothesis `State.PairedTraceBound`.  It is **strictly weaker**
than the (false) operator subadditivity `√S₀ ≤ ∑ⱼ√ρⱼ`: it pairs against the *specific* positive
`√ρᵢ`.  It holds for every family of density operators (it fails for arbitrarily-reweighted positive
operators, so it genuinely uses `tr ρⱼ = 1`); its general proof is not given here. -/
def State.PairedTraceBound (ρ : ι → State S) (i : ι) : Prop :=
  RCLike.re ((LinearMap.trace ℂ S.space)
      ((cfc Real.sqrt (∑ j, (ρ j).op) * cfc Real.sqrt (ρ i).op : S.space →L[ℂ] S.space)
        : S.space →ₗ[ℂ] S.space))
    ≤ ∑ j, (ρ i).affinity (ρ j)

/-- **The per-state Barnum–Knill affinity-sum discrimination error bound** (Nielsen & Chuang,
Problem 5.5 — the *per-state* form, the route N&C's *linear* sample count needs).  Fix one state
`ρ i` of a finite family `ρ : ι → State S` with total operator `S₀ = ∑ⱼ ρⱼ.op`.  *Given* the
**paired-trace inequality** `State.PairedTraceBound ρ i` (`re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ A(ρ i, ρ j)`),
the probability of *failing* to identify `ρ i` with the pretty-good measurement is bounded by twice
the off-diagonal pairwise-affinity sum of `ρ i` *alone*:

`1 − p(some i ∣ ρ i) ≤ 2·∑_{j ≠ i} A(ρ i, ρ j)`.

This is the **per-state** companion of the summed bound
`State.sum_one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity`
(`∑ᵢ(1−p(some i∣ρ i)) ≤ 2·∑ᵢ∑_{j≠i}A(ρ i, ρ j)`), and it is the form the linear sample count of the
identification clause consumes: the summed bound only gives `1−p(i) ≤ ∑ᵢ(1−p(i))`, over-counting by
the whole family size `|ι|` (`= #subgroups`, super-polynomial for the coset family), whereas this
per-state bound charges `ρ i`'s error to *its own* collision sum `∑_{j≠i}A(ρ i, ρ j)`, which the
coset reduced states drive to `O(1/|G|)` already at `m = 4 log₂|G| + 2`.

It composes the per-state error reduction
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt`
(`1 − p(some i∣ρ i) ≤ 2·(re tr(√S₀ · √ρᵢ) − 1)`) with the hypothesis, peeling the `−1` with the
diagonal affinity `A(ρ i, ρ i) = 1` (`State.affinity_self`).  The hypothesis `hpaired` is the single
Ettinger–Høyer–Knill operator ingredient: the trace of `√ρᵢ` against the *total* `√S₀` is at most
the affinity sum.  It is **strictly weaker** than the *false* operator subadditivity `√S₀ ≤ ∑ⱼ√ρⱼ` —
it pairs the difference `√S₀ − ∑ⱼ√ρⱼ` against the *specific* positive operator `√ρᵢ` rather than
asserting an operator inequality — and holds for every family of *density* operators (it fails for
arbitrarily-reweighted positive operators, so it uses `tr ρⱼ = 1`; its general proof is not given
here — see `AxQM/NC/Ch5/Problem5_5.lean`).  Stated over `State.prettyGoodMeasurement` /
`State.affinity`. -/
theorem State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired
    [DecidableEq ι] (ρ : ι → State S) (i : ι) (hpaired : State.PairedTraceBound ρ i) :
    1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      ≤ 2 * ∑ j ∈ Finset.univ.erase i, (ρ i).affinity (ρ j) := by
  unfold State.PairedTraceBound at hpaired
  have hred := State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt ρ i
  -- `∑ⱼ A(ρᵢ, ρⱼ) = A(ρᵢ, ρᵢ) + ∑_{j≠i} A(ρᵢ, ρⱼ) = 1 + ∑_{j≠i} A(ρᵢ, ρⱼ)`.
  have hdiag : ∑ j, (ρ i).affinity (ρ j)
      = (ρ i).affinity (ρ i) + ∑ j ∈ Finset.univ.erase i, (ρ i).affinity (ρ j) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [(ρ i).affinity_self] at hdiag
  linarith

/-- **The paired-trace inequality holds unconditionally for a commuting family** (Nielsen & Chuang,
Problem 5.5 — the tractable case of piece (i)(a)).  For a finite family `ρ : ι → State S` whose
density operators **pairwise commute** (`∀ j k, Commute (ρ j).op (ρ k).op`), the paired-trace
inequality `State.PairedTraceBound ρ i` holds for *every* index `i`:

`re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ A(ρ i, ρ j)`   (`S₀ = ∑ⱼ ρⱼ.op`).

For general (non-commuting) families the paired-trace inequality is a subtle,
normalization-dependent operator fact (still open in this development); but when the family commutes
it follows from the honest operator inequality `√S₀ ≤ ∑ⱼ √ρⱼ` — the subadditivity of the operator
square root over a *commuting* family (`ContinuousLinearMap.cfc_real_sqrt_sum_le_of_commute`, which
*fails* without commutativity) — paired against the positive `√ρᵢ`
(`ContinuousLinearMap.re_trace_mul_mono_left`), the resulting
`re tr((∑ⱼ√ρⱼ)·√ρᵢ) = ∑ⱼ re tr(√ρⱼ√ρᵢ)` being the affinity sum `∑ⱼ A(ρ i, ρ j)` (`State.affinity`,
symmetric by `State.affinity_comm`).  Notably this needs **no** normalization — it holds for any
commuting family of positive operators — because the commuting operator inequality is stronger than
the paired-trace bound it implies.

This discharges the hypothesis of
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired` for commuting
families, giving the per-state discrimination bound `1 − p(some i ∣ ρ i) ≤ 2·∑_{j≠i} A(ρ i, ρ j)`
unconditionally there.  The intended application (Nielsen & Chuang, Problem 5.5) is the coset
reduced states of an **abelian** hidden subgroup instance, which are simultaneously diagonal in the
character basis and hence commute.  Stated over `State.PairedTraceBound` / `State.affinity`. -/
theorem State.pairedTraceBound_of_commute (ρ : ι → State S) (i : ι)
    (hc : ∀ j k, Commute (ρ j).op (ρ k).op) : State.PairedTraceBound ρ i := by
  classical
  unfold State.PairedTraceBound
  have hnn : ∀ j, (0 : S.space →L[ℂ] S.space) ≤ (ρ j).op :=
    fun j => (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ j).isPositive_op
  -- Commuting square-root subadditivity: `√S₀ ≤ ∑ⱼ √ρⱼ`.
  have hsub : cfc Real.sqrt (∑ j, (ρ j).op) ≤ ∑ j, cfc Real.sqrt (ρ j).op :=
    ContinuousLinearMap.cfc_real_sqrt_sum_le_of_commute Finset.univ (fun j => (ρ j).op) hnn hc
  have hqnn : (0 : S.space →L[ℂ] S.space) ≤ cfc Real.sqrt (ρ i).op := cfc_real_sqrt_nonneg _
  -- Pair against `√ρᵢ ≥ 0`, then identify the sum with the affinity sum.
  refine (ContinuousLinearMap.re_trace_mul_mono_left hsub hqnn).trans (le_of_eq ?_)
  rw [Finset.sum_mul, ContinuousLinearMap.toLinearMap_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(ρ i).affinity_comm (ρ j)]
  rfl

/-- **The unconditional per-state Barnum–Knill *fidelity*-sum discrimination error bound** (Nielsen
& Chuang, Problem 5.5 — the Rotfel'd route to piece (i)(a), holding for *every* family with **no**
paired-trace hypothesis).  For a finite family of states `ρ : ι → State S` with total operator
`S₀ = ∑ⱼ ρⱼ.op`, the probability of *failing* to identify `ρ i` with the pretty-good measurement is
bounded by twice `ρ i`'s off-diagonal pairwise-**fidelity** sum:

`1 − p(some i ∣ ρ i) ≤ 2·∑_{j ≠ i} F(ρ i, ρ j)`.

This is the fidelity-metric companion of the *conditional* affinity bound
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired`
(`1 − p ≤ 2·∑_{j≠i} A(ρ i, ρ j)` *given* `State.PairedTraceBound ρ i`).  Since `A(ρ, σ) ≤ F(ρ, σ)`
(`State.affinity_le_fidelity`) the fidelity bound is the weaker of the two, but — crucially — it is
**unconditional**: the affinity paired-trace inequality `re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ A(ρ i, ρ j)` is a
subtle, normalization-dependent operator fact (open in general), whereas the fidelity analogue
`re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ F(ρ i, ρ j)` is **Rotfel'd's trace inequality**
(`ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm`, `tr √(∑ⱼ Bⱼ) ≤ ∑ⱼ tr √Bⱼ` applied
to `Bⱼ = √ρᵢ ρⱼ √ρᵢ`), which holds for every family of positive operators with no commutativity or
normalization hypothesis.  It thus discharges the identification clause **outright** in the fidelity
metric — the coset reduced states then need only their fidelity collision sum controlled (a counting
task), not the paired-trace inequality.

It composes the per-state reduction
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt`
(`1 − p(some i ∣ ρ i) ≤ 2·(re tr(√S₀ · √ρᵢ) − 1)`) with the Rotfel'd fidelity-sum bound, peeling the
`−1` with the diagonal fidelity `F(ρ i, ρ i) = 1` (`State.fidelity_self`); the fidelity terms are
read off as trace norms `F(ρ i, ρ j) = ‖√ρᵢ √ρⱼ‖₁` (`State.fidelity_eq_traceNorm`).  Stated over
`State.prettyGoodMeasurement` / `State.fidelity`. -/
theorem State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_fidelity
    [DecidableEq ι] (ρ : ι → State S) (i : ι) :
    1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      ≤ 2 * ∑ j ∈ Finset.univ.erase i, (ρ i).fidelity (ρ j) := by
  have hred := State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt ρ i
  have hnn : ∀ j, (0 : S.space →L[ℂ] S.space) ≤ (ρ j).op :=
    fun j => (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ j).isPositive_op
  have hbound := ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm
    (fun j => (ρ j).op) hnn i
  -- Rewrite each pairwise trace norm as the fidelity `F(ρ i, ρ j)`.
  have hfid : ∀ j, (cfc Real.sqrt (ρ i).op * cfc Real.sqrt (ρ j).op).traceNorm
      = (ρ i).fidelity (ρ j) := fun j => (State.fidelity_eq_traceNorm (ρ i) (ρ j)).symm
  rw [Finset.sum_congr rfl (fun j _ => hfid j)] at hbound
  -- `∑ⱼ F(ρᵢ, ρⱼ) = F(ρᵢ, ρᵢ) + ∑_{j≠i} F = 1 + ∑_{j≠i} F`.
  have hdiag : ∑ j, (ρ i).fidelity (ρ j)
      = (ρ i).fidelity (ρ i) + ∑ j ∈ Finset.univ.erase i, (ρ i).fidelity (ρ j) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [(ρ i).fidelity_self] at hdiag
  rw [hdiag] at hbound
  linarith

/-- **The pretty-good discrimination measurement is inconclusive with probability zero on a family
state** (Nielsen & Chuang, Problem 5.5).  For a finite family `ρ : ι → State S` with total operator
`S₀ = ∑ⱼ ρⱼ.op`, measuring `State.prettyGoodMeasurement ρ` on one of the family states `ρ i` never
returns the junk outcome:

`p(none ∣ ρ i) = 0`.

The junk effect is `1 − ∑ⱼ Eⱼ = 1 − Π_{S₀}`, where `Π_{S₀} = S₀⁻¹ᐟ² · S₀ · S₀⁻¹ᐟ²` is the support
projection of the total operator; since `ρᵢ.op ≤ S₀` its range lies in that of `S₀`, so `Π_{S₀}`
fixes `ρᵢ.op` (`ContinuousLinearMap.mul_genInvSqrt_mul_self_mul_genInvSqrt_of_le`) and the junk
trace `re tr((1 − Π_{S₀}) ρᵢ) = re tr(ρᵢ) − re tr(Π_{S₀} ρᵢ) = 1 − 1 = 0`.  This is the
completeness of the
pretty-good measurement *on its own family*: no probability leaks to the inconclusive outcome, so
the identification error decomposes exactly into the off-diagonal confusion probabilities
(`State.one_sub_prettyGoodMeasurement_bornProb_self_eq_sum`). -/
theorem State.prettyGoodMeasurement_bornProb_none_self_eq_zero (ρ : ι → State S) (i : ι) :
    (State.prettyGoodMeasurement ρ).bornProb (ρ i) none = 0 := by
  have hρS : (ρ i).op ≤ ∑ j, (ρ j).op :=
    Finset.single_le_sum (f := fun j => (ρ j).op)
      (fun j _ => (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ j).isPositive_op)
      (Finset.mem_univ i)
  have hfork := ContinuousLinearMap.mul_genInvSqrt_mul_self_mul_genInvSqrt_of_le
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ i).isPositive_op) hρS
  rw [State.prettyGoodMeasurement_bornProb_none, ← Finset.sum_mul, ← Finset.mul_sum,
    ← ContinuousLinearMap.mul_def, sub_mul, one_mul, ContinuousLinearMap.toLinearMap_sub, map_sub]
  -- `tr(Π_{S₀} · ρᵢ) = tr(ρᵢ · Π_{S₀}) = tr ρᵢ` (trace cyclicity + support-projection identity).
  have hcyc : (LinearMap.trace ℂ S.space)
        (((∑ j, (ρ j).op).genInvSqrt * (∑ k, (ρ k).op) * (∑ j, (ρ j).op).genInvSqrt * (ρ i).op :
          S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)
      = (LinearMap.trace ℂ S.space) ((ρ i).op : S.space →ₗ[ℂ] S.space) := by
    rw [ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
        ← ContinuousLinearMap.toLinearMap_mul, hfork]
  rw [hcyc, sub_self, map_zero]

/-- **The pretty-good measurement fully classifies each family state** (Nielsen & Chuang, Problem
5.5).  For a finite family `ρ : ι → State S`, the identification outcomes `some j` exhaust the
probability on any family state `ρ i`:

`∑ⱼ p(some j ∣ ρ i) = 1`.

This is the measurement's total-probability law `Measurement.sum_bornProb_eq_one` over `Option ι`
together with the vanishing inconclusive probability
`State.prettyGoodMeasurement_bornProb_none_self_eq_zero` (`p(none ∣ ρ i) = 0`).  It is the exact
book-keeping identity behind the per-state error decomposition below. -/
theorem State.sum_prettyGoodMeasurement_bornProb_some_self_eq_one (ρ : ι → State S) (i : ι) :
    ∑ j, (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j) = 1 := by
  have htot := (State.prettyGoodMeasurement ρ).sum_bornProb_eq_one (ρ i)
  rw [Fintype.sum_option, State.prettyGoodMeasurement_bornProb_none_self_eq_zero, zero_add] at htot
  exact htot

/-- **The exact per-state pretty-good identification error is the total confusion probability**
(Nielsen & Chuang, Problem 5.5 — the exact per-state form of the Ettinger–Høyer–Knill discrimination
step).  For a finite family `ρ : ι → State S`, the deficit of correctly identifying `ρ i` with the
pretty-good measurement equals the total probability of *confusing* it with another family member:

`1 − p(some i ∣ ρ i) = ∑_{j ≠ i} p(some j ∣ ρ i)`.

This is an **exact identity**, not the loose bound `≤ 2·(1 − re tr(√ρᵢ · S₀⁻¹ᐟ² · ρᵢ))`
(`State.one_sub_prettyGoodMeasurement_bornProb_self_le`): the pretty-good measurement leaks no
probability to the inconclusive outcome on its own family
(`State.sum_prettyGoodMeasurement_bornProb_some_self_eq_one`), so the error is precisely the
off-diagonal confusion mass `∑_{j≠i} p(some j ∣ ρ i)`, with `p(some j ∣ ρ i)
= re tr(S₀⁻¹ᐟ² · ρⱼ · S₀⁻¹ᐟ² · ρᵢ)` (`State.prettyGoodMeasurement_bornProb_some`).  It is the
*per-state* (not merely summed) starting point the identification clause needs: it redirects the
remaining Ettinger–Høyer–Knill step onto bounding each confusion probability by the pairwise
affinity `A(ρᵢ, ρⱼ)`, off the summed route (whose per-state analogue reduces to the *false* operator
subadditivity `√S₀ ≤ ∑ⱼ √ρⱼ`). -/
theorem State.one_sub_prettyGoodMeasurement_bornProb_self_eq_sum [DecidableEq ι]
    (ρ : ι → State S) (i : ι) :
    1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      = ∑ j ∈ Finset.univ.erase i,
          (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j) := by
  have h := State.sum_prettyGoodMeasurement_bornProb_some_self_eq_one ρ i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
  linarith

/-- **Symmetry of the pretty-good confusion probabilities** (Nielsen & Chuang, Problem 5.5).  For a
finite family `ρ : ι → State S`, the probability that the pretty-good measurement reports `some j`
on the state `ρ i` equals the probability it reports `some i` on `ρ j`:

`p(some j ∣ ρ i) = p(some i ∣ ρ j)`.

Both are the same physical trace `re tr(S₀⁻¹ᐟ² ρⱼ S₀⁻¹ᐟ² ρᵢ)`
(`prettyGoodMeasurement_bornProb_some`, `S₀ = ∑ₖ ρₖ.op`), symmetric in `i, j` by cyclicity of the
trace (`LinearMap.trace_mul_comm`):
`tr((S₀⁻¹ᐟ² ρⱼ S₀⁻¹ᐟ²) ρᵢ) = tr((S₀⁻¹ᐟ² ρᵢ S₀⁻¹ᐟ²) ρⱼ)`.  So the **confusion matrix** of the
pretty-good measurement on its own family is symmetric.  Combined with the exact per-state error
identity `one_sub_prettyGoodMeasurement_bornProb_self_eq_sum` it recasts the identification deficit
`1 − p(some i ∣ ρ i) = ∑_{j≠i} p(some i ∣ ρ j)` — the total mass by which the *other* family states
are misidentified as `i`.  A reusable structural fact of the discrimination measurement, feeding the
Ettinger–Høyer–Knill per-pair analysis of Problem 5.5's identification clause. -/
theorem State.prettyGoodMeasurement_bornProb_some_comm (ρ : ι → State S) (i j : ι) :
    (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j)
      = (State.prettyGoodMeasurement ρ).bornProb (ρ j) (some i) := by
  rw [State.prettyGoodMeasurement_bornProb_some, State.prettyGoodMeasurement_bornProb_some]
  congr 1
  set W := (∑ k, (ρ k).op).genInvSqrt with hWdef
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
  rw [mul_assoc (W * (ρ j).op) W (ρ i).op, mul_assoc (W * (ρ i).op) W (ρ j).op,
      ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
          ← ContinuousLinearMap.toLinearMap_mul]

/-- **A Cauchy–Schwarz bound on the pretty-good confusion probabilities** (Nielsen & Chuang, Problem
5.5).  For a finite family `ρ : ι → State S`, the *confusion* probability of the pretty-good
measurement reporting `some j` on `ρ i` is controlled by the two *success* probabilities:

`p(some j ∣ ρ i)² ≤ p(some i ∣ ρ i) · p(some j ∣ ρ j)`.

Equivalently `p(some j ∣ ρ i) ≤ √(p(some i ∣ ρ i)·p(some j ∣ ρ j))`: two states cannot be confused
by more than the geometric mean of the rates at which each is correctly identified.  This is the
Cauchy–Schwarz inequality for the **Hilbert–Schmidt pairing** applied to the *amplitude operators*
`Tₐ = √W · ρₐ.op · √W` (`W = S₀⁻¹ᐟ²` the generalized inverse square root of the total
`S₀ = ∑ₖ ρₖ.op`, `√W = cfc Real.sqrt W`): each confusion trace is the pairing
`re⟨Tᵢ, Tⱼ⟩_HS = re tr(ρⱼ W ρᵢ W) = p(some j ∣ ρ i)` (via
`ContinuousLinearMap.hsPairing_mul_cfc_sqrt_eq_trace` with the sqrt-sandwich `√W·√W = W`,
`prettyGoodMeasurement_bornProb_some`, and trace cyclicity), so
`ContinuousLinearMap.norm_hsPairing_sq_le` gives
`p(some j ∣ ρ i)² ≤ ‖⟨Tᵢ, Tⱼ⟩‖² ≤ re⟨Tᵢ,Tᵢ⟩·re⟨Tⱼ,Tⱼ⟩ = p(some i ∣ ρ i)·p(some j ∣ ρ j)`, using
`p(some j ∣ ρ i) = re⟨Tᵢ,Tⱼ⟩ ≤ ‖⟨Tᵢ,Tⱼ⟩‖` (`RCLike.re_le_norm`) and
`p(some j ∣ ρ i) ≥ 0` (`Measurement.bornProb_nonneg`).  A reusable structural bound on the
discrimination measurement, part of the per-pair analysis of Problem 5.5's identification clause. -/
theorem State.prettyGoodMeasurement_bornProb_some_sq_le (ρ : ι → State S) (i j : ι) :
    ((State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j)) ^ 2
      ≤ (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
        * (State.prettyGoodMeasurement ρ).bornProb (ρ j) (some j) := by
  classical
  set W : S.space →L[ℂ] S.space := (∑ k, (ρ k).op).genInvSqrt with hWdef
  have hWnn : (0 : S.space →L[ℂ] S.space) ≤ W :=
    ContinuousLinearMap.genInvSqrt_nonneg
      (Finset.sum_nonneg fun k _ =>
        (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ k).isPositive_op)
  set r : S.space →L[ℂ] S.space := cfc Real.sqrt W with hrdef
  have hrsa : IsSelfAdjoint r := by rw [hrdef]; exact (cfc_real_sqrt_nonneg W).isSelfAdjoint
  have hrr : r * r = W := cfc_real_sqrt_mul_self_of_nonneg hWnn
  -- The pairing→trace identity `⟨X·√W, Y·√W⟩_HS = tr(Y† X W)`.
  have hgen : ∀ X Y : S.space →L[ℂ] S.space, (X * r).hsPairing (Y * r)
      = (LinearMap.trace ℂ S.space)
          (↑(ContinuousLinearMap.adjoint Y * X * W) : S.space →ₗ[ℂ] S.space) :=
    fun X Y => ContinuousLinearMap.hsPairing_mul_cfc_sqrt_eq_trace hWnn X Y
  -- Each confusion probability is the real HS pairing of the amplitude operators `Tₐ = √W ρₐ √W`.
  have hval : ∀ a b, RCLike.re ((r * (ρ a).op * r).hsPairing (r * (ρ b).op * r))
      = (State.prettyGoodMeasurement ρ).bornProb (ρ a) (some b) := by
    intro a b
    rw [State.prettyGoodMeasurement_bornProb_some]
    congr 1
    rw [hgen (r * (ρ a).op) (r * (ρ b).op),
        ← ContinuousLinearMap.star_eq_adjoint, star_mul, hrsa.star_eq,
        (ρ b).isPositive_op.isSelfAdjoint.star_eq,
        show (ρ b).op * r * (r * (ρ a).op) * W = (ρ b).op * (r * r) * (ρ a).op * W by
          simp only [mul_assoc], hrr,
        ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
            ← ContinuousLinearMap.toLinearMap_mul]
    congr 2
  have hnn : 0 ≤ (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j) :=
    Measurement.bornProb_nonneg _ _ _
  have hle : (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j)
      ≤ ‖(r * (ρ i).op * r).hsPairing (r * (ρ j).op * r)‖ := by
    rw [← hval i j]; exact RCLike.re_le_norm _
  have hcs := ContinuousLinearMap.norm_hsPairing_sq_le
    (r * (ρ i).op * r) (r * (ρ j).op * r)
  rw [hval i i, hval j j] at hcs
  calc ((State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j)) ^ 2
      ≤ ‖(r * (ρ i).op * r).hsPairing (r * (ρ j).op * r)‖ ^ 2 := pow_le_pow_left₀ hnn hle 2
    _ ≤ _ := hcs

/-- **The amplitude operator** `Tᵢ = √W · ρᵢ.op · √W` of the family state `ρ i` for the pretty-good
discrimination measurement of `ρ : ι → State S`, where `W = S₀⁻¹ᐟ²` (`= (∑ₖ ρₖ.op).genInvSqrt`) is
the generalized inverse square root of the total `S₀ = ∑ₖ ρₖ.op` and `√W = cfc Real.sqrt W`.

This is the **symmetric** square-root factorisation of the pretty-good confusion: each `Tᵢ` is a
*positive* operator (`prettyGoodMeasurementAmplitude_nonneg`), the confusion probability is the
Hilbert–Schmidt overlap `p(some j ∣ ρ i) = re tr(Tᵢ Tⱼ)`
(`prettyGoodMeasurement_bornProb_some_eq_re_trace_amplitude`), and the identification error is the
off-diagonal amplitude-overlap sum `1 − p(some i ∣ ρ i) = ∑_{j ≠ i} re tr(Tᵢ Tⱼ)`
(`one_sub_prettyGoodMeasurement_bornProb_self_eq_re_trace_amplitude_sum`).  It is the reusable
construction the per-pair Barnum–Knill affinity bound `re tr(Tᵢ Tⱼ) ≤ C·A(ρ i, ρ j)` of Problem
5.5's identification clause is stated over.  Distinct from the pretty-good *effect* `Eᵢ = W ρᵢ W`
(which is trace-equal, `re tr(Tᵢ Tⱼ) = re tr(Eⱼ ρᵢ) = p(some j ∣ ρ i)`, but not manifestly positive
as a Hilbert–Schmidt factor). -/
noncomputable def State.prettyGoodMeasurementAmplitude (ρ : ι → State S) (i : ι) :
    S.space →L[ℂ] S.space :=
  cfc Real.sqrt (∑ k, (ρ k).op).genInvSqrt * (ρ i).op
    * cfc Real.sqrt (∑ k, (ρ k).op).genInvSqrt

/-- **The pretty-good amplitude operator is positive** (Nielsen & Chuang, Problem 5.5).  The
amplitude operator `Tᵢ = √W · ρᵢ.op · √W` (`State.prettyGoodMeasurementAmplitude`) of a family state
`ρ i` is a positive operator:

`0 ≤ Tᵢ`.

It is the conjugation of the positive `ρ i.op` (`State.isPositive_op`) by the self-adjoint `√W`
(`IsSelfAdjoint.conjugate_nonneg`, `√W` self-adjoint as the CFC image of a real function of the
positive `W = (∑ₖ ρₖ.op).genInvSqrt`).  Positivity of `Tᵢ, Tⱼ` makes the confusion probability
`p(some j ∣ ρ i) = re tr(Tᵢ Tⱼ)` a Hilbert–Schmidt overlap of two *positive* operators. -/
theorem State.prettyGoodMeasurementAmplitude_nonneg (ρ : ι → State S) (i : ι) :
    (0 : S.space →L[ℂ] S.space) ≤ State.prettyGoodMeasurementAmplitude ρ i :=
  IsSelfAdjoint.conjugate_nonneg
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ i).isPositive_op)
    (cfc_real_sqrt_nonneg (∑ k, (ρ k).op).genInvSqrt).isSelfAdjoint

/-- **The confusion probability of the pretty-good measurement as an amplitude-operator trace**
(Nielsen & Chuang, Problem 5.5).  For a finite family `ρ : ι → State S` with total operator
`S₀ = ∑ₖ ρₖ.op` and amplitude operators `Tₐ = √W · ρₐ.op · √W`
(`State.prettyGoodMeasurementAmplitude`, `W = S₀⁻¹ᐟ²`), the probability that the pretty-good
discrimination measurement reports outcome `some j` on the state `ρ i` is the Hilbert–Schmidt inner
product of the two amplitude operators:

`p(some j ∣ ρ i) = re tr(Tᵢ · Tⱼ)`.

Both sides are the physical trace `re tr(ρᵢ · W · ρⱼ · W)`: the pretty-good Born rule gives
`p(some j ∣ ρ i) = re tr((W ρⱼ W) · ρᵢ)` (`prettyGoodMeasurement_bornProb_some`,
`ContinuousLinearMap.mul_def`), while `Tᵢ · Tⱼ = √W ρᵢ (√W √W) ρⱼ √W = √W ρᵢ W ρⱼ √W`
(`√W · √W = W`, `cfc_real_sqrt_mul_self_of_nonneg`), whose trace equals `tr(W ρᵢ W ρⱼ)` by
cyclicity (`LinearMap.trace_mul_comm`, grouping `(W ρᵢ)(W ρⱼ)`).  The two amplitude operators
`Tᵢ, Tⱼ` are each positive (`prettyGoodMeasurementAmplitude_nonneg`), so `re tr(Tᵢ Tⱼ) ≥ 0` and the
confusion is a genuine Hilbert–Schmidt overlap — the reusable operator form that the per-pair
Barnum–Knill affinity bound of Problem 5.5's identification clause is stated over
(`p(some j ∣ ρ i) ≤ C · A(ρ i, ρ j)`, still to prove). -/
theorem State.prettyGoodMeasurement_bornProb_some_eq_re_trace_amplitude
    (ρ : ι → State S) (i j : ι) :
    (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j)
      = RCLike.re ((LinearMap.trace ℂ S.space)
          ((State.prettyGoodMeasurementAmplitude ρ i * State.prettyGoodMeasurementAmplitude ρ j :
            S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) := by
  classical
  simp only [State.prettyGoodMeasurementAmplitude]
  set W : S.space →L[ℂ] S.space := (∑ k, (ρ k).op).genInvSqrt with hWdef
  have hWnn : (0 : S.space →L[ℂ] S.space) ≤ W :=
    ContinuousLinearMap.genInvSqrt_nonneg (Finset.sum_nonneg fun k _ =>
      (ContinuousLinearMap.nonneg_iff_isPositive).mpr (ρ k).isPositive_op)
  set r : S.space →L[ℂ] S.space := cfc Real.sqrt W with hrdef
  have hrr : r * r = W := cfc_real_sqrt_mul_self_of_nonneg hWnn
  -- Both sides equal the physical trace `re tr((W ρᵢ)(W ρⱼ)) = re tr(W ρᵢ W ρⱼ)`.
  have hLHS : (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some j)
      = RCLike.re ((LinearMap.trace ℂ S.space)
          (((W * (ρ i).op) * (W * (ρ j).op) : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) := by
    rw [State.prettyGoodMeasurement_bornProb_some, ← ContinuousLinearMap.mul_def,
      mul_assoc (W * (ρ j).op) W (ρ i).op,
      ContinuousLinearMap.toLinearMap_mul (W * (ρ j).op) (W * (ρ i).op), LinearMap.trace_mul_comm,
      ← ContinuousLinearMap.toLinearMap_mul]
  have hRHS : RCLike.re ((LinearMap.trace ℂ S.space)
        (((r * (ρ i).op * r) * (r * (ρ j).op * r) : S.space →L[ℂ] S.space)
          : S.space →ₗ[ℂ] S.space))
      = RCLike.re ((LinearMap.trace ℂ S.space)
          (((W * (ρ i).op) * (W * (ρ j).op) : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) := by
    congr 1
    -- `(r ρᵢ r)(r ρⱼ r) = r · (ρᵢ W ρⱼ) · r`; cycle the trailing `r` to the front (`r · r = W`).
    rw [show (r * (ρ i).op * r) * (r * (ρ j).op * r) = r * ((ρ i).op * W * (ρ j).op) * r by
          rw [← hrr]; simp only [mul_assoc],
      ContinuousLinearMap.toLinearMap_mul (r * ((ρ i).op * W * (ρ
          j).op)) r, LinearMap.trace_mul_comm,
      ← ContinuousLinearMap.toLinearMap_mul,
      show r * (r * ((ρ i).op * W * (ρ j).op)) = (W * (ρ i).op) * (W * (ρ j).op) by
        rw [← mul_assoc, hrr]; simp only [mul_assoc]]
  rw [hLHS, hRHS]

/-- **The identification error of the pretty-good measurement as a sum of amplitude-overlap traces**
(Nielsen & Chuang, Problem 5.5).  For a finite family `ρ : ι → State S` with total operator
`S₀ = ∑ₖ ρₖ.op` and amplitude operators `Tₐ = √W ρₐ √W` (`W = S₀⁻¹ᐟ²`), the deficit of the
probability of correctly identifying `ρ i` is the **off-diagonal amplitude-overlap sum**:

`1 − p(some i ∣ ρ i) = ∑_{j ≠ i} re tr(Tᵢ · Tⱼ)`.

It combines the exact junk-free error decomposition
`State.one_sub_prettyGoodMeasurement_bornProb_self_eq_sum`
(`1 − p(some i ∣ ρ i) = ∑_{j ≠ i} p(some j ∣ ρ i)`, the pretty-good measurement leaking no
probability to its inconclusive outcome on a family state) with the amplitude-trace form of each
confusion probability (`prettyGoodMeasurement_bornProb_some_eq_re_trace_amplitude`).  This is the
operator handle for the linear-sample-count identification clause: the remaining
Ettinger–Høyer–Knill step of Problem 5.5 bounds each amplitude overlap `re tr(Tᵢ Tⱼ)` by the
pairwise affinity `A(ρ i, ρ j) = re tr(√ρᵢ √ρⱼ)`, turning this into the pairwise-affinity sum
`∑_{j ≠ i} A(ρ i, ρ j)` the near-orthogonality theorems supply. -/
theorem State.one_sub_prettyGoodMeasurement_bornProb_self_eq_re_trace_amplitude_sum
    [DecidableEq ι] (ρ : ι → State S) (i : ι) :
    1 - (State.prettyGoodMeasurement ρ).bornProb (ρ i) (some i)
      = ∑ j ∈ Finset.univ.erase i, RCLike.re ((LinearMap.trace ℂ S.space)
          ((State.prettyGoodMeasurementAmplitude ρ i * State.prettyGoodMeasurementAmplitude ρ j :
            S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) := by
  rw [State.one_sub_prettyGoodMeasurement_bornProb_self_eq_sum]
  exact Finset.sum_congr rfl fun j _ =>
    State.prettyGoodMeasurement_bornProb_some_eq_re_trace_amplitude ρ i j

end AxQM
