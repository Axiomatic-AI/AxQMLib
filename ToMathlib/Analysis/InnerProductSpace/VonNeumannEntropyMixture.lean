/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Entropy of a mixture — relative-entropy levers (Nielsen & Chuang, Theorem 11.10)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 11.10 (the "entropy of a
mixture" upper bound) states that for a mixture `ρ = ∑ᵢ pᵢ ρᵢ` of density operators,

`S(ρ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`,

with equality iff the `ρᵢ` have support on orthogonal subspaces. Together with the concavity
inequality `∑ᵢ pᵢ S(ρᵢ) ≤ S(ρ)` (Theorem 11.8,
`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_convex_combination_le`) this bounds the *Holevo
χ quantity* `χ := S(ρ) − ∑ᵢ pᵢ S(ρᵢ)` between `0` and `H(p)`.

This file develops the two operator-level **relative-entropy lemmas** on which the upper bound
rests. Writing the χ quantity as an average of relative entropies,
`χ = ∑ᵢ pᵢ D(ρᵢ ‖ ρ)`, the bound `χ ≤ H(p)` follows term by term from
`D(ρᵢ ‖ ρ) ≤ D(ρᵢ ‖ pᵢ ρᵢ) = −log pᵢ`: the inequality is *antitonicity of the relative entropy in
its second argument* (`ρ ≥ pᵢ ρᵢ` shrinks the divergence), and the equality is the scaling law
`D(r ‖ c • r) = −log c` (Problem 11.2). The two lemmas proved here are exactly:

* the antitonicity `quantumRelativeEntropy_le_of_le_right`, and
* the χ-as-average identity `sum_mul_quantumRelativeEntropy_mix`.

## Main results

* `ContinuousLinearMap.quantumRelativeEntropy_le_of_le_right`: **antitonicity of the quantum
  relative entropy in the second argument.** For a positive `ρ` and strictly positive `σ ≤ τ`,
  `D(ρ ‖ τ) ≤ D(ρ ‖ σ)`. Enlarging the reference operator (in the Loewner order) cannot increase
  the divergence, because `log` is operator monotone.
* `ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix`: the **Holevo χ identity** — for a
  mixture `μ = ∑ᵢ pᵢ ρᵢ` of density operators, the weighted sum of relative entropies against the
  mixture equals the concavity gap, `∑ᵢ pᵢ D(ρᵢ ‖ μ) = S(μ) − ∑ᵢ pᵢ S(ρᵢ)`.
* `ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_mix_le_sum_add_entropy`: the
  **entropy-of-a-mixture upper bound** itself — for a mixture `μ = ∑ᵢ pᵢ ρᵢ` of *strictly positive*
  density operators with `p` a subprobability weight vector, `S(μ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`, where
  `H(p) = Real.entropy p` is the Shannon entropy. This assembles the two levers with the scaling law
  `D(ρᵢ ‖ pᵢ • ρᵢ) = −log pᵢ` (Problem 11.2, `quantumRelativeEntropy_smul_smul`) term by term.

The strict-positivity hypothesis on the components is inherent to this relative-entropy route (the
antitonicity lever needs the reference operator `pᵢ • ρᵢ` strictly positive), so this lemma
is the *faithful* form of Nielsen–Chuang Theorem 11.10 under the finite-branch faithfulness
convention. The general (possibly rank-deficient) case and the equality condition (orthogonal
supports) are handled in
`AxQM/NC/Ch11/Theorem11_10.lean`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]

/-- **Antitonicity of the quantum relative entropy in its second argument.** For a positive
operator `ρ` and strictly positive operators `σ ≤ τ` (Loewner order),
`D(ρ ‖ τ) ≤ D(ρ ‖ σ)`: enlarging the reference operator cannot increase the divergence.

The proof rests on the operator monotonicity of the logarithm (`CFC.log_le_log`): since
`σ ≤ τ` with `σ` strictly positive, `log σ ≤ log τ`, so `log τ − log σ ≥ 0`. The two relative
entropies share the `tr(ρ log ρ)` term, so their difference is
`re tr((log τ − log σ) ρ) ≥ 0`, non-negative because it is the trace of a product of positive
operators (`re_trace_mul_nonneg_of_nonneg`).

This is the monotonicity behind the entropy-of-a-mixture upper bound (Nielsen–Chuang
Theorem 11.10): applied with `σ = pᵢ ρᵢ ≤ ρ = τ` it bounds each `D(ρᵢ ‖ ρ)` by `D(ρᵢ ‖ pᵢ ρᵢ)`. -/
theorem quantumRelativeEntropy_le_of_le_right {ρ σ τ : E →L[ℂ] E} (hρ : 0 ≤ ρ)
    (hσ : IsStrictlyPositive σ) (hστ : σ ≤ τ) :
    quantumRelativeEntropy ρ τ ≤ quantumRelativeEntropy ρ σ := by
  -- `log` is operator monotone: `σ ≤ τ` with `σ` strictly positive gives `log σ ≤ log τ`.
  have hlog : cfc Real.log σ ≤ cfc Real.log τ := CFC.log_le_log hστ hσ
  rw [quantumRelativeEntropy_def, quantumRelativeEntropy_def]
  -- `re tr((log τ − log σ) ρ) ≥ 0` as the trace of a product of positive operators.
  have hdiff : 0 ≤ RCLike.re (LinearMap.trace ℂ E
      (((cfc Real.log τ - cfc Real.log σ) * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
    re_trace_mul_nonneg_of_nonneg (sub_nonneg.mpr hlog) hρ
  simp only [sub_mul, ContinuousLinearMap.toLinearMap_sub, map_sub,
      ContinuousLinearMap.toLinearMap_mul,
    Module.End.mul_eq_comp] at hdiff
  linarith [hdiff]

/-- **The Holevo χ identity.** For a mixture `μ = ∑ᵢ pᵢ ρᵢ` of density operators, the weighted
average of the relative entropies of the components against the mixture equals the concavity gap
(the Holevo χ quantity):

`∑ᵢ pᵢ D(ρᵢ ‖ μ) = S(μ) − ∑ᵢ pᵢ S(ρᵢ)`.

A pure trace identity (no constraint on the sign or sum of the `pᵢ`). Each term expands via
`D(ρᵢ ‖ μ) = −S(ρᵢ) − re tr(ρᵢ log μ)`
(`IsDensityOp.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub`); linearity of the trace over the
mixture (`re_trace_comp_clm_finset_sum_smul`) collapses the weighted sum of cross terms
`∑ᵢ pᵢ re tr(ρᵢ log μ)` to `re tr(μ log μ) = −S(μ)`
(`re_trace_cfc_log_self_eq_neg_vonNeumannEntropy`).

Combined with the concavity inequality `∑ᵢ pᵢ S(ρᵢ) ≤ S(μ)` this exhibits χ ≥ 0; combined with the
per-term bound `D(ρᵢ ‖ μ) ≤ −log pᵢ` it yields the entropy-of-a-mixture upper bound χ ≤ H(p)
(Nielsen–Chuang Theorem 11.10). -/
theorem sum_mul_quantumRelativeEntropy_mix {ι : Type*} [Fintype ι] {ρ : ι → E →L[ℂ] E}
    (hρ : ∀ i, (ρ i).IsDensityOp) (p : ι → ℝ) {μ : E →L[ℂ] E} (hμ : μ.IsDensityOp)
    (hμeq : μ = ∑ i, (p i : ℂ) • ρ i) :
    ∑ i, p i * quantumRelativeEntropy (ρ i) μ
      = μ.vonNeumannEntropy - ∑ i, p i * (ρ i).vonNeumannEntropy := by
  -- The weighted sum of cross terms `∑ᵢ pᵢ re tr(ρᵢ log μ)` collapses to `re tr(μ log μ) = −S(μ)`.
  have key : ∑ i, p i * RCLike.re (LinearMap.trace ℂ E
        ((cfc Real.log μ).toLinearMap ∘ₗ (ρ i).toLinearMap)) = -μ.vonNeumannEntropy := by
    rw [← re_trace_comp_clm_finset_sum_smul (cfc Real.log μ) ρ p, ← hμeq,
      hμ.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy]
  -- Expand each `D(ρᵢ ‖ μ) = −S(ρᵢ) − re tr(ρᵢ log μ)`.
  have hterm : ∀ i, p i * quantumRelativeEntropy (ρ i) μ =
      p i * (-(ρ i).vonNeumannEntropy) -
        p i * RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.log μ).toLinearMap ∘ₗ (ρ i).toLinearMap)) := fun i => by
    rw [(hρ i).quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub]; ring
  simp only [hterm, Finset.sum_sub_distrib, key, mul_neg, Finset.sum_neg_distrib]
  ring

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {ι : Type*} [Fintype ι] {n : Type*} [Fintype n]

open scoped ComplexOrder

set_option synthInstance.maxHeartbeats 80000 in
-- The `IsStrictlyPositive.smul` / `smul_nonneg` applications need the `PosSMulMono ℝ (E →L[ℂ] E)`
-- instance, whose synthesis on the operator algebra exceeds the default budget.
set_option maxHeartbeats 400000 in
-- The assembled proof (Loewner order + scaling law + Holevo χ) is elaboration-heavy, as in the
-- sibling `GeneralizedRelativeEntropy` file.
/-- **The entropy of a mixture of quantum states — upper bound** (Nielsen & Chuang, Theorem 11.10,
eq. (11.87)). For a mixture `μ = ∑ᵢ pᵢ ρᵢ` of *strictly positive* density operators `ρᵢ`, weighted
by a family of nonnegative reals `pᵢ`, the von Neumann entropy of the mixture is bounded by the
average entropy of the components plus the Shannon entropy of the weights:

`S(μ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`, where `H(p) = Real.entropy p = ∑ᵢ −pᵢ log pᵢ`.

The proof assembles the two relative-entropy levers with the scaling law. The Holevo χ identity
(`sum_mul_quantumRelativeEntropy_mix`) rewrites the concavity gap as the average relative entropy
`S(μ) − ∑ᵢ pᵢ S(ρᵢ) = ∑ᵢ pᵢ D(ρᵢ ‖ μ)`, and each term is bounded by `−pᵢ log pᵢ = negMulLog pᵢ`:

* for `pᵢ = 0` the term vanishes (`negMulLog 0 = 0`);
* for `pᵢ > 0`, `D(ρᵢ ‖ μ) ≤ D(ρᵢ ‖ pᵢ • ρᵢ)` by antitonicity in the reference
  (`quantumRelativeEntropy_le_of_le_right`, since `pᵢ • ρᵢ ≤ μ` in the Loewner order — the other
  summands are positive — and `pᵢ • ρᵢ` is strictly positive), and
  `D(ρᵢ ‖ pᵢ • ρᵢ) = −log pᵢ` by the scaling law `quantumRelativeEntropy_smul_smul` at `c = 1`,
  `d = pᵢ` (using `D(ρᵢ ‖ ρᵢ) = 0` and `tr ρᵢ = 1`).

Summing, `∑ᵢ pᵢ D(ρᵢ ‖ μ) ≤ ∑ᵢ negMulLog pᵢ = H(p)`, which is the claim.

The strict-positivity hypothesis on the components is inherent to this route (the antitonicity lever
requires `pᵢ • ρᵢ` strictly positive); this is the faithful form of the theorem under the
finite-branch faithfulness convention. -/
theorem IsDensityOp.vonNeumannEntropy_mix_le_sum_add_entropy
    {ρ : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hρpos : ∀ i, IsStrictlyPositive (ρ i)) (hρ : ∀ i, (ρ i).IsDensityOp) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) {μ : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} (hμ : μ.IsDensityOp)
    (hμeq : μ = ∑ i, (p i : ℂ) • ρ i) :
    μ.vonNeumannEntropy ≤ ∑ i, p i * (ρ i).vonNeumannEntropy + Real.entropy p := by
  -- `IsScalarTower ℝ ℂ (E →L[ℂ] E)` holds for a concrete Euclidean space but is not a global
  -- instance; provide it locally (as in `QuantumRelativeEntropy`).
  have : IsScalarTower ℝ ℂ (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Rewrite the mixture with real scalars for the Loewner-order argument.
  have hμeqR : μ = ∑ i, p i • ρ i := by
    rw [hμeq]
    exact Finset.sum_congr rfl fun i _ => (RCLike.real_smul_eq_coe_smul (p i) (ρ i)).symm
  -- Each component is positive.
  have hρnn : ∀ i, 0 ≤ ρ i := fun i => (IsStrictlyPositive.iff_of_unital.mp (hρpos i)).1
  -- Term-by-term bound `pᵢ D(ρᵢ ‖ μ) ≤ negMulLog pᵢ`.
  have hterm : ∀ i, p i * (ρ i).quantumRelativeEntropy μ ≤ Real.negMulLog (p i) := by
    intro i
    rcases (hp i).eq_or_lt with h0 | hpos
    · simp [← h0, Real.negMulLog]
    · -- `pᵢ • ρᵢ ≤ μ` since the omitted summands are positive.
      have hle_op : p i • ρ i ≤ μ := by
        rw [hμeqR]
        exact Finset.single_le_sum (fun j _ => smul_nonneg (hp j) (hρnn j)) (Finset.mem_univ i)
      have hσ : IsStrictlyPositive (p i • ρ i) := IsStrictlyPositive.smul hpos (hρpos i)
      -- Antitonicity of the relative entropy in the reference operator.
      have hanti : (ρ i).quantumRelativeEntropy μ ≤ (ρ i).quantumRelativeEntropy (p i • ρ i) :=
        quantumRelativeEntropy_le_of_le_right (hρnn i) hσ hle_op
      -- Scaling law: `D(ρᵢ ‖ pᵢ • ρᵢ) = −log pᵢ`.
      have hscale : (ρ i).quantumRelativeEntropy (p i • ρ i) = -Real.log (p i) := by
        have h := quantumRelativeEntropy_smul_smul (hρpos i) (hρpos i) one_pos hpos
        rw [one_smul, quantumRelativeEntropy_self, (hρ i).trace_eq_one] at h
        rw [h, RCLike.one_re, one_div, Real.log_inv]; ring
      calc p i * (ρ i).quantumRelativeEntropy μ
          ≤ p i * (ρ i).quantumRelativeEntropy (p i • ρ i) :=
            mul_le_mul_of_nonneg_left hanti (le_of_lt hpos)
        _ = Real.negMulLog (p i) := by rw [hscale, Real.negMulLog]; ring
  -- Assemble via the Holevo χ identity.
  have hHolevo := sum_mul_quantumRelativeEntropy_mix hρ p hμ hμeq
  have hsum : ∑ i, p i * (ρ i).quantumRelativeEntropy μ ≤ ∑ i, Real.negMulLog (p i) :=
    Finset.sum_le_sum fun i _ => hterm i
  rw [hHolevo] at hsum
  have hent : Real.entropy p = ∑ i, Real.negMulLog (p i) := rfl
  linarith [hsum, hent]

end ContinuousLinearMap
