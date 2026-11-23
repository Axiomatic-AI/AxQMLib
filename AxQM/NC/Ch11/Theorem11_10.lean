/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyMixture
import AxQM.Postulates.API.MaximallyMixed
import AxQM.NC.Ch11.Theorem11_6
import AxQM.NC.Ch9.Theorem9_3
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# N&C Theorem 11.10 — Entropy of a mixture of quantum states

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.10, p. 518.

For a mixture `ρ = ∑ᵢ pᵢ ρᵢ` of quantum states `ρᵢ` with a probability distribution `p`, the von
Neumann entropy obeys the upper bound (eq. (11.87))

`S(ρ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`,

with equality **iff** the states `ρᵢ` have support on orthogonal subspaces. Paired with the
concavity inequality `∑ᵢ pᵢ S(ρᵢ) ≤ S(ρ)` (Theorem 11.8), this bounds the Holevo χ quantity
`χ = S(ρ) − ∑ᵢ pᵢ S(ρᵢ)` between `0` and `H(p)` (eq. (11.86)).

## What is proved here

This file proves two results about `State.vonNeumannEntropy`, `State.mix`, and
`State.traceDistance`, using the Fannes inequality (`State.abs_vonNeumannEntropy_sub_le_fannes`,
Theorem 11.6):

* `AxQM.State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance` — **continuity of the von
  Neumann entropy in trace distance**: if `σᵢ → ρ` in trace distance along a filter, then
  `S(σᵢ) → S(ρ)`. A reusable Fannes corollary.
* `AxQM.State.vonNeumannEntropy_mix_le'` — the **general** (faithfulness-free) upper bound
  `S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)` for an arbitrary family of states, i.e. eq. (11.87) exactly as
  N&C state it (no strict-positivity hypothesis).

The remaining results, whose statements are in terms of the density operators `.op`, are in
`AxQM/Postulates/API/`:

* `AxQM.State.vonNeumannEntropy_mix_le`
  (`AxQM/Postulates/API/EntropyMixture.lean`) — the *faithful* form of the bound (each
  `(ρ i).op` strictly positive), derived from the `ToMathlib/` bound
  `ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_mix_le_sum_add_entropy`. The general bound
  `vonNeumannEntropy_mix_le'` here is obtained *from* it by perturbation (below).
* `AxQM.State.vonNeumannEntropy_mix_of_orthonormal_rankOne`
  (`AxQM/Postulates/API/EntropyOrthogonalMixture.lean`) — the equality "if" engine:
  `S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ) + H(p)` when the components carry jointly-orthonormal eigen-
  decompositions (= orthogonal supports), N&C's own eq. (11.92) computation.
* `AxQM.State.vonNeumannEntropy_mix_eq_iff_orthogonal`
  (`AxQM/Postulates/API/EntropyMixtureReverse.lean`) — **the equality condition itself**:
  `S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)` iff the components of non-zero probability have orthogonal
  supports (`(ρ i).op * (ρ j).op = 0` for `i ≠ j`, `pᵢ, pⱼ ≠ 0`). Its `⟹` direction is N&C's mixed-
  case argument (eq. (11.92)–(11.94)): reduce the mixture to its combined eigen-ensemble
  `{pᵢ λᵢₖ, |eᵢₖ⟩}` and invoke the pure-state converse
  `AxQM.Ensemble.inner_states_eq_zero_of_vonNeumannEntropy_toState_eq`
  (eq. (11.88)–(11.91)); its `⟸` direction is the orthogonal-support "if" engine above, restricted
  to the positive-weight components.

## Proof route for the general bound

N&C prove the bound by an auxiliary-system argument (purify, then invoke Theorem 11.9). The library
takes the **relative-entropy route** for the *faithful* case (`vonNeumannEntropy_mix_le`), which
needs each `ρᵢ` strictly positive because the antitonicity lever requires the reference `pᵢ ρᵢ`
strictly positive.

The general bound removes that hypothesis by **perturbation**: for `εₙ = 1/(n+1) ↓ 0`, replace each
`ρᵢ` by the faithful state `ρᵢ⁽ⁿ⁾ = (1−εₙ) ρᵢ + εₙ (I/d)` (strictly positive, since the maximally
mixed `I/d` is), apply the faithful bound to the family `ρ⁽ⁿ⁾`, and pass to the limit `n → ∞`. Both
sides are continuous in trace distance (via Fannes,
`tendsto_vonNeumannEntropy_of_tendsto_traceDistance`), and `ρᵢ⁽ⁿ⁾ → ρᵢ`, `μ⁽ⁿ⁾ → μ` in trace
distance (joint convexity of the trace distance under mixing), so the faithful inequality survives
the limit. This keeps full N&C generality.

The equality condition (equality iff the `ρᵢ` have orthogonal supports) is assembled as
`AxQM.State.vonNeumannEntropy_mix_eq_iff_orthogonal`
(`AxQM/Postulates/API/EntropyMixtureReverse.lean`, listed above).
-/

namespace AxQM

open Filter
open scoped Topology

variable {S : QSystem}

/-- **Continuity of the von Neumann entropy in trace distance.** If a family of states `σ i`
converges to `ρ` in trace distance along a filter `l`, then their von Neumann entropies converge:
`S(σ i) → S(ρ)`. This is a direct corollary of Fannes' inequality
(`State.abs_vonNeumannEntropy_sub_le_fannes`): the entropy gap is squeezed between `0` and
`2 D · log d + η(2 D)`, which tends to `0` as the trace distance `D` does (`η = Real.negMulLog` is
continuous at `0` with `η 0 = 0`). -/
theorem State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance {ι : Type*} {l : Filter ι}
    (σ : ι → State S) (ρ : State S)
    (h : Tendsto (fun i => (σ i).traceDistance ρ) l (𝓝 0)) :
    Tendsto (fun i => (σ i).vonNeumannEntropy) l (𝓝 ρ.vonNeumannEntropy) := by
  have h2 : Tendsto (fun i => 2 * (σ i).traceDistance ρ) l (𝓝 0) := by
    simpa using h.const_mul 2
  have hA : Tendsto (fun i => 2 * (σ i).traceDistance ρ * Real.log (S.dim : ℝ)) l (𝓝 0) := by
    simpa using h2.mul_const (Real.log (S.dim : ℝ))
  have hB : Tendsto (fun i => Real.negMulLog (2 * (σ i).traceDistance ρ)) l (𝓝 0) := by
    have hcomp := (Real.continuous_negMulLog.tendsto (0 : ℝ)).comp h2
    rw [Real.negMulLog_zero] at hcomp
    exact hcomp
  have hg : Tendsto (fun i => 2 * (σ i).traceDistance ρ * Real.log (S.dim : ℝ)
      + Real.negMulLog (2 * (σ i).traceDistance ρ)) l (𝓝 0) := by
    simpa using hA.add hB
  have hev : ∀ᶠ i in l, ‖(σ i).vonNeumannEntropy - ρ.vonNeumannEntropy‖
      ≤ 2 * (σ i).traceDistance ρ * Real.log (S.dim : ℝ)
        + Real.negMulLog (2 * (σ i).traceDistance ρ) := by
    have hsmall : ∀ᶠ i in l, 2 * (σ i).traceDistance ρ < Real.exp (-1) :=
      h2.eventually (Iio_mem_nhds (Real.exp_pos _))
    filter_upwards [hsmall] with i hi
    rw [Real.norm_eq_abs]
    exact (σ i).abs_vonNeumannEntropy_sub_le_fannes ρ hi.le
  have hsub : Tendsto (fun i => (σ i).vonNeumannEntropy - ρ.vonNeumannEntropy) l (𝓝 0) :=
    squeeze_zero_norm' hev hg
  simpa using hsub.add_const ρ.vonNeumannEntropy

/-- **Entropy of a mixture — upper bound, general form** (Nielsen & Chuang, Theorem 11.10,
eq. (11.87)). For *any* probability distribution `p` and *any* family `ρ : ι → State S` of quantum
states, the von Neumann entropy of the mixture is bounded by the average component entropy plus the
Shannon entropy of the weights:

`S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`.

This is the faithfulness-free strengthening of `State.vonNeumannEntropy_mix_le` (which assumes each
`(ρ i).op` strictly positive): it is exactly N&C eq. (11.87), with no restriction on the states.

The proof perturbs each component toward the maximally mixed state,
`ρᵢ⁽ⁿ⁾ = (1 − εₙ) ρᵢ + εₙ (I/d)` with `εₙ = 1/(n+1) ↓ 0` (strictly positive, so the faithful bound
applies), and passes to the limit: both `S(∑ᵢ pᵢ ρᵢ⁽ⁿ⁾) → S(∑ᵢ pᵢ ρᵢ)` and
`∑ᵢ pᵢ S(ρᵢ⁽ⁿ⁾) → ∑ᵢ pᵢ S(ρᵢ)` by continuity of the entropy in trace distance
(`State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance`), the trace-distance convergence coming
from joint convexity of the trace distance under mixing. -/
theorem State.vonNeumannEntropy_mix_le' {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
      ≤ ∑ i, p i * (ρ i).vonNeumannEntropy + Real.entropy p := by
  classical
  -- The weights sum to `1`, so the index type is nonempty and `S.space` is nontrivial; hence the
  -- maximally mixed reference state `I/d` exists.
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have : Nontrivial S.space := State.nontrivial_space (ρ i₀)
  set τ : State S := maximallyMixedState S with hτ
  have hτpos : IsStrictlyPositive τ.op := by
    rw [hτ]; exact maximallyMixedState_isStrictlyPositive S
  -- Perturbation weights `εₙ = 1/(n+1) ∈ (0, 1]`, `εₙ ↓ 0`.
  have hεpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hεle : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]; linarith
  have h0 : ∀ n : ℕ, (0 : ℝ) ≤ 1 - 1 / (n + 1) := fun n => by linarith [hεle n]
  have h1 : ∀ n : ℕ, (1 : ℝ) - 1 / (n + 1) ≤ 1 := fun n => by linarith [hεpos n]
  have hεtendsto : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- Perturbed components `ρᵢ⁽ⁿ⁾ = (1 − εₙ) ρᵢ + εₙ τ`.
  set F : ℕ → ι → State S := fun n i => State.mixPair (h0 n) (h1 n) (ρ i) τ with hF
  -- Each perturbed component is faithful (strictly positive).
  have hposN : ∀ n i, IsStrictlyPositive (F n i).op := by
    intro n i
    simp only [hF, State.mixPair_op, Complex.coe_smul]
    refine IsStrictlyPositive.nonneg_add ?_ ?_
    · exact smul_nonneg (h0 n) ((ρ i).isDensity.nonneg)
    · have hpos : (0 : ℝ) < 1 - (1 - 1 / (n + 1)) := by have := hεpos n; linarith
      exact IsStrictlyPositive.smul hpos hτpos
  -- Each component converges to `ρᵢ` in trace distance.
  have hDcomp : ∀ i, Tendsto (fun n => (F n i).traceDistance (ρ i)) atTop (𝓝 0) := by
    intro i
    have hg : Tendsto (fun n : ℕ => 1 / (n + 1) * τ.traceDistance (ρ i)) atTop (𝓝 0) := by
      simpa using hεtendsto.mul_const (τ.traceDistance (ρ i))
    refine squeeze_zero (fun n => State.traceDistance_nonneg _ _) (fun n => ?_) hg
    simp only [hF]
    have hconv := State.traceDistance_mixPair_jointly_convex (h0 n) (h1 n) (ρ i) τ (ρ i) (ρ i)
    rw [State.mixPair_self (h0 n) (h1 n) (ρ i), State.traceDistance_self] at hconv
    exact hconv.trans (le_of_eq (by ring))
  -- Hence each component entropy converges, and the mixture converges in trace distance.
  have hScomp : ∀ i, Tendsto (fun n => (F n i).vonNeumannEntropy) atTop
      (𝓝 (ρ i).vonNeumannEntropy) := fun i =>
    State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance (fun n => F n i) (ρ i) (hDcomp i)
  have hsumD : Tendsto (fun n => ∑ i, p i * (F n i).traceDistance (ρ i)) atTop (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun i _ => (hDcomp i).const_mul (p i))
    simpa using this
  have hμlim : Tendsto (fun n => (State.mix p hp hsum (F n)).vonNeumannEntropy) atTop
      (𝓝 (State.mix p hp hsum ρ).vonNeumannEntropy) := by
    apply State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance
    refine squeeze_zero (fun n => State.traceDistance_nonneg _ _) (fun n => ?_) hsumD
    exact State.traceDistance_mix_jointly_convex p hp hsum (F n) ρ
  -- Assemble: the faithful bound holds along the sequence and both sides converge.
  have hbound : ∀ n, (State.mix p hp hsum (F n)).vonNeumannEntropy
      ≤ ∑ i, p i * (F n i).vonNeumannEntropy + Real.entropy p :=
    fun n => State.vonNeumannEntropy_mix_le p hp hsum (F n) (fun i => hposN n i)
  have hRHSlim : Tendsto (fun n => ∑ i, p i * (F n i).vonNeumannEntropy + Real.entropy p) atTop
      (𝓝 (∑ i, p i * (ρ i).vonNeumannEntropy + Real.entropy p)) := by
    have hsumS : Tendsto (fun n => ∑ i, p i * (F n i).vonNeumannEntropy) atTop
        (𝓝 (∑ i, p i * (ρ i).vonNeumannEntropy)) :=
      tendsto_finsetSum Finset.univ (fun i _ => (hScomp i).const_mul (p i))
    simpa using hsumS.add_const (Real.entropy p)
  exact le_of_tendsto_of_tendsto' hμlim hRHSlim hbound

end AxQM
