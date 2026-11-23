/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Mixture
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Theorem 9.3 (Strong convexity of the trace distance)

Strong convexity of trace distance for mixtures of states and probability distributions.

The trace distance between two *mixtures* is controlled by two separate sources of
distinguishability: the classical distance `D(p, q)` between the mixing weights, plus the
average `∑ᵢ pᵢ D(ρᵢ, σᵢ)` of the distances between the paired components. N&C call `(9.46)`
the **strong convexity** of the trace distance because the joint-convexity inequality `(9.50)`
follows from it as the special case `q = p`.

## The physical form

The two mixtures `∑ᵢ pᵢ ρᵢ` and `∑ᵢ qᵢ σᵢ` are formed with `AxQM.State.mix`
(`AxQM/Postulates/API/Mixture.lean`); `D` on states is `State.traceDistance` and `D` on
distributions is `AxQM.Concrete.classicalTraceDist` (N&C `(9.1)`).

## Proof

The proof is the **trace-norm triangle-inequality** argument, which is cleaner than and stronger
than N&C's projector construction (N&C `(9.47)–(9.49)` pick a maximizing projector `P`; the
triangle inequality avoids choosing one). Writing the difference of the two mixed operators as
```
∑ᵢ pᵢρᵢ − ∑ᵢ qᵢσᵢ = ∑ᵢ pᵢ(ρᵢ − σᵢ) + ∑ᵢ (pᵢ − qᵢ)σᵢ,
```
subadditivity of the trace norm over finite sums (`ContinuousLinearMap.traceNorm_sum_le`) and
its absolute homogeneity (`traceNorm_smul`) bound the two pieces by
`∑ᵢ pᵢ ‖ρᵢ − σᵢ‖₁` and `∑ᵢ |pᵢ − qᵢ| · ‖σᵢ‖₁`. Since each `σᵢ` is a density operator its trace
norm is `1` (`State.op_traceNorm_eq_one`), and `pᵢ ≥ 0`, so halving (`D = ½‖·‖₁`) turns these
into `∑ᵢ pᵢ D(ρᵢ, σᵢ)` and `D(p, q) = ½∑ᵢ|pᵢ − qᵢ|`. Only `pᵢ ≥ 0` and normalization of the
`σᵢ` are used for the inequality itself; the full probability-distribution hypotheses enter
through `State.mix`, which requires them to build the mixed states.

## Main statements

* `State.traceDistance_mix_le` — **Theorem 9.3, `(9.46)`**: the strong-convexity bound.
* `State.traceDistance_mix_jointly_convex` — **joint convexity, `(9.50)`**: the special case
  `q = p`, `D(∑ᵢ pᵢ ρᵢ, ∑ᵢ pᵢ σᵢ) ≤ ∑ᵢ pᵢ D(ρᵢ, σᵢ)`, obtained by `classicalTraceDist_self`.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information*
(10th anniv. ed.). Cambridge University Press. Theorem 9.3, §9.2.1.

N&C Theorem 9.3, p. 407.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Theorem 9.3 (Strong convexity of the trace distance, `(9.46)`).** For
probability distributions `p, q : ι → ℝ` over a finite index set and families of states
`ρ, σ : ι → State S`, the trace distance between the mixtures is bounded by the classical
distance of the weights plus the `p`-average of the componentwise distances:
`D(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ) ≤ D(p, q) + ∑ᵢ pᵢ D(ρᵢ, σᵢ)`.

The mixtures are `State.mix p hp hpsum ρ` and `State.mix q hq hqsum σ`. Proof: the trace-norm
triangle inequality (`ContinuousLinearMap.traceNorm_sum_le`, `traceNorm_add_le`) applied to the
splitting `∑ᵢ pᵢρᵢ − ∑ᵢ qᵢσᵢ = ∑ᵢ pᵢ(ρᵢ − σᵢ) + ∑ᵢ (pᵢ − qᵢ)σᵢ`, using `‖σᵢ‖₁ = 1`
(`State.op_traceNorm_eq_one`) and `pᵢ ≥ 0`. -/
theorem State.traceDistance_mix_le {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (ρ σ : ι → State S) :
    (State.mix p hp hpsum ρ).traceDistance (State.mix q hq hqsum σ)
      ≤ Concrete.classicalTraceDist p q + ∑ i, p i * (ρ i).traceDistance (σ i) := by
  -- Split the difference of the two mixed density operators into a component part and a
  -- weight part: `∑ᵢ pᵢρᵢ − ∑ᵢ qᵢσᵢ = ∑ᵢ pᵢ(ρᵢ − σᵢ) + ∑ᵢ (pᵢ − qᵢ)σᵢ`.
  have hA : (∑ i, (p i : ℂ) • (ρ i).op) - (∑ i, (q i : ℂ) • (σ i).op)
      = (∑ i, (p i : ℂ) • ((ρ i).op - (σ i).op))
        + (∑ i, ((p i : ℂ) - (q i : ℂ)) • (σ i).op) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub, sub_smul]; module
  -- Component part: `‖∑ᵢ pᵢ(ρᵢ − σᵢ)‖₁ ≤ ∑ᵢ pᵢ ‖ρᵢ − σᵢ‖₁` (subadditivity + `pᵢ ≥ 0`).
  have hX : (∑ i, (p i : ℂ) • ((ρ i).op - (σ i).op)).traceNorm
      ≤ ∑ i, p i * ((ρ i).op - (σ i).op).traceNorm := by
    refine (ContinuousLinearMap.traceNorm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.traceNorm_smul, Complex.norm_real, Real.norm_of_nonneg (hp i)]
  -- Weight part: `‖∑ᵢ (pᵢ − qᵢ)σᵢ‖₁ ≤ ∑ᵢ |pᵢ − qᵢ|` (subadditivity + `‖σᵢ‖₁ = 1`).
  have hY : (∑ i, ((p i : ℂ) - (q i : ℂ)) • (σ i).op).traceNorm ≤ ∑ i, |p i - q i| := by
    refine (ContinuousLinearMap.traceNorm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.traceNorm_smul, State.op_traceNorm_eq_one, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  -- Convert the `p`-average of trace distances to a trace-norm sum divided by two.
  have hD : ∑ i, p i * (ρ i).traceDistance (σ i)
      = (∑ i, p i * ((ρ i).op - (σ i).op).traceNorm) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [State.traceDistance_eq]; ring
  have hC : Concrete.classicalTraceDist p q = (∑ i, |p i - q i|) / 2 := rfl
  rw [State.traceDistance_eq, State.mix_op, State.mix_op, hA, hC, hD]
  have hXY := (ContinuousLinearMap.traceNorm_add_le
    (∑ i, (p i : ℂ) • ((ρ i).op - (σ i).op)) (∑ i, ((p i : ℂ) - (q i : ℂ)) • (σ i).op)).trans
    (add_le_add hX hY)
  linarith [hXY]

/-- **Joint convexity of the trace distance** (Nielsen & Chuang `(9.50)`), the special case of
strong convexity with equal weight distributions `q = p`:
`D(∑ᵢ pᵢ ρᵢ, ∑ᵢ pᵢ σᵢ) ≤ ∑ᵢ pᵢ D(ρᵢ, σᵢ)`.

Immediate from `State.traceDistance_mix_le` at `q = p`, since the classical trace distance of a
distribution from itself vanishes (`classicalTraceDist_self`). -/
theorem State.traceDistance_mix_jointly_convex {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) (ρ σ : ι → State S) :
    (State.mix p hp hpsum ρ).traceDistance (State.mix p hp hpsum σ)
      ≤ ∑ i, p i * (ρ i).traceDistance (σ i) := by
  have h := State.traceDistance_mix_le p p hp hpsum hp hpsum ρ σ
  rwa [Concrete.classicalTraceDist_self, zero_add] at h

end AxQM
