/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyMixLine
import AxQM.Postulates.API.MaximallyMixed

/-!
# N&C Exercise 11.22 — alternate (second-derivative) proof of concavity of the entropy

Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Exercise 11.22, p. 518.

Alternate proof of concavity: show f(p)=S(p rho+(1-p)sigma) has f''(p)<=0.

The exercise concerns the two-point concavity inequality (Nielsen &
Chuang eq. (11.79) for two components)

`p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`   for `0 ≤ p ≤ 1`,

for **all** states `ρ, σ` — `AxQM.State.vonNeumannEntropy_concave` below — obtained by
the alternate second-derivative route the exercise prescribes, extended from the invertible case
to the general case by regularisation. Compare the concavity results of Exercises 11.20, 11.21
and 11.25.

## The supporting development

The exercise's three tasks are formalised as a single development, in
`AxQM/Postulates/API/EntropyMixLine.lean`:

* **Part 1 — "to show concavity it is sufficient to prove `f''(p) ≤ 0`".** The mixing-line
  entropy `State.entropyMixLine ρ σ p = S(p ρ + (1 − p) σ)`, with endpoints `f 0 = S(σ)`,
  `f 1 = S(ρ)`; the reduction `State.vonNeumannEntropy_concave_of_entropyMixLine_concaveOn`
  (concavity of `f` on `[0,1]` ⟹ the two-point inequality, by reading `ConcaveOn` at the
  endpoints `1, 0`); and the calculus bridge `State.entropyMixLine_concaveOn_of_deriv2_nonpos`
  (`f'' ≤ 0` ⟹ `ConcaveOn`, via Mathlib's `concaveOn_of_deriv2_nonpos`). Their composite is
  `State.vonNeumannEntropy_concave_of_deriv2_nonpos`.
* **Part 2, invertible case — `f''(p) ≤ 0`.**
  `State.entropyMixLine_deriv2_nonpos_of_isStrictlyPositive` (`f'' ≤ 0` on `(0,1)` for invertible
  `ρ, σ`), the operator-level Daleckii–Krein / resolvent-integral computation
  `f''(p) = −∫₀^∞ tr(Δ (ω_p+s)⁻¹ Δ (ω_p+s)⁻¹) ds ≤ 0`
  (`deriv2_re_trace_cfc_negMulLog_add_smul_nonpos`, `ToMathlib`), transported along the
  affine-line identification `State.entropyMixLine_eq_re_trace_cfc_negMulLog`; whence the
  two-point concavity for invertible states,
  `State.vonNeumannEntropy_concave_of_isStrictlyPositive`.

## Part 2, general case — "and then for the case where they are not [invertible]"

The theorem below removes the invertibility hypothesis from
`State.vonNeumannEntropy_concave_of_isStrictlyPositive` by the standard regularisation/limit
argument. For `t ∈ (0,1]` regularise each state towards the (strictly positive) maximally mixed
state `τ = I/d`,

`ρ_t := (1 − t) ρ + t τ = State.mixPair (1−t) ρ τ`,   `σ_t` likewise;

`ρ_t.op = (1−t) • ρ.op + t • τ.op` is strictly positive (a nonnegative summand plus the strictly
positive `t • τ.op`), so the invertible concavity applies at every `t ∈ (0,1]`. As `t → 0⁺` the
von Neumann entropy is continuous on density operators
(`ContinuousLinearMap.tendsto_vonNeumannEntropy_regularise`, built on the continuity keystone
`ContinuousLinearMap.IsDensityOp.continuousOn_vonNeumannEntropy`), and — since
`State.mixPair p ρ_t σ_t` is itself the regularisation
`(1−t) • (State.mixPair p ρ σ).op + t • τ.op` of the unperturbed mixture — all three entropies
converge (`S(ρ_t) → S(ρ)`, `S(σ_t) → S(σ)`, `S(mixPair p ρ_t σ_t) → S(mixPair p ρ σ)`), so the
inequality, being closed, passes to the limit (`le_of_tendsto_of_tendsto` over `𝓝[Set.Ioc 0 1] 0`).

## Main result

* `AxQM.State.vonNeumannEntropy_concave` — the two-point concavity inequality (11.79) for
  arbitrary states, the alternate-proof statement of Exercise 11.22.
-/

open scoped ComplexOrder

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang Exercise 11.22 — concavity of the von Neumann entropy, for all states.** The
two-point concavity inequality (Nielsen & Chuang eq. (11.79) for two components): for arbitrary
states `ρ, σ` and `0 ≤ p ≤ 1`,

`p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`.

This is the culmination of the exercise's alternate (second-derivative) proof: the invertible case
`State.vonNeumannEntropy_concave_of_isStrictlyPositive` (proved from `f''(p) ≤ 0`) is extended to
**non-invertible** `ρ, σ` — N&C's "and then for the case where they are not" — by regularising each
state towards the maximally mixed state `τ = I/d`, applying the invertible inequality along `(0,1]`,
and passing to the `t → 0⁺` limit using continuity of the entropy on density operators (see the
module docstring). -/
theorem State.vonNeumannEntropy_concave {ρ σ : State S} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy
      ≤ (State.mixPair hp0 hp1 ρ σ).vonNeumannEntropy := by
  have : Nontrivial S.space := ρ.nontrivial_space
  set τ := maximallyMixedState S with hτdef
  have hτd : τ.op.IsDensityOp := τ.isDensity
  have hτs : IsStrictlyPositive τ.op := maximallyMixedState_isStrictlyPositive S
  have : (nhdsWithin (0 : ℝ) (Set.Ioc (0 : ℝ) 1)).NeBot :=
    left_nhdsWithin_Ioc_neBot (by norm_num)
  -- Continuity of the entropy along the three regularisations `ω_t = (1-t) ω + t τ` as `t → 0⁺`.
  have tρ := ContinuousLinearMap.tendsto_vonNeumannEntropy_regularise ρ.op τ.op ρ.isDensity hτd
  have tσ := ContinuousLinearMap.tendsto_vonNeumannEntropy_regularise σ.op τ.op σ.isDensity hτd
  have tμ := ContinuousLinearMap.tendsto_vonNeumannEntropy_regularise
    (State.mixPair hp0 hp1 ρ σ).op τ.op (State.mixPair hp0 hp1 ρ σ).isDensity hτd
  rw [State.vonNeumannEntropy_def ρ, State.vonNeumannEntropy_def σ,
    State.vonNeumannEntropy_def (State.mixPair hp0 hp1 ρ σ)]
  refine le_of_tendsto_of_tendsto ((tρ.const_mul p).add (tσ.const_mul (1 - p))) tμ ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  -- `ht : t ∈ Set.Ioc 0 1`, i.e. `0 < t ≤ 1`.
  have h1t0 : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
  have h1t1 : (1 : ℝ) - t ≤ 1 := by linarith [ht.1]
  have htpos : (0 : ℝ) < t := ht.1
  have hcoe : ((1 - (1 - t) : ℝ) : ℂ) = ((t : ℝ) : ℂ) := by push_cast; ring
  set ρt := State.mixPair h1t0 h1t1 ρ τ with hρtdef
  set σt := State.mixPair h1t0 h1t1 σ τ with hσtdef
  -- The regularised states are strictly positive: a nonnegative summand plus `t • τ.op` — the
  -- reusable `State.isStrictlyPositive_mixPair_op` (right operand `τ` faithful, weight `t > 0`).
  have hρts : IsStrictlyPositive ρt.op :=
    State.isStrictlyPositive_mixPair_op h1t0 h1t1 (by linarith [htpos]) hτs
  have hσts : IsStrictlyPositive σt.op :=
    State.isStrictlyPositive_mixPair_op h1t0 h1t1 (by linarith [htpos]) hτs
  -- The invertible-case concavity, applied at the regularised states.
  have key := State.vonNeumannEntropy_concave_of_isStrictlyPositive hρts hσts hp0 hp1
  -- Identify the three regularised entropies with the operator-regularisation forms of `tρ/tσ/tμ`.
  have hEρ : ρt.vonNeumannEntropy
      = (((1 - t : ℝ) : ℂ) • ρ.op + ((t : ℝ) : ℂ) • τ.op).vonNeumannEntropy := by
    rw [hρtdef, State.vonNeumannEntropy_def, State.mixPair_op, hcoe]
  have hEσ : σt.vonNeumannEntropy
      = (((1 - t : ℝ) : ℂ) • σ.op + ((t : ℝ) : ℂ) • τ.op).vonNeumannEntropy := by
    rw [hσtdef, State.vonNeumannEntropy_def, State.mixPair_op, hcoe]
  have hopeq : (State.mixPair hp0 hp1 ρt σt).op
      = ((1 - t : ℝ) : ℂ) • (State.mixPair hp0 hp1 ρ σ).op + ((t : ℝ) : ℂ) • τ.op := by
    rw [hρtdef, hσtdef]
    simp only [State.mixPair_op]
    push_cast
    module
  rw [hEρ, hEσ, State.vonNeumannEntropy_def (State.mixPair hp0 hp1 ρt σt), hopeq] at key
  exact key

end AxQM
