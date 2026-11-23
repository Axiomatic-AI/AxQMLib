/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.API.Mixture
import Mathlib.Analysis.Convex.Deriv
import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.EntropyDeriv
import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropyContinuous

/-!
# AxQM — the von Neumann entropy along a mixing line, and the second-derivative
concavity criterion (Nielsen & Chuang Exercise 11.22, Part 1)

Nielsen & Chuang **Exercise 11.22** ("Alternate proof of concavity", §11.3.5, p. 518) asks, for two
states `ρ, σ`, to define

`f(p) ≡ S(p ρ + (1 − p) σ)`,

to **argue that to show concavity it is sufficient to prove that `f''(p) ≤ 0`**, and then to prove
`f''(p) ≤ 0` (first for invertible `ρ, σ`, then in general). This file formalises the **sufficiency
reduction** — the first task — as a self-contained, complete development. Compare
`AxQM/Postulates/API/EntropyConcavity.lean`, which proves concavity of the entropy by the
relative-entropy route.

* the entropy-along-a-mixing-line function `State.entropyMixLine ρ σ`, with `f(0) = S(σ)`,
  `f(1) = S(ρ)`, and, on `[0,1]`, `f(p) = S(p ρ + (1 − p) σ)` (the entropy of the binary mixture
  `State.mixPair`);
* the reduction `State.vonNeumannEntropy_concave_of_entropyMixLine_concaveOn`: if `f` is concave on
  `[0,1]`, then the two-point concavity inequality `p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`
  (Nielsen & Chuang eq. (11.79) for two components) holds — obtained by reading concavity of `f` at
  the endpoints `1, 0`;
* the calculus bridge `State.entropyMixLine_concaveOn_of_deriv2_nonpos`: if `f''(p) ≤ 0` on the
  interior of `[0,1]` (with the usual continuity/differentiability, all packaged by Mathlib's
  `concaveOn_of_deriv2_nonpos`), then `f` is concave on `[0,1]`;
* their composite `State.vonNeumannEntropy_concave_of_deriv2_nonpos`, which is exactly N&C's
  assertion "**to show concavity it is sufficient to prove `f''(p) ≤ 0`**".

Part 2 below proves `f''(p) ≤ 0`, and hence the concavity of `f`, for invertible `ρ, σ`. The general
case is not proved in this file.

## Main definitions

* `AxQM.State.entropyMixLine` — the function `f(p) = S(p ρ + (1 − p) σ)`.

## Main results

* `AxQM.State.vonNeumannEntropy_concave_of_entropyMixLine_concaveOn` — concavity of `f` on
  `[0,1]` gives the two-point concavity inequality (11.79).
* `AxQM.State.entropyMixLine_concaveOn_of_deriv2_nonpos` — `f'' ≤ 0` gives concavity of
  `f`.
* `AxQM.State.vonNeumannEntropy_concave_of_deriv2_nonpos` — the sufficiency reduction:
  `f'' ≤ 0` (with smoothness) gives the two-point concavity inequality.
-/

namespace AxQM

variable {S : QSystem}

/-- The **von Neumann entropy along the mixing line** through two states `ρ, σ`:
`f(p) = S(p ρ + (1 − p) σ)` (Nielsen & Chuang Exercise 11.22). Defined as the entropy
of the operator `(p : ℂ) • ρ.op + (1 − p : ℂ) • σ.op` for every real `p`; on the physical interval
`p ∈ [0,1]` this operator is the density operator of the binary mixture `State.mixPair` (see
`State.entropyMixLine_eq_mixPair`), so `f` there is the entropy of an honest state. Extending `f` to
all of `ℝ` (where the operator need not be a density operator, and the entropy is whatever
`ContinuousLinearMap.vonNeumannEntropy` returns) lets `f` be treated as a plain function `ℝ → ℝ`, as
Mathlib's real-variable convexity/derivative API requires. -/
noncomputable def State.entropyMixLine (ρ σ : State S) (p : ℝ) : ℝ :=
  ((p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op).vonNeumannEntropy

/-- On `[0,1]` the mixing-line entropy is the entropy of the honest binary mixture: for `0 ≤ p ≤ 1`,
`f(p) = S(p ρ + (1 − p) σ) = S(State.mixPair p ρ σ)`. Both sides are the entropy of the same
operator (`State.mixPair_op`). -/
theorem State.entropyMixLine_eq_mixPair {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : State S) :
    ρ.entropyMixLine σ p = (State.mixPair hp0 hp1 ρ σ).vonNeumannEntropy := by
  rw [State.vonNeumannEntropy_def, State.mixPair_op, State.entropyMixLine]

/-- Left endpoint: `f(0) = S(σ)`. At `p = 0` the operator is `0 • ρ.op + 1 • σ.op = σ.op`. -/
@[simp] theorem State.entropyMixLine_zero (ρ σ : State S) :
    ρ.entropyMixLine σ 0 = σ.vonNeumannEntropy := by
  simp only [State.entropyMixLine, Complex.ofReal_zero, zero_smul, zero_add, sub_zero,
    Complex.ofReal_one, one_smul, State.vonNeumannEntropy_def]

/-- Right endpoint: `f(1) = S(ρ)`. At `p = 1` the operator is `1 • ρ.op + 0 • σ.op = ρ.op`. -/
@[simp] theorem State.entropyMixLine_one (ρ σ : State S) :
    ρ.entropyMixLine σ 1 = ρ.vonNeumannEntropy := by
  simp only [State.entropyMixLine, Complex.ofReal_one, one_smul, sub_self, Complex.ofReal_zero,
    zero_smul, add_zero, State.vonNeumannEntropy_def]

/-- **The sufficiency reduction, concavity form.** If the mixing-line entropy
`f(p) = S(p ρ + (1−p)σ)` is **concave on `[0,1]`**, then the two-point concavity inequality
(Nielsen & Chuang eq. (11.79) for
two components) holds: for `0 ≤ p ≤ 1`,

`p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`.

This is the second half of N&C's Part-1 argument: concavity of `f` on `[0,1]`, evaluated at the
endpoints `x = 1` (giving `S(ρ)`) and `y = 0` (giving `S(σ)`) with weights `p, 1 − p`, is exactly
the concavity of the entropy. -/
theorem State.vonNeumannEntropy_concave_of_entropyMixLine_concaveOn {ρ σ : State S}
    (h : ConcaveOn ℝ (Set.Icc 0 1) (ρ.entropyMixLine σ)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy
      ≤ (State.mixPair hp0 hp1 ρ σ).vonNeumannEntropy := by
  simpa [State.entropyMixLine_eq_mixPair hp0 hp1] using
    h.2 (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
      hp0 (by linarith : (0 : ℝ) ≤ 1 - p) (by ring : p + (1 - p) = 1)

/-- **The sufficiency reduction, calculus bridge.** If the mixing-line entropy `f` has non-positive
second derivative on the interior of `[0,1]` (with the continuity and twice-differentiability that
Mathlib's `concaveOn_of_deriv2_nonpos` requires), then `f` is concave on `[0,1]`. This is the
"`f''(p) ≤ 0` ⟹ concave" step that N&C invokes; the hypotheses are exactly the analytic input
supplied for invertible states by Part 2 below (the derivative-of-entropy computation). -/
theorem State.entropyMixLine_concaveOn_of_deriv2_nonpos {ρ σ : State S}
    (hcont : ContinuousOn (ρ.entropyMixLine σ) (Set.Icc 0 1))
    (hdiff : DifferentiableOn ℝ (ρ.entropyMixLine σ) (interior (Set.Icc 0 1)))
    (hdiff2 : DifferentiableOn ℝ (deriv (ρ.entropyMixLine σ)) (interior (Set.Icc 0 1)))
    (hf2 : ∀ p ∈ interior (Set.Icc (0 : ℝ) 1), (deriv^[2] (ρ.entropyMixLine σ)) p ≤ 0) :
    ConcaveOn ℝ (Set.Icc 0 1) (ρ.entropyMixLine σ) :=
  concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hcont hdiff hdiff2 hf2

/-- **N&C Exercise 11.22, Part 1 — "to show concavity it is sufficient to prove `f''(p) ≤ 0`".**
Combining the two reduction steps: if the mixing-line entropy `f(p) = S(p ρ + (1 − p) σ)` has
non-positive second derivative on `(0,1)` (with the packaged smoothness), then the two-point
concavity inequality holds: for `0 ≤ p ≤ 1`,

`p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`.

The hypothesis `f''(p) ≤ 0` is proved for invertible states in Part 2 below. -/
theorem State.vonNeumannEntropy_concave_of_deriv2_nonpos {ρ σ : State S}
    (hcont : ContinuousOn (ρ.entropyMixLine σ) (Set.Icc 0 1))
    (hdiff : DifferentiableOn ℝ (ρ.entropyMixLine σ) (interior (Set.Icc 0 1)))
    (hdiff2 : DifferentiableOn ℝ (deriv (ρ.entropyMixLine σ)) (interior (Set.Icc 0 1)))
    (hf2 : ∀ p ∈ interior (Set.Icc (0 : ℝ) 1), (deriv^[2] (ρ.entropyMixLine σ)) p ≤ 0)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy
      ≤ (State.mixPair hp0 hp1 ρ σ).vonNeumannEntropy :=
  State.vonNeumannEntropy_concave_of_entropyMixLine_concaveOn
    (State.entropyMixLine_concaveOn_of_deriv2_nonpos hcont hdiff hdiff2 hf2) hp0 hp1

/-! ## Part 2: `f''(p) ≤ 0` and the concavity it yields, for invertible `ρ, σ`

The remaining task of Exercise 11.22 — prove `f''(p) ≤ 0` — is now carried out for the case where
`ρ` and `σ` are **invertible** (equivalently, strictly positive). The analytic input is the
operator-level statement
`deriv2_re_trace_cfc_negMulLog_add_smul_nonpos` (`ToMathlib`,
`.../ExpLog/EntropyDeriv.lean`): for a self-adjoint direction `b` and a base point where
`a + p • b` is strictly positive, the entropy `p ↦ re tr(cfc negMulLog (a + p • b))` has
non-positive second derivative — the Daleckii–Krein / resolvent-integral computation
`f''(p) = -∫₀^∞ tr(Δ (ω_p+s)⁻¹ Δ (ω_p+s)⁻¹) ds ≤ 0` with `Δ = ρ − σ`, `ω_p = p ρ + (1−p) σ`.

The bridge to the mixing line is that `f(p) = S(p ρ + (1−p) σ)` is exactly this operator entropy
along the affine line `p ↦ σ.op + p • (ρ.op − σ.op)` (`entropyMixLine_eq_re_trace_cfc_negMulLog`),
whose base point is strictly positive on all of `[0,1]` when `ρ, σ` are invertible
(`isStrictlyPositive_op_add_smul`, a convex-combination-of-strictly-positive fact). Feeding the
resulting `f'' ≤ 0`, together with the differentiability the same operator lemmas provide, into the
Part-1 reduction gives concavity of `f`, hence the two-point concavity inequality (11.79) — for
invertible `ρ, σ`. -/

/-- The density operator of a state is self-adjoint (a density operator is symmetric,
`ContinuousLinearMap.IsDensityOp.isSymmetric`, hence self-adjoint on the finite-dimensional
space). The self-adjointness the affine-line derivative lemmas require of `ρ.op` and the direction
`ρ.op − σ.op`. -/
theorem State.isSelfAdjoint_op (ρ : State S) : IsSelfAdjoint ρ.op :=
  ρ.isDensity.isSymmetric.isSelfAdjoint

/-- The mixing-line entropy as the operator entropy along an affine line: for every `p`,
`f(p) = S(p ρ + (1−p) σ) = re tr(cfc negMulLog (σ.op + p • (ρ.op − σ.op)))`. The operator
`(p : ℂ) • ρ.op + (1 − p : ℂ) • σ.op` defining `f` equals the affine-line operator
`σ.op + p • (ρ.op − σ.op)` (a real-scalar reparametrisation), which is self-adjoint, so
`ContinuousLinearMap.vonNeumannEntropy_eq_re_trace_cfc_negMulLog` applies. This is the shape
consumed by the operator-level derivative lemmas of `ExpLog/EntropyDeriv.lean`. -/
theorem State.entropyMixLine_eq_re_trace_cfc_negMulLog (ρ σ : State S) (p : ℝ) :
    ρ.entropyMixLine σ p
      = RCLike.re ((LinearMap.trace ℂ S.space)
        ↑(cfc Real.negMulLog (σ.op + p • (ρ.op - σ.op)))) := by
  have hb : IsSelfAdjoint (ρ.op - σ.op) := ρ.isSelfAdjoint_op.sub σ.isSelfAdjoint_op
  have hsa : IsSelfAdjoint (σ.op + p • (ρ.op - σ.op)) :=
    σ.isSelfAdjoint_op.add ((IsSelfAdjoint.all p).smul hb)
  rw [State.entropyMixLine,
    show ((p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op) = σ.op + p • (ρ.op - σ.op) from by
      simp only [Complex.coe_smul]; module,
    ContinuousLinearMap.vonNeumannEntropy_eq_re_trace_cfc_negMulLog hsa]

/-- For invertible (strictly positive) states `ρ, σ`, the affine-line operator
`σ.op + p • (ρ.op − σ.op) = p ρ.op + (1 − p) σ.op` is strictly positive for every `p ∈ [0,1]`: it is
a convex combination of the strictly positive operators `ρ.op, σ.op`, and the set of strictly
positive elements is convex (`convex_isStrictlyPositive`). -/
theorem State.isStrictlyPositive_op_add_smul {ρ σ : State S} {p : ℝ}
    (hρ : IsStrictlyPositive ρ.op) (hσ : IsStrictlyPositive σ.op) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsStrictlyPositive (σ.op + p • (ρ.op - σ.op)) := by
  rw [show σ.op + p • (ρ.op - σ.op) = p • ρ.op + (1 - p) • σ.op from by module]
  exact convex_isStrictlyPositive hρ hσ hp0 (by linarith) (by ring)

/-- **Exercise 11.22, Part 2 (invertible case): `f''(p) ≤ 0`.** For invertible states `ρ, σ`, the
mixing-line entropy `f(p) = S(p ρ + (1 − p) σ)` has non-positive second derivative on the open
interval `(0,1)`. This is the operator-level second-derivative bound
`deriv2_re_trace_cfc_negMulLog_add_smul_nonpos` transported along the affine-line identification
`entropyMixLine_eq_re_trace_cfc_negMulLog`, whose base point is strictly positive on `(0,1)` by
`isStrictlyPositive_op_add_smul`. -/
theorem State.entropyMixLine_deriv2_nonpos_of_isStrictlyPositive {ρ σ : State S}
    (hρ : IsStrictlyPositive ρ.op) (hσ : IsStrictlyPositive σ.op)
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (deriv^[2] (ρ.entropyMixLine σ)) p ≤ 0 := by
  have : Nontrivial S.space := ρ.nontrivial_space
  have hb : IsSelfAdjoint (ρ.op - σ.op) := ρ.isSelfAdjoint_op.sub σ.isSelfAdjoint_op
  have hstrict : IsStrictlyPositive (σ.op + p • (ρ.op - σ.op)) :=
    State.isStrictlyPositive_op_add_smul hρ hσ hp.1.le hp.2.le
  rw [funext (ρ.entropyMixLine_eq_re_trace_cfc_negMulLog σ)]
  exact deriv2_re_trace_cfc_negMulLog_add_smul_nonpos hb hstrict

/-- For invertible states `ρ, σ`, the mixing-line entropy `f` is concave on `[0,1]`. All the
smoothness inputs of the Part-1 reduction `entropyMixLine_concaveOn_of_deriv2_nonpos` are supplied
by the operator-level derivative lemmas of `ExpLog/EntropyDeriv.lean`: on `[0,1]` the base point
`σ.op + p • (ρ.op − σ.op)` is strictly positive (`isStrictlyPositive_op_add_smul`), so
`hasDerivAt_re_trace_cfc_negMulLog_add_smul` gives `f` a derivative at every such point (hence
continuity on `[0,1]` and differentiability on `(0,1)`); the first-derivative function is in turn
differentiable via `hasDerivAt_neg_re_trace_mul_cfc_log_add_smul`, and it agrees with `deriv f` on a
neighbourhood of each interior point (`eventually_isStrictlyPositive_add_smul`), giving
differentiability of `deriv f` on `(0,1)`; and `f'' ≤ 0` is
`entropyMixLine_deriv2_nonpos_of_isStrictlyPositive`. -/
theorem State.entropyMixLine_concaveOn_of_isStrictlyPositive {ρ σ : State S}
    (hρ : IsStrictlyPositive ρ.op) (hσ : IsStrictlyPositive σ.op) :
    ConcaveOn ℝ (Set.Icc 0 1) (ρ.entropyMixLine σ) := by
  have hnt : Nontrivial S.space := ρ.nontrivial_space
  have hb : IsSelfAdjoint (ρ.op - σ.op) := ρ.isSelfAdjoint_op.sub σ.isSelfAdjoint_op
  have hSP : ∀ q ∈ Set.Icc (0 : ℝ) 1, IsStrictlyPositive (σ.op + q • (ρ.op - σ.op)) :=
    fun q hq => State.isStrictlyPositive_op_add_smul hρ hσ hq.1 hq.2
  have hgeq : ρ.entropyMixLine σ = fun q =>
      RCLike.re ((LinearMap.trace ℂ S.space) ↑(cfc Real.negMulLog (σ.op + q • (ρ.op - σ.op)))) :=
    funext (ρ.entropyMixLine_eq_re_trace_cfc_negMulLog σ)
  refine State.entropyMixLine_concaveOn_of_deriv2_nonpos ?_ ?_ ?_ ?_
  · rw [hgeq]
    exact fun q hq =>
      (hasDerivAt_re_trace_cfc_negMulLog_add_smul hb (hSP q hq)).continuousAt.continuousWithinAt
  · rw [hgeq, interior_Icc]
    exact fun q hq => (hasDerivAt_re_trace_cfc_negMulLog_add_smul hb
      (hSP q (Set.Ioo_subset_Icc_self hq))).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro q hq
    have hqI : q ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hq
    have hderivEq : deriv (ρ.entropyMixLine σ) =ᶠ[nhds q] fun r =>
        -RCLike.re ((LinearMap.trace ℂ S.space)
            ↑((ρ.op - σ.op) * cfc Real.log (σ.op + r • (ρ.op - σ.op))))
          - RCLike.re ((LinearMap.trace ℂ S.space) ↑(ρ.op - σ.op)) := by
      filter_upwards [eventually_isStrictlyPositive_add_smul (hSP q hqI) hb] with r hr
      rw [hgeq]
      exact (hasDerivAt_re_trace_cfc_negMulLog_add_smul hb hr).deriv
    exact DifferentiableAt.differentiableWithinAt ((hderivEq.differentiableAt_iff).mpr
      (hasDerivAt_neg_re_trace_mul_cfc_log_add_smul hb (hSP q hqI)).differentiableAt)
  · rw [interior_Icc]
    exact fun q hq => State.entropyMixLine_deriv2_nonpos_of_isStrictlyPositive hρ hσ hq

/-- **Exercise 11.22, Part 2 (invertible case), concavity form.** For invertible states `ρ, σ` the
two-point concavity inequality (Nielsen & Chuang eq. (11.79)) holds: for `0 ≤ p ≤ 1`,

`p S(ρ) + (1 − p) S(σ) ≤ S(p ρ + (1 − p) σ)`.

This is the alternate (second-derivative) proof of concavity of the von Neumann entropy carried out
for invertible states: `f'' ≤ 0` (`entropyMixLine_concaveOn_of_isStrictlyPositive`) fed through the
Part-1 sufficiency reduction. -/
theorem State.vonNeumannEntropy_concave_of_isStrictlyPositive {ρ σ : State S}
    (hρ : IsStrictlyPositive ρ.op) (hσ : IsStrictlyPositive σ.op)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy
      ≤ (State.mixPair hp0 hp1 ρ σ).vonNeumannEntropy :=
  State.vonNeumannEntropy_concave_of_entropyMixLine_concaveOn
    (State.entropyMixLine_concaveOn_of_isStrictlyPositive hρ hσ) hp0 hp1

end AxQM
