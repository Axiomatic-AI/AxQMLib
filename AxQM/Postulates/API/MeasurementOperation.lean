/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement

/-!
# AxQM — measurement as a quantum operation (N&C Exercise 8.2)

**Nielsen–Chuang Exercise 8.2**: a general measurement
(Postulate 3, `Measurement`) acts on density operators as the quantum operation

  `Eₘ(ρ) = Mₘ ρ Mₘ†`   (Nielsen–Chuang Eq. (8.5)),

and the two outputs of the measurement postulate are read off from this single operator:

* the **outcome probability** is its trace, `p(m) = tr(Eₘ(ρ))`;
* the **post-measurement state** is its normalization, `Eₘ(ρ)/tr(Eₘ(ρ))`.

The exercise is the statement that the Born probability and the post-measurement state —
`Measurement.bornProb` (Postulate 3 / the Born rule) and `Measurement.postMeasurement`
(Postulate 4 / collapse) — coincide with the operator-sum quantities `tr(Eₘ(ρ))` and
`Eₘ(ρ)/tr(Eₘ(ρ))`.

## Contents

* `Measurement.opElement` — the quantum operation element `Eₘ(ρ) = Mₘ ρ Mₘ†` of outcome `i`
  (a thin `AxQM`-level name for `ContinuousLinearMap.postOp m.op ρ.op i`), with
  `opElement_isPositive`: `Eₘ(ρ)` is a positive operator (a genuine subnormalized state).
* `Measurement.bornProb_eq_trace_opElement` — **Exercise 8.2, probability:** `p(m) = tr(Eₘ(ρ))`,
  as the equality `(p(m) : ℂ) = tr(Eₘ(ρ))` (the trace is real and equals the Born probability).
* `Measurement.postMeasurement_op_eq_opElement_div` — **Exercise 8.2, state update:** the
  post-measurement state is `Eₘ(ρ)/tr(Eₘ(ρ))` (N&C Eq. (8.5)), and
  `postMeasurement_op_eq_bornProb_smul_opElement` gives its physical reading `Eₘ(ρ)/p(m)`.

The statements of Exercise 8.2 are in `AxQM/NC/Ch8/Exercise8_2.lean`, which refers to these
declarations.

## Design notes

* **Fidelity to N&C.** N&C introduces `Eₘ(ρ) ≡ Mₘ ρ Mₘ†` as a named object and asks for
  two identities about it; the formalisation names `opElement` as its own `def` and states each
  identity as its own theorem, about `bornProb`/`postMeasurement`, for an
  arbitrary measurement `m`, state `ρ`, and outcome `i` — no dimension is specialized and no extra
  hypothesis is added (`postMeasurement` already carries the standard `p(m) ≠ 0` side condition for
  the collapse to be defined). The probability identity is stated as the *complex* equality
  `(p(m) : ℂ) = tr(Eₘ(ρ))`, which simultaneously records that `tr(Eₘ(ρ))` is real and that it equals
  `p(m)` — strictly stronger than the real-part form `p(m) = re tr(Eₘ(ρ))`. The state identity is
  stated as N&C's literal `Eₘ(ρ)/tr(Eₘ(ρ))` (division by the complex trace), with a corollary in the
  `Eₘ(ρ)/p(m)` form to make the physical normalization explicit.
* **Proof.** Both identities are short bridges over existing lemmas.
  `bornProb_eq_trace_opElement` combines `bornProb_eq_re_trace_postOp` (`p(m) = re tr(Eₘ(ρ))`) with
  `trace_postOp_eq_ofReal_re` (for positive `ρ`, the trace equals its own real part), the positivity
  coming from `State.isPositive_op`. `postMeasurement_op_eq_bornProb_smul_opElement` unfolds
  `postMeasurement.op = postState m.op ρ.op i = (re tr(Eₘ(ρ)))⁻¹ • Eₘ(ρ)` and rewrites the real
  scale factor to `p(m)⁻¹` via the same Born-rule bridge; the literal Eq. (8.5) form follows by
  substituting `tr(Eₘ(ρ)) = p(m)` from the probability identity.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- The **quantum operation element** of outcome `i` for the measurement `m` on state `ρ`:
`Eₘ(ρ) = Mₘ ρ Mₘ†` (Nielsen–Chuang Eq. (8.5)). A `AxQM`-level name for the operator-level
post-measurement operation `ContinuousLinearMap.postOp m.op ρ.op i`. -/
def opElement (m : Measurement ι S) (ρ : State S) (i : ι) : S →L[ℂ] S :=
  ContinuousLinearMap.postOp m.op ρ.op i

@[simp]
theorem opElement_eq_postOp (m : Measurement ι S) (ρ : State S) (i : ι) :
    m.opElement ρ i = ContinuousLinearMap.postOp m.op ρ.op i := rfl

/-- `Eₘ(ρ) = Mₘ ρ Mₘ†` is a positive operator when `ρ` is a state: it is a genuine (subnormalized)
density operator, which is why its normalization `Eₘ(ρ)/tr(Eₘ(ρ))` is again a state. -/
theorem opElement_isPositive (m : Measurement ι S) (ρ : State S) (i : ι) :
    (m.opElement ρ i).IsPositive :=
  ContinuousLinearMap.postOp_isPositive m.op ρ.isPositive_op i

/-- **Nielsen & Chuang, Exercise 8.2 (outcome probability).** The probability of obtaining outcome
`i` is the trace of the quantum operation element: `p(m) = tr(Eₘ(ρ))`. Stated as the complex
equality `(p(m) : ℂ) = tr(Eₘ(ρ))`, which records both that `tr(Eₘ(ρ))` is real and that it equals
the Born probability `bornProb`. Combines the Born-rule bridge `bornProb_eq_re_trace_postOp`
(`p(m) = re tr(Eₘ(ρ))`) with the positivity fact `trace_postOp_eq_ofReal_re` that the trace of the
positive operator `Eₘ(ρ)` equals its own real part. -/
theorem bornProb_eq_trace_opElement (m : Measurement ι S) (ρ : State S) (i : ι) :
    (m.bornProb ρ i : ℂ) = LinearMap.trace ℂ S (m.opElement ρ i : S →ₗ[ℂ] S) := by
  rw [opElement_eq_postOp, ContinuousLinearMap.trace_postOp_eq_ofReal_re m.op ρ.isPositive_op i,
    bornProb_eq_re_trace_postOp]

/-- **Nielsen & Chuang, Exercise 8.2 (state update, physical form).** The post-measurement state is
`Eₘ(ρ)/p(m)`: the quantum operation element normalized by the outcome probability. This is the
physical reading of the collapse rule; `postMeasurement_op_eq_opElement_div` gives N&C's literal
`Eₘ(ρ)/tr(Eₘ(ρ))` form (equal because `tr(Eₘ(ρ)) = p(m)`). Unfolds `postMeasurement.op` to the
normalized conjugation `(re tr(Eₘ(ρ)))⁻¹ • Eₘ(ρ)` and rewrites the real scale factor to `p(m)⁻¹`. -/
theorem postMeasurement_op_eq_bornProb_smul_opElement (m : Measurement ι S) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) :
    (m.postMeasurement ρ i hp).op = ((m.bornProb ρ i : ℂ))⁻¹ • m.opElement ρ i := by
  rw [postMeasurement_op, opElement_eq_postOp, ContinuousLinearMap.postState,
    bornProb_eq_re_trace_postOp]

/-- **Nielsen & Chuang, Exercise 8.2 (state update, Eq. (8.5)).** The state of the system
immediately after obtaining outcome `i` is `Eₘ(ρ)/tr(Eₘ(ρ))`: the quantum operation element
normalized by its trace. This is N&C's Equation (8.5). Immediate from the probability identity
`bornProb_eq_trace_opElement` (`tr(Eₘ(ρ)) = p(m)`) and the physical form
`postMeasurement_op_eq_bornProb_smul_opElement`. -/
theorem postMeasurement_op_eq_opElement_div (m : Measurement ι S) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) :
    (m.postMeasurement ρ i hp).op
      = (LinearMap.trace ℂ S (m.opElement ρ i : S →ₗ[ℂ] S))⁻¹ • m.opElement ρ i := by
  rw [← bornProb_eq_trace_opElement, postMeasurement_op_eq_bornProb_smul_opElement]

end Measurement

end AxQM
