/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TraceDistance
import AxQM.Postulates.API.QuantumChannel

/-!
# Nielsen & Chuang, Theorem 9.2 (Trace-preserving quantum operations are contractive)

Trace-preserving quantum operations are contractive: D(E(rho),E(sigma))<=D(rho,sigma).

No physical process ever increases the trace distance between two quantum states: a channel can only
make states *less* distinguishable. This is the central structural fact of §9.2.1, from which the
data-processing–flavoured corollaries follow (e.g. monotonicity under partial trace, `(9.45)`).

## Statement

A **trace-preserving quantum operation** is a quantum *channel*: `AxQM.IsChannel f` says
the state-map `f : State S → State S` is the restriction of a completely-positive, trace-preserving
linear superoperator `Φ` on operators. The distance is the trace distance
`AxQM.State.traceDistance` (`ρ.traceDistance σ`), `D(ρ, σ) = ½ ‖ρ − σ‖₁`. The result is

* `AxQM.traceDistance_channel_le` — `D(f ρ, f σ) ≤ D(ρ, σ)` for every channel `f` and all
  states `ρ`, `σ`.

## Proof

The mathematical heart is a general operator-theoretic fact, proved as an operator lemma
`ContinuousLinearMap.traceNorm_map_le_of_isPositive_of_trace_eq` (`ToMathlib/`,
`ToMathlib.Analysis.InnerProductSpace.TraceNorm`): **a positivity-preserving, trace-preserving
linear
superoperator does not increase the trace norm of any self-adjoint operator**. Its proof is the
clean Jordan-decomposition argument — for `A = A⁺ − A⁻`,
`‖Φ A‖₁ ≤ ‖Φ A⁺‖₁ + ‖Φ A⁻‖₁ = tr Φ A⁺ + tr Φ A⁻ = tr A⁺ + tr A⁻ = ‖A‖₁`
(triangle inequality; positivity turns each trace norm into a trace; trace preservation; the
trace-norm Jordan split) — which is *stronger* than the projector argument N&C writes out, and needs
only positivity + trace preservation, not full complete positivity.

Here that lemma is instantiated at `Φ` with `A = ρ.op − σ.op` (self-adjoint, since density operators
are). Two ingredients bridge `IsChannel` to the lemma's hypotheses:

* **Positivity on *all* positive operators.** `IsChannel` gives complete positivity, but the lemma
  needs `Φ` to preserve the positivity of the Jordan parts `A⁺, A⁻` — general positive operators,
  not states. This is obtained from the operator-sum representation: a CPTP `Φ` is a quantum
  operation (`SatisfiesOperationAxioms`, trace-*preservation* implying trace-non-increase), hence
  `Φ = krausSumₗ E` for some Kraus family `E`
  (`ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum`), and the operator-sum map
  preserves positivity unconditionally (`ContinuousLinearMap.krausSumₗ_isPositive`).
* **Trace preservation** is carried by `IsChannel` directly.

The proof body unfolds `traceDistance` to the trace norm and discharges the operator work through
the lemma above.

N&C Theorem 9.2, p. 406.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Trace-preserving quantum operations are contractive** (Nielsen & Chuang, Theorem 9.2,
`(9.35)`). A quantum channel `f` never increases the trace distance: `D(f ρ, f σ) ≤ D(ρ, σ)` for all
states `ρ`, `σ`.

The proof reduces, through the defining equation of `traceDistance`, to the operator-level fact that
a positivity-preserving, trace-preserving superoperator contracts the trace norm of the self-adjoint
operator `ρ.op − σ.op`
(`ContinuousLinearMap.traceNorm_map_le_of_isPositive_of_trace_eq`). Complete positivity of the
channel enters only to supply an operator-sum representation, from which positivity of `Φ` on the
(non-state) Jordan parts of `ρ.op − σ.op` follows. -/
theorem traceDistance_channel_le {f : State S → State S} (hf : IsChannel f) (ρ σ : State S) :
    (f ρ).traceDistance (f σ) ≤ ρ.traceDistance σ := by
  obtain ⟨Φ, hΦCP, hΦTP, hfop⟩ := hf
  -- `Φ` has a Kraus (operator-sum) representation, so it preserves positivity of *every* positive
  -- operator — not merely density operators — which is what the contractivity lemma needs.
  obtain ⟨_, _, E, hEeq, -⟩ :=
    (ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum Φ).mp
      ⟨hΦCP, fun τ _ => le_of_eq (by rw [hΦTP τ])⟩
  have hpos : ∀ A : S.space →L[ℂ] S.space, A.IsPositive → (Φ A).IsPositive := fun A hA => by
    rw [hEeq]; exact ContinuousLinearMap.krausSumₗ_isPositive E hA
  -- `ρ.op − σ.op` is self-adjoint, and the channel commutes with the subtraction.
  have hsa : IsSelfAdjoint (ρ.op - σ.op) :=
    ρ.isPositive_op.isSelfAdjoint.sub σ.isPositive_op.isSelfAdjoint
  have hdiff : (f ρ).op - (f σ).op = Φ (ρ.op - σ.op) := by rw [hfop, hfop, map_sub]
  rw [State.traceDistance_eq, State.traceDistance_eq, hdiff]
  gcongr
  exact ContinuousLinearMap.traceNorm_map_le_of_isPositive_of_trace_eq Φ hpos hΦTP hsa

end AxQM
