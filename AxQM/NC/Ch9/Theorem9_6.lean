/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fidelity
import AxQM.Postulates.API.QuantumChannel
import ToMathlib.Analysis.InnerProductSpace.FidelityMonotone

/-!
# Nielsen & Chuang, Theorem 9.6 (Monotonicity of the fidelity)

Monotonicity of fidelity: F(E(rho),E(sigma))>=F(rho,sigma) for trace-preserving E.

A physical process can never *increase* the distinguishability of two states measured by the
fidelity: applying a channel to both arguments can only bring them closer (fidelity closer to `1`).
This is the fidelity counterpart of the trace-distance contractivity `D(E(ρ), E(σ)) ≤ D(ρ, σ)`
(`AxQM.traceDistance_channel_le`, Theorem 9.2) — with the inequality reversed, since larger
fidelity means *less* distinguishable.

## Statement

A **trace-preserving quantum operation** is a quantum *channel* (`AxQM.IsChannel f`): the
state-map `f` is the restriction of a completely-positive, trace-preserving superoperator. The
distance is the **fidelity** `AxQM.State.fidelity` (`ρ.fidelity σ = F(ρ, σ)`, N&C
`(9.53)`). The result is

* `AxQM.State.fidelity_le_fidelity_channel` — `F(ρ, σ) ≤ F(f ρ, f σ)` for every channel
  `f` and all states `ρ, σ`.

## Proof

The proof reduces to the operator-level heart, proved in `ToMathlib/` as
`ContinuousLinearMap.traceNorm_cfc_sqrt_mul_le_krausSum`:

  `‖√ρ √σ‖₁ ≤ ‖√(∑ₖ Eₖ ρ Eₖ†) √(∑ₖ Eₖ σ Eₖ†)‖₁`

for a **complete** Kraus family (`∑ₖ Eₖ† Eₖ = 1`). That inequality is N&C's proof (§9.3): Uhlmann's
theorem (Theorem 9.4) realizes `‖√ρ √σ‖₁` as an overlap of purifications, which is *transported*
through the channel's environment dilation into a larger ancilla and bounded there by the
arbitrary-ancilla Uhlmann upper bound (Theorem 9.4, generalized) — completeness of the Kraus family
making the overlap invariant.

Two ingredients bridge `IsChannel f` to that lemma:

* **Fidelity as a trace norm.** `State.fidelity_eq_traceNorm` rewrites both fidelities to
  `‖√· √·‖₁`.
* **A complete Kraus family for the channel.** From complete positivity + trace preservation the
  channel's superoperator has an operator-sum representation `Φ = krausSumₗ E`
  (`satisfiesOperationAxioms_iff_isOperatorSum`, N&C Theorem 8.1), whose operation elements satisfy
  `∑ₖ Eₖ† Eₖ ≤ 1`; **trace preservation upgrades this to the completeness relation**
  `∑ₖ Eₖ† Eₖ = 1` via `ContinuousLinearMap.sum_adjoint_comp_eq_one_of_trace_krausSumₗ_eq` (the
  equality-sharpening of the trace bound, `ToMathlib/`, mirroring its `≤` sibling
  `sum_adjoint_comp_le_one_of_isTraceNonIncreasing`). Then `(f ρ).op = Φ ρ.op = ∑ₖ Eₖ ρ.op Eₖ†`.

N&C Theorem 9.6, p. 414.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Monotonicity of the fidelity under a trace-preserving quantum operation** (Nielsen & Chuang,
Theorem 9.6, `(9.87)`): a quantum channel `f` never decreases the fidelity,
`F(ρ, σ) ≤ F(f ρ, f σ)` for all states `ρ, σ`.

The proof reduces, through `State.fidelity_eq_traceNorm`, to the operator-sum
monotonicity `ContinuousLinearMap.traceNorm_cfc_sqrt_mul_le_krausSum` (`ToMathlib/`, the
Uhlmann-plus-dilation argument). Complete positivity of the channel supplies a Kraus representation
`Φ = krausSumₗ E`, and trace preservation upgrades its trace bound to the completeness relation
`∑ₖ Eₖ† Eₖ = 1` required by that lemma. -/
theorem State.fidelity_le_fidelity_channel {f : State S → State S} (hf : IsChannel f)
    (ρ σ : State S) : ρ.fidelity σ ≤ (f ρ).fidelity (f σ) := by
  obtain ⟨Φ, hΦCP, hΦTP, hfop⟩ := hf
  -- Kraus representation of `Φ` (trace-preservation ⟹ trace-non-increasing ⟹ quantum operation).
  obtain ⟨ι, _, E, hΦeq, _⟩ :=
    (ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum Φ).mp
      ⟨hΦCP, fun τ _ => le_of_eq (by rw [hΦTP τ])⟩
  -- Completeness `∑ₖ Eₖ† Eₖ = 1` from trace preservation (the equality-sharpening of the
  -- operator-sum trace bound, in `ToMathlib/`).
  have hcomp : ∑ i, (ContinuousLinearMap.adjoint (E i)).comp (E i) = 1 :=
    ContinuousLinearMap.sum_adjoint_comp_eq_one_of_trace_krausSumₗ_eq E
      fun ρ => by rw [← hΦeq]; exact hΦTP ρ
  -- Reduce to the operator-level monotonicity through the trace-norm bridge.
  have hfk : ∀ τ : State S, (f τ).op = ContinuousLinearMap.krausSumₗ E τ.op :=
    fun τ => by rw [hfop, hΦeq]
  rw [State.fidelity_eq_traceNorm, State.fidelity_eq_traceNorm, hfk ρ, hfk σ]
  exact ContinuousLinearMap.traceNorm_cfc_sqrt_mul_le_krausSum E hcomp
    ρ.isDensity.nonneg σ.isDensity.nonneg

end AxQM
