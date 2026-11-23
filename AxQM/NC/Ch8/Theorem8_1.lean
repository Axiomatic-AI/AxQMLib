/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumOperation

/-!
# Nielsen & Chuang, Theorem 8.1 (Operator-sum representation theorem)

*(N&C p. 368.)*

E satisfies axioms A1,A2,A3 iff E(ρ)=ΣE_iρE_i† with ΣE_i†E_i≤I.

Here the three axioms of a quantum operation `E` (N&C §8.2.4) are:

* **A1** — `tr[E(ρ)]` is the probability that the process represented by `E` occurs, so
  `0 ≤ tr[E(ρ)] ≤ 1` (trace-non-increasing).
* **A2** — `E` is convex-linear on density operators: `E(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ E(ρᵢ)`.
* **A3** — `E` is completely positive: `I_R ⊗ E` takes positive operators to positive operators for
  every auxiliary system `R`.

## Where this is formalised

Theorem 8.1 is formalised at two levels.

**The mathematical core (`ToMathlib/`).** At the abstract operator level the theorem is a
statement of finite-dimensional complex Hilbert-space linear algebra over an input space `H` and an
output space `G`. It is the central result of §8.2:

* `ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum`
  (`ToMathlib/Analysis/InnerProductSpace/OperatorSumTheorem.lean`) — **Theorem 8.1**:
  `SatisfiesOperationAxioms Φ ↔ ∃ ι E, IsOperatorSum E Φ`, i.e. `Φ` is completely positive
  (A3, `ContinuousLinearMap.IsCompletelyPositive`) and trace-non-increasing
  (A1, `ContinuousLinearMap.IsTraceNonIncreasing`) — with A2 subsumed by `ℂ`-linearity — iff
  `Φ ρ = ∑ᵢ Eᵢ ρ Eᵢ†` with `∑ᵢ Eᵢ† Eᵢ ≤ 1` (`ContinuousLinearMap.IsOperatorSum`).
  * Forward `⇐` (`ContinuousLinearMap.IsOperatorSum.satisfiesAxioms`): an operator sum is completely
    positive (`krausSumₗ_isCompletelyPositive`) and trace-non-increasing (from `∑ᵢ Eᵢ† Eᵢ ≤ 1`).
  * Reverse `⇒` (`ContinuousLinearMap.SatisfiesOperationAxioms.isOperatorSum`): the Choi
    construction `σ = (I_R ⊗ E)(|α⟩⟨α|)` is positive (`choiOp_isPositive`), its PSD decomposition
    yields operation elements (`krausOfChoi`) reproducing `E` on pure states, extended to all
    operators by the polarization identity, with the trace bound `∑ᵢ Eᵢ† Eᵢ ≤ 1` from A1. This
    yields a representation with at most `finrank ℂ (H ⊗ G)` operation elements.

**The physics reading (`Postulates/API`).** For a quantum operation *on a quantum system*, the
theorem is stated in terms of `QSystem` and `State` in
`AxQM/Postulates/API/QuantumOperation.lean`:

* `AxQM.IsQuantumOperation` — the quantum-operation predicate on a superoperator between
  the operators of an input system `S` and an output system `T`.
* `AxQM.isQuantumOperation_iff_isOperatorSum` — **Theorem 8.1 for a quantum system**:
  `IsQuantumOperation Φ ↔ ∃ ι E, IsOperatorSum E Φ`.
* `AxQM.IsQuantumOperation.isPositive_apply` /
  `AxQM.IsQuantumOperation.re_trace_apply_le_one` — the physical content on `State`: a
  quantum operation sends each state to a subnormalised density operator `Φ ρ` (positive, with
  `tr[Φ(ρ)] ≤ 1` the probability the process occurs).

This is the abstract quantum-operation object used by the other section-8.2 items (Exercise
8.5, Exercise 8.6, Theorem 8.3), which speak of "quantum operations" via `SatisfiesOperationAxioms`
/ `IsOperatorSum`.
-/
