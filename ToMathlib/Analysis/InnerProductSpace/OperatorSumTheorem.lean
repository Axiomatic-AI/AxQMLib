/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumReverse

/-!
# The operator-sum representation theorem (Nielsen–Chuang Theorem 8.1)

This file assembles the two directions established by the `OperatorSum*` development into the single
equivalence that is Nielsen & Chuang **Theorem 8.1** (*Quantum Computation and Quantum Information*,
§8.2.4, Box 8.1, Eq. (8.50)):

a map `E` satisfies the operation axioms A1–A3 exactly when it has an operator-sum form
`E(ρ) = Σᵢ Eᵢ ρ Eᵢ†`, with operators `Eᵢ` from the input to the output space and `Σᵢ Eᵢ† Eᵢ ≤ I`.

At the abstract operator level the left-hand side is
`ContinuousLinearMap.SatisfiesOperationAxioms Φ`
(complete positivity `IsCompletelyPositive`, axiom A3, together with trace-non-increasing
`IsTraceNonIncreasing`, axiom A1; axiom A2 — convex-linearity — is subsumed by modelling `Φ` as a
genuine `ℂ`-linear superoperator), and the right-hand side is the existence of a finite family `E`
with `ContinuousLinearMap.IsOperatorSum E Φ` (`Φ = krausSumₗ E` and `Σᵢ Eᵢ† Eᵢ ≤ 1`). The two
operators `Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)` carry independent input space `H` and output space
`G`, exactly matching N&C's "operators which map the input Hilbert space to the output Hilbert
space".

## Main results

* `ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum` — **N&C Theorem 8.1**: a
  superoperator `Φ` satisfies the operation axioms A1, A2, A3 iff it has an operator-sum (Kraus)
  representation. The forward (`⇐`) direction is `IsOperatorSum.satisfiesAxioms`; the reverse
  (`⇒`) direction is `SatisfiesOperationAxioms.isOperatorSum`.

This is general finite-dimensional complex Hilbert-space operator mathematics. The physics
reading — a *quantum operation on a quantum system* — is
`AxQM.isQuantumOperation_iff_isOperatorSum`, which states this equivalence for quantum operations.
-/

open scoped TensorProduct

noncomputable section

@[expose] public section

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **Nielsen–Chuang Theorem 8.1 (operator-sum representation theorem).** A superoperator
`Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)` satisfies the quantum-operation axioms A1, A2, A3
(`SatisfiesOperationAxioms`: completely positive and trace-non-increasing) **iff** it has an
operator-sum (Kraus) representation — a finite family of operation elements `E : ι → (H →L[ℂ] G)`
with `Φ = krausSumₗ E` (i.e. `Φ ρ = Σᵢ Eᵢ ρ Eᵢ†`) and the trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`
(`IsOperatorSum E Φ`).

The forward (`⇐`) direction — an operator sum is a quantum operation — is
`IsOperatorSum.satisfiesAxioms` (complete positivity of `krausSumₗ`, and the trace bound from
`Σᵢ Eᵢ† Eᵢ ≤ 1`). The reverse (`⇒`) direction — a quantum operation is an operator sum — is
`SatisfiesOperationAxioms.isOperatorSum` (the Choi construction, extended to all operators by
convex-linearity); it in fact yields a representation with at most `finrank ℂ (H ⊗ G)` operation
elements. -/
theorem satisfiesOperationAxioms_iff_isOperatorSum
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)) :
    SatisfiesOperationAxioms Φ ↔
      ∃ (ι : Type) (_ : Fintype ι) (E : ι → H →L[ℂ] G), IsOperatorSum E Φ := by
  constructor
  · intro hΦ
    obtain ⟨E, hE⟩ := hΦ.isOperatorSum
    exact ⟨_, inferInstance, E, hE⟩
  · rintro ⟨ι, _, E, hE⟩
    exact hE.satisfiesAxioms

end ContinuousLinearMap
