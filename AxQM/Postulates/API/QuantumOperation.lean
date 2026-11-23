/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.OperatorSumTheorem

/-!
# AxQM.Postulates.API — quantum operations (the operator-sum representation theorem)

A **quantum operation** is the general (not necessarily deterministic) evolution of an open quantum
system — Nielsen & Chuang's object of Chapter 8, of which a *quantum channel* (CPTP, see
`AxQM.IsChannel`) is the trace-preserving special case. Abstractly it is a linear
superoperator `Φ` on operators that is **completely positive** (N&C axiom A3) and
**trace-non-increasing** (`re tr Φ(A) ≤ re tr A` for positive `A`; N&C axiom A1, so that
`tr[Φ(ρ)] ≤ 1` is a probability). By the operator-sum representation theorem (N&C **Theorem 8.1**)
such a `Φ` is exactly one of the form `ρ ↦ ∑ₖ Eₖ ρ Eₖ†` with the **trace condition**
`∑ₖ Eₖ† Eₖ ≤ I` — the inequality (not the equality of a channel), since a general operation may
occur with probability `< 1`.

* `AxQM.IsQuantumOperation` — the predicate on a superoperator `Φ` from the operators of an
  **input** system `S` to those of an **output** system `T` saying `Φ` is a quantum operation:
  completely positive and trace-non-increasing (`ContinuousLinearMap.SatisfiesOperationAxioms`).
  N&C's Theorem 8.1 explicitly allows the input and output Hilbert spaces to differ; the
  same-system case is the specialisation `T = S`. This is the abstract quantum-operation object
  that the section-8.2 exercises (8.3, 8.5, 8.6, Theorem 8.3, …) refer to.
* `AxQM.isQuantumOperation_iff_isOperatorSum` — **Theorem 8.1 for a quantum system**: `Φ`
  is a quantum operation iff it admits an operator-sum (Kraus) representation
  `ContinuousLinearMap.IsOperatorSum E Φ` (a finite family `E` with `Φ = krausSumₗ E` and
  `∑ₖ Eₖ† Eₖ ≤ 1`). This is `ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum` read
  at the physical systems `S`, `T`.
* `AxQM.IsQuantumOperation.isPositive_apply` /
  `AxQM.IsQuantumOperation.re_trace_apply_le_one` — the physical meaning for
  states: a quantum operation sends each state `ρ` to a *subnormalised density operator*
  `Φ ρ` — a positive operator whose trace `tr[Φ(ρ)] ≤ 1` is the probability the process occurs.

`IsQuantumOperation` is phrased in terms of operators `S.space →L[ℂ] S.space`, the density
operator `State.op`, `SatisfiesOperationAxioms`, `krausSumₗ` and `LinearMap.trace`, exactly like the
trace-preserving `IsChannel`. The underlying operator-sum theorem is general Hilbert-space
mathematics, proved in `ToMathlib/Analysis/InnerProductSpace/OperatorSumTheorem.lean`.

## Design notes

* **Why a predicate on a superoperator `Φ`, not a map `State S → State S`.** A quantum operation is
  generally *not* trace-preserving, so `Φ ρ` is a subnormalised density operator (`tr ≤ 1`), which
  is **not** a `State` (a `State` has trace one). The trace-preserving channel `IsChannel` can be
  phrased on `State S → State S`; a general operation cannot, so it is stated on the superoperator,
  matching how N&C and the section-8.2 development (`SatisfiesOperationAxioms Φ`,
  `IsOperatorSum E Φ`) speak of it. The bridge lemmas re-expose the physical content on `State`.
* **Axiom A2.** Convex-linearity on density operators is subsumed by modelling `Φ` as a genuine
  `ℂ`-linear superoperator (the unique linear extension of a convex-linear map, the density
  operators spanning the operator space); see `ContinuousLinearMap.SatisfiesOperationAxioms`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A quantum operation from system `S` to system `T`** (Nielsen & Chuang, Chapter 8; the object
of the operator-sum representation theorem, **Theorem 8.1**). A superoperator
`Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)` is a quantum operation when it is

* **completely positive** (`ContinuousLinearMap.IsCompletelyPositive`, N&C axiom A3), and
* **trace-non-increasing** (`ContinuousLinearMap.IsTraceNonIncreasing`, N&C axiom A1: for every
  positive operator `A`, `re tr(Φ A) ≤ re tr A`, so that `tr[Φ(ρ)] ≤ 1` on a state `ρ`).

Axiom A2 (convex-linearity on density operators) is subsumed by the `ℂ`-linearity of `Φ`. This is
`ContinuousLinearMap.SatisfiesOperationAxioms Φ`, read as a physical condition on a map between the
operators of two quantum systems. N&C allows the input system `S` and output system `T` to differ;
the same-system case is `T = S`. By `isQuantumOperation_iff_isOperatorSum` (Theorem 8.1) this is
equivalent to `Φ` having an operator-sum representation `ρ ↦ ∑ₖ Eₖ ρ Eₖ†` with `∑ₖ Eₖ† Eₖ ≤ I`. -/
def IsQuantumOperation (Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)) : Prop :=
  ContinuousLinearMap.SatisfiesOperationAxioms Φ

/-- **Nielsen–Chuang Theorem 8.1, for a quantum system.** A superoperator `Φ` between the operators
of quantum systems `S` and `T` is a quantum operation (`IsQuantumOperation`, i.e. completely
positive and trace-non-increasing — axioms A1, A2, A3) **iff** it admits an operator-sum (Kraus)
representation: a finite family of operation elements `E : ι → (S.space →L[ℂ] T.space)` with
`Φ ρ = ∑ₖ Eₖ ρ Eₖ†` (`Φ = krausSumₗ E`) and the trace condition `∑ₖ Eₖ† Eₖ ≤ 1`
(`ContinuousLinearMap.IsOperatorSum E Φ`).

This is the operator-sum theorem
`ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum` for the systems `S`, `T`. -/
theorem isQuantumOperation_iff_isOperatorSum
    (Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)) :
    IsQuantumOperation Φ ↔
      ∃ (ι : Type) (_ : Fintype ι) (E : ι → S.space →L[ℂ] T.space),
        ContinuousLinearMap.IsOperatorSum E Φ := by
  unfold IsQuantumOperation
  exact ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum Φ

/-- **A quantum operation sends a state to a positive operator.** For a quantum operation `Φ` and a
state `ρ` of the input system, the output `Φ ρ` is a positive operator — a valid (unnormalised)
density operator, part of the physical requirement A3. Proved from the operator-sum representation
(`isQuantumOperation_iff_isOperatorSum`): `Φ ρ.op = ∑ₖ Eₖ ρ Eₖ†` is a sum of conjugations of the
positive operator `ρ.op` (`ContinuousLinearMap.krausSumₗ_isPositive`). -/
theorem IsQuantumOperation.isPositive_apply
    {Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)}
    (hΦ : IsQuantumOperation Φ) (ρ : State S) : (Φ ρ.op).IsPositive := by
  obtain ⟨ι, _, E, hE⟩ := (isQuantumOperation_iff_isOperatorSum Φ).mp hΦ
  rw [hE.1]
  exact ContinuousLinearMap.krausSumₗ_isPositive E ρ.isPositive_op

/-- **A quantum operation does not increase probability** (Nielsen & Chuang axiom A1). For a quantum
operation `Φ` and a state `ρ` of the input system, `tr[Φ(ρ)] ≤ 1`: the trace of the output — the
probability that the process represented by `Φ` occurs on input `ρ` — is at most one. Immediate from
trace-non-increasing applied to the density operator `ρ.op` (positive, trace one). -/
theorem IsQuantumOperation.re_trace_apply_le_one
    {Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (T.space →L[ℂ] T.space)}
    (hΦ : IsQuantumOperation Φ) (ρ : State S) :
    RCLike.re (LinearMap.trace ℂ T.space (Φ ρ.op : T.space →ₗ[ℂ] T.space)) ≤ 1 := by
  obtain ⟨_, hTNI⟩ := hΦ
  have h := hTNI ρ.op (ContinuousLinearMap.nonneg_iff_isPositive.2 ρ.isPositive_op)
  rwa [ρ.trace_op_eq_one, RCLike.one_re] at h

end AxQM
