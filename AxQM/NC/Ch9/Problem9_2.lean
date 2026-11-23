/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity

/-!
# Nielsen & Chuang, Problem 9.2 (Concentrating the entanglement fidelity in one operation element)

Show for each rho there exist operation elements {E_i} with F(rho,E)=|tr(rho E_1)|^2.

Here `F(ρ, E)` is the **entanglement fidelity** of Section 9.3, computed from any set of operation
elements by `F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²` (N&C `(9.135)`). The problem asks us to exhibit, for a given
`ρ`, a set of operation elements for the *same* operation in which the whole sum collapses onto its
first term.

## The mathematics: unitary freedom rotates the trace vector

Writing `vᵢ = tr(ρ Eᵢ)`, the fidelity is `‖v‖²` for the complex vector `v`. Any two sets of
operation elements for the same operation are related by a unitary coefficient matrix (the
**unitary freedom in the operator-sum representation**, N&C Theorem 8.2), which acts on `v` by the
same unitary; a unitary preserves `‖v‖²`, so `F(ρ, E)` is well-defined, and one may *choose* the
unitary so that `v` is rotated entirely into its first coordinate — then `tr(ρ E₁) = ‖v‖`, every
other `tr(ρ Eᵢ)` vanishes, and `F(ρ, E) = |tr(ρ E₁)|²`.

The statement is about the operation elements — bounded operators `H →L[ℂ] H` — and the trace. It
uses the operator-sum representation and the unitary-freedom theorem
(`ContinuousLinearMap.krausSumₗ`, `ContinuousLinearMap.krausSumₗ_eq_iff_exists_mem_unitaryGroup`,
both in `ToMathlib/Analysis/InnerProductSpace/OperatorSum.lean`).

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/EntanglementFidelity.lean`:

* `ContinuousLinearMap.entanglementFidelity` — the entanglement fidelity
  `F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²` of a state `ρ` under the operation with operation elements `E`
  (N&C `(9.135)`).
* `ContinuousLinearMap.trace_mul_sum_smul` — linearity of `tr(ρ ·)` in the operation-element
  argument, the reusable step behind both results below.
* `Matrix.sum_normSq_mulVec_eq_of_mem_unitaryGroup` — a unitary matrix preserves the `ℓ²` sum of
  squared norms of a vector, `Σᵢ |Σⱼ uᵢⱼ wⱼ|² = Σⱼ |wⱼ|²`.
* `ContinuousLinearMap.entanglementFidelity_eq_of_krausSumₗ_eq` — **well-definedness**: `F(ρ, E)`
  depends on the operation elements only through the operation `krausSumₗ E` they generate. This is
  what makes `(9.135)` a definition of the *intrinsic* fidelity `F(ρ, E)` rather than of the chosen
  elements.
* `ContinuousLinearMap.exists_krausSumₗ_eq_entanglementFidelity_eq_normSq_trace` — **Problem 9.2**:
  for each `ρ` there exist operation elements `F` for the same operation
  (`krausSumₗ F = krausSumₗ E`) with `tr(ρ Fᵢ) = 0` for all `i ≠ 0` and
  `F(ρ, E) = |tr(ρ F₀)|²`, i.e. N&C `(9.146)`.
-/
