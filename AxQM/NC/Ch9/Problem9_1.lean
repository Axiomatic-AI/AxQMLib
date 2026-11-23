/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AlbertiFidelity
import ToMathlib.Analysis.InnerProductSpace.AlbertiFidelity

/-!
# Nielsen & Chuang, Problem 9.1 (Alternate characterization of the fidelity)

Alternate characterization: F(rho,sigma)=inf_P tr(rho P)tr(sigma P^-1) over invertible positive P.

## The printed statement is an erratum; the true result is Alberti's theorem

The identity is genuine **only with `F(ρ, σ)²` on the left** — this is
**Alberti's theorem** (P. M. Alberti, *A note on the transition probability over
C\*-algebras*, Lett. Math. Phys. 7 (1983) 25–32):
```
F(ρ, σ)² = inf_P tr(ρ P) tr(σ P⁻¹).
```
With N&C's *square-root* fidelity `F(ρ, σ) = tr √(√ρ σ √ρ)` (for which
`F(ρ, ρ) = 1` and `F(|ψ⟩, |ϕ⟩) = |⟨ψ|ϕ⟩|`, so `0 ≤ F ≤ 1`), the infimum equals
`F²`, and `F² < F` for every non-trivial pair `0 < F < 1`. Hence the printed
`(9.145)` — with an unsquared `F` — is **false as written**, per the obligation
to read the source critically rather than silently repair it.

The lower-bound direction of Alberti's theorem is a Cauchy–Schwarz argument:
`tr(ρ P) = ‖√P √ρ‖₂²` and `tr(σ P⁻¹) = ‖(√P)⁻¹ √σ‖₂²` in the Hilbert–Schmidt
norm, and inserting the polar unitary of `√ρ √σ`,
`tr(ρ P) tr(σ P⁻¹) ≥ (tr|√ρ √σ|)² = F(ρ, σ)²`, with equality at the minimizer.

Both halves of the item are formalised: the **refutation** of the printed identity,
and the **corrected identity** `F² = inf_P …`. The corrected identity is proved at the full
**non-commuting** generality of the book, for **all** positive `ρ, σ` — as an `IsGLB`
(`ContinuousLinearMap.isGLB_albertiProduct`), which is the exact infimum form N&C states, and
sharpened to an `IsLeast` (`ContinuousLinearMap.isLeast_albertiProduct`) for the strictly
positive (invertible) states where the minimizer exists — see the operator-level development in
`ToMathlib/Analysis/InnerProductSpace/AlbertiFidelity.lean` below. The refutation and the
classical (commuting-state) specialisation, together with the concrete qubit witness that
pins the infimum at `F² = 9/25 < 3/5 = F`, live in `Concrete/AlbertiFidelity.lean`.

For a density operator with non-trivial kernel the minimizer `(√ρ)⁻¹ √(√ρ σ √ρ) (√ρ)⁻¹` does
not exist, so the identity there is a genuine *infimum* (`IsGLB`) that is approached but not
attained; it is reached by the regularisation `ρ ↝ ρ + ε` limit, which the `IsGLB` result
carries out.

The refutation is a statement about concrete matrices and real numbers. The refuting states are
the real-diagonal density matrices `ρ = diag(9/10, 1/10)`
and `σ = diag(1/10, 9/10)`: genuine density matrices whose entries happen to be
real, so the fidelity and the functional `tr(ρ P) tr(σ P⁻¹)` are computed over
`ℝ` (identical values to the complex computation, and the available `CFC.sqrt`
matrix API — mirroring `Concrete/PolarDecompositionExample.lean`). One real
counterexample refutes the general complex claim, so nothing is weakened.

The formalisation is in `AxQM/Concrete/AlbertiFidelity.lean`:

* `AxQM.Concrete.matrixFidelity` — N&C's fidelity
  `F(ρ, σ) = tr √(√ρ σ √ρ)` on matrices (the quantity `(9.145)` is about).
* `AxQM.Concrete.albertiProduct` — the functional
  `P ↦ tr(ρ P) tr(σ P⁻¹)` of the right-hand side of `(9.145)`.
* `AxQM.Concrete.cfc_sqrt_diagonal` — the reusable computation that the
  functional-calculus square root of a nonnegative real diagonal matrix is the
  entrywise square root.
* `AxQM.Concrete.matrixFidelity_diagonal` — the fidelity of commuting
  (diagonal) density matrices is the classical Bhattacharyya coefficient
  `∑ᵢ √(pᵢ qᵢ)` (the quantum fidelity restricts to the classical fidelity on
  commuting states).
* `AxQM.Concrete.posDef_one_le_diag_mul_inv_diag` — for positive definite
  `P`, `1 ≤ Pᵢᵢ (P⁻¹)ᵢᵢ` (Cauchy–Schwarz via `√P`); the operator ingredient letting
  the Alberti lower bound range over all positive `P`, not just diagonal ones.
* `AxQM.Concrete.albertiProduct_diagonal_ge_fidelity_sq` — **Alberti's lower
  bound** for commuting states, over *all* invertible positive `P`:
  `F(ρ, σ)² ≤ tr(ρ P) tr(σ P⁻¹)`.
* `AxQM.Concrete.albertiProduct_diagonal_minimizer_eq_fidelity_sq` — the
  minimizer `P = diag(√(qᵢ/pᵢ))` attains `F(ρ, σ)²`.
* `AxQM.Concrete.isLeast_albertiProduct_diagonal` — **the corrected `(9.145)`
  for commuting states**: `F(ρ, σ)²` is the least value of `P ↦ tr(ρ P) tr(σ P⁻¹)` over
  invertible positive `P`.
* `AxQM.Concrete.isLeast_albertiProduct_qubitDiagExample` — the corrected
  identity instantiated at the counterexample states: the true infimum is `F² = 9/25`.
* `AxQM.Concrete.matrixFidelity_qubitDiagExample`,
  `AxQM.Concrete.albertiProduct_qubitDiagExample` — the concrete witness
  `ρ = diag(9/10, 1/10)`, `σ = diag(1/10, 9/10)`, `P = diag(1/9, 1)`:
  `F(ρ, σ) = 3/5` while `tr(ρ P) tr(σ P⁻¹) = 9/25`.
* `AxQM.Concrete.weightEx_posDef` — the witness `P = diag(1/9, 1)` is
  positive definite, so it is an admissible (invertible positive) `P` in
  `(9.145)`'s index set.
* `AxQM.Concrete.albertiProduct_qubitDiagExample_eq_fidelity_sq` — the
  witnessed value is exactly `F(ρ, σ)² = (3/5)²`, the Alberti minimum (off by a
  square).
* `AxQM.Concrete.exists_posDef_albertiProduct_lt_fidelity` /
  `AxQM.Concrete.fidelity_not_lower_bound_of_albertiProduct` — **the
  refutation of `(9.145)`**: there is an *invertible positive* (`PosDef`) `P` with
  `tr(ρ P) tr(σ P⁻¹) < F(ρ, σ)`, so `F(ρ, σ)` is not a lower bound of the
  functional over `(9.145)`'s index set and cannot be the infimum.

## The general non-commuting case (operator level, `ToMathlib/`)

Alberti's theorem for *arbitrary* (non-commuting) operators is a statement about
positive operators on a complex Hilbert space and their trace norm/CFC square roots —
general operator analysis — so it is stated in
`ToMathlib/Analysis/InnerProductSpace/AlbertiFidelity.lean`, with `F` in trace-norm form
`F(ρ, σ) = ‖√ρ √σ‖₁` (`= tr √(√ρ σ √ρ)`, the operator content of
`AxQM.State.fidelity_eq_traceNorm`):

* `ContinuousLinearMap.albertiProduct ρ σ P` — the functional `tr(ρ P) · tr(σ P⁻¹)`
  (`Ring.inverse P` for the inverse), the operator-level right-hand side of `(9.145)`.
* `ContinuousLinearMap.traceNorm_cfc_sqrt_mul_sq_le_albertiProduct` — **Alberti's lower
  bound** `‖√ρ √σ‖₁² ≤ tr(ρ P) tr(σ P⁻¹)` for *arbitrary* positive `ρ, σ` and invertible
  positive `P` (no commutativity, no invertibility of the states). Cauchy–Schwarz for the
  Hilbert–Schmidt pairing at the fidelity-maximising unitary.
* `ContinuousLinearMap.traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj` — the operator
  identity `‖√ρ √σ‖₁ = tr √(√ρ σ √ρ)` reconciling the two forms of the fidelity.
* `ContinuousLinearMap.albertiMinimizer ρ σ` — the minimizer `(√ρ)⁻¹ √(√ρ σ √ρ) (√ρ)⁻¹`,
  and `ContinuousLinearMap.albertiMinimizer_isStrictlyPositive` /
  `ContinuousLinearMap.albertiProduct_albertiMinimizer`: it is invertible positive and
  attains `‖√ρ √σ‖₁²` (both traces collapse to `tr √(√ρ σ √ρ)`).
* `ContinuousLinearMap.isLeast_albertiProduct` — **Alberti's theorem** at full
  non-commuting generality for strictly positive `ρ, σ`: `F(ρ, σ)²` is the *least* value
  of `tr(ρ P) tr(σ P⁻¹)` over all invertible positive `P`.
* `ContinuousLinearMap.isGLB_albertiProduct` — **the item's headline result: Alberti's
  theorem for arbitrary positive `ρ, σ`** (the exact `inf` form of N&C's `(9.145)`, corrected
  to `F²`): `F(ρ, σ)²` is the *infimum* of `tr(ρ P) tr(σ P⁻¹)` over all invertible positive
  `P`, with **no** invertibility assumption on the states — covering the rank-deficient case
  where the infimum is approached but not attained.
* `ContinuousLinearMap.tendsto_albertiRegularization` / `continuousOn_cfc_real_sqrt` — the
  analytic step reaching the non-invertible case: `‖√(ρ+δ) √(σ+δ)‖₁² → F(ρ, σ)²` as the
  regularisation `δ → 0⁺`, via continuity of `cfc Real.sqrt` on the nonnegative cone.
-/
