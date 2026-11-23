/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.PolarDecomposition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Alberti's alternate characterization of the fidelity (Nielsen & Chuang, Problem 9.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 9.1
(p. 423) asks to show the "alternate characterization of the fidelity", N&C
equation `(9.145)`:
```
F(ρ, σ) = inf_P tr(ρ P) tr(σ P⁻¹),
```
where `F(ρ, σ) = tr √(√ρ σ √ρ)` is N&C's fidelity (their `(9.53)`, the
*square-root* fidelity, with `F(ρ, ρ) = 1` and `F(|ψ⟩, |ϕ⟩) = |⟨ψ|ϕ⟩|`) and the
infimum ranges over invertible positive matrices `P`.

## The literal statement is an erratum (off by a square)

The genuine theorem behind this problem is **Alberti's theorem** (P. M. Alberti,
*A note on the transition probability over C\*-algebras*, Lett. Math. Phys. 7
(1983) 25–32), which reads
```
F(ρ, σ)² = inf_P tr(ρ P) tr(σ P⁻¹).
```
The right-hand side equals `F(ρ, σ)²`, **not** `F(ρ, σ)`. One direction is a
one-line Cauchy–Schwarz argument: writing `tr(ρ P) = ‖√P √ρ‖₂²` and
`tr(σ P⁻¹) = ‖(√P)⁻¹ √σ‖₂²` (Hilbert–Schmidt norms) and inserting the polar
unitary of `√ρ √σ`,
```
tr(ρ P) tr(σ P⁻¹) = ‖√P √ρ‖₂² ‖(√P)⁻¹ √σ‖₂² ≥ (tr|√ρ √σ|)² = F(ρ, σ)²,
```
with equality attained at the Alberti minimizer. Since `0 ≤ F ≤ 1` we have
`F² ≤ F`, with `F² < F` whenever `0 < F < 1`; so the infimum equals `F²` and is
*strictly below* `F` for all non-trivial pairs. N&C's printed `(9.145)` is thus
**false as written** — per the obligation to read the source critically rather
than silently repair it, this file records precisely why and proves the
refutation.

Beyond disproving the printed identity we also **prove the corrected one for
commuting states**. For commuting density matrices (`ρ, σ` diagonal — the case where
the fidelity is the classical Bhattacharyya coefficient), we prove `IsLeast … F²`: the
squared fidelity is the infimum of `P ↦ tr(ρ P) tr(σ P⁻¹)` over Alberti's *full* index
set of invertible positive `P`, attained at the diagonal minimizer `P = diag(√(qᵢ/pᵢ))`.
The lower bound holds over **all** positive `P`, not just diagonal ones — the operator
content of Alberti's theorem specialized to commuting inputs.

**Scope and remaining work.** N&C's `(9.145)` is stated for *arbitrary* `ρ, σ`, so the
commuting-state corrected identity here is only a special case: the general non-commuting
Alberti identity `F(ρ,σ)² = inf_P tr(ρP)tr(σP⁻¹)` for arbitrary `ρ, σ` is not formalised here.
Its proof is the Hilbert–Schmidt/trace-norm/polar-unitary argument sketched above, and
the required apparatus already exists in the library at the operator level:
`ContinuousLinearMap.traceNorm` with `traceNorm_eq_iSup` /
`isGreatest_norm_trace_mul_unitary` (the variational `tr|M| = sup_U |tr(UM)|`),
`LinearMap.norm_hsPairing_sq_le` (Hilbert–Schmidt Cauchy–Schwarz), and
`AxQM.State.fidelity_eq_traceNorm` (`F = ‖√ρ √σ‖₁`). Landing the general case
needs a `Matrix ↔ ContinuousLinearMap` bridge for these quantities plus the general
minimizer, which is a multi-declaration development of its own. The commuting case
proved here already pins the infimum of the counterexample states at `F² = 9/25`,
strictly below the `F = 3/5` the erratum asserts.

## What this file proves

Everything here is **pure mathematics over matrices**; the statement of Problem 9.1 is in
`AxQM/NC/Ch9/Problem9_1.lean`.

The refuting states are the *real-diagonal* density matrices
`ρ = diag(9/10, 1/10)` and `σ = diag(1/10, 9/10)`. These are genuine density
matrices whose entries happen to be real; the fidelity `tr √(√ρ σ √ρ)` and the
functional `tr(ρ P) tr(σ P⁻¹)` are basis-independent real numbers, identical to
the values obtained over `ℂ`, so we compute over `ℝ` (matching the precedent of
`AxQM/Concrete/PolarDecompositionExample.lean`, whose real operand has
real polar factors) using the continuous-functional-calculus square root
`CFC.sqrt`. Exhibiting one real counterexample refutes the general (complex)
claim, so nothing is weakened.

## Main definitions and statements

* `matrixFidelity` — N&C's fidelity formula `F(ρ, σ) = tr √(√ρ σ √ρ)` on
  matrices, the quantity `(9.145)` is about.
* `albertiProduct` — the functional `P ↦ tr(ρ P) tr(σ P⁻¹)` of `(9.145)`.
* `cfc_sqrt_diagonal` — the reusable fact that the functional-calculus square
  root of a nonnegative diagonal matrix is the entrywise square root.
* `matrixFidelity_diagonal` — for commuting (diagonal) density matrices the
  quantum fidelity reduces to the classical *Bhattacharyya coefficient*
  `∑ᵢ √(pᵢ qᵢ)` (N&C's remark that the fidelity of commuting states is the
  classical fidelity).
* `posDef_one_le_diag_mul_inv_diag` — for positive definite `P`, `1 ≤ Pᵢᵢ (P⁻¹)ᵢᵢ`
  (a Cauchy–Schwarz fact via `√P`); the operator ingredient of the Alberti lower bound.
* `albertiProduct_diagonal_ge_fidelity_sq` — **Alberti's lower bound** for commuting
  states over *all* invertible positive `P`: `F(ρ, σ)² ≤ tr(ρ P) tr(σ P⁻¹)`.
* `albertiProduct_diagonal_minimizer_eq_fidelity_sq` — the minimizer
  `P = diag(√(qᵢ/pᵢ))` attains `F(ρ, σ)²`.
* `isLeast_albertiProduct_diagonal` — **the corrected `(9.145)` for commuting states**:
  `F(ρ, σ)²` is the least value of `P ↦ tr(ρ P) tr(σ P⁻¹)` over invertible positive `P`.
* `isLeast_albertiProduct_qubitDiagExample` — the same for the counterexample states:
  the true infimum is `F² = 9/25`, strictly below the erratum's claimed `F = 3/5`.
* `matrixFidelity_qubitDiagExample` / `albertiProduct_qubitDiagExample` — the
  concrete witness `ρ = diag(9/10, 1/10)`, `σ = diag(1/10, 9/10)`,
  `P = diag(1/9, 1)`: `F(ρ, σ) = 3/5` while `tr(ρ P) tr(σ P⁻¹) = 9/25`.
* `weightEx_posDef` — the witness `P = diag(1/9, 1)` is positive definite, hence
  an admissible (invertible positive) `P` in `(9.145)`'s index set.
* `albertiProduct_qubitDiagExample_eq_fidelity_sq` — the witnessed value is
  exactly `F(ρ, σ)²` (`9/25 = (3/5)²`), the Alberti minimum.
* `exists_posDef_albertiProduct_lt_fidelity` /
  `fidelity_not_lower_bound_of_albertiProduct` — **the refutation of N&C
  `(9.145)`**: there is an *invertible positive* (`PosDef`) `P` with
  `tr(ρ P) tr(σ P⁻¹) < F(ρ, σ)`, so `F(ρ, σ)` is not a lower bound of the
  functional over `(9.145)`'s index set and cannot equal the infimum.
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix MatrixOrder ComplexOrder BigOperators

/-- **Nielsen & Chuang fidelity formula on matrices** (their `(9.53)`):
`F(ρ, σ) = tr √(√ρ σ √ρ)`. For density matrices `ρ, σ` the matrix `√ρ σ √ρ` is
positive semidefinite, so its continuous-functional-calculus square root has a
nonnegative trace. This is the quantity Nielsen & Chuang's Problem 9.1
(`(9.145)`) is about. -/
noncomputable def matrixFidelity {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℝ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace

/-- The functional `P ↦ tr(ρ P) tr(σ P⁻¹)` appearing on the right-hand side of
Nielsen & Chuang `(9.145)`. The infimum of this functional over invertible
positive `P` is, by Alberti's theorem, `F(ρ, σ)²`. -/
noncomputable def albertiProduct {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ P : Matrix n n ℝ) : ℝ :=
  (ρ * P).trace * (σ * P⁻¹).trace

/-- The continuous-functional-calculus square root of a diagonal matrix with
nonnegative entries is the entrywise square root. Proved from the
polar-decomposition characterization `√(Dᴴ D) = D` for the positive semidefinite
diagonal `D = diag(√dᵢ)`, whose square is `diag(dᵢ)`. -/
theorem cfc_sqrt_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    CFC.sqrt (diagonal d) = diagonal (fun i => Real.sqrt (d i)) := by
  set D : Matrix n n ℝ := diagonal (fun i => Real.sqrt (d i)) with hD
  have hDpsd : D.PosSemidef := by
    rw [hD]
    exact Matrix.posSemidef_diagonal_iff.mpr fun i => Real.sqrt_nonneg (d i)
  have key : Dᴴ * D = diagonal d := by
    rw [hDpsd.isHermitian, hD, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hd i)
  calc CFC.sqrt (diagonal d) = CFC.sqrt (Dᴴ * D) := by rw [key]
    _ = D := Matrix.PosSemidef.sqrt_conjTranspose_mul_self hDpsd

/-- **Fidelity of commuting (diagonal) density matrices = classical Bhattacharyya
coefficient.** For nonnegative diagonals `p, q`, N&C's fidelity of the commuting
density matrices `diag(p)` and `diag(q)` is `F = ∑ᵢ √(pᵢ qᵢ)`, the classical
fidelity of the two distributions — the statement that the quantum fidelity
restricts to the classical one on commuting states. -/
theorem matrixFidelity_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    matrixFidelity (diagonal p) (diagonal q) = ∑ i, Real.sqrt (p i * q i) := by
  have hmid : CFC.sqrt (diagonal p) * diagonal q * CFC.sqrt (diagonal p)
      = diagonal (fun i => p i * q i) := by
    rw [cfc_sqrt_diagonal p hp, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [show Real.sqrt (p i) * q i * Real.sqrt (p i)
        = Real.sqrt (p i) * Real.sqrt (p i) * q i by ring, Real.mul_self_sqrt (hp i)]
  unfold matrixFidelity
  rw [hmid, cfc_sqrt_diagonal (fun i => p i * q i) (fun i => mul_nonneg (hp i) (hq i)),
    Matrix.trace_diagonal]

/-! ### The corrected statement: Alberti's identity for commuting states

The refutation above shows the printed `(9.145)` is false; the genuine theorem is
Alberti's, with `F²` on the left. Here we *prove* that corrected identity for
**commuting** density matrices `ρ = diag(p)`, `σ = diag(q)` — the case where N&C's
fidelity is the classical Bhattacharyya coefficient (`matrixFidelity_diagonal`).

Crucially the lower bound `F² ≤ tr(ρ P) tr(σ P⁻¹)` is established over **all**
invertible positive `P` (not merely diagonal `P`): the operator content of Alberti's
theorem restricted to commuting inputs. Combined with the explicit minimizer
`P = diag(√(qᵢ/pᵢ))`, this yields `IsLeast … F²`, i.e. `F²` *is* the infimum of the
Alberti functional over Alberti's full index set. Only `ρ, σ` are assumed to commute;
the general non-commuting theorem additionally needs the Hilbert–Schmidt/polar-unitary
apparatus sketched in the module docstring. -/

/-- **A diagonal entry of a positive definite matrix times the matching diagonal entry
of its inverse is at least `1`.** With `S := √P` (Hermitian, `S * S = P`, invertible),
`Pᵢᵢ = ∑ₖ Sᵢₖ²`, `(P⁻¹)ᵢᵢ = ∑ₖ (S⁻¹)ᵢₖ²` and `1 = (P⁻¹ S)ᵢᵢ = ∑ₖ Sᵢₖ (S⁻¹)ᵢₖ`, so the
claim is the discrete Cauchy–Schwarz inequality applied to the `i`-th rows of `S` and
`S⁻¹`. This is the operator ingredient that makes the Alberti lower bound hold over all
positive `P`, not only diagonal ones. -/
theorem posDef_one_le_diag_mul_inv_diag {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : P.PosDef) (i : n) :
    1 ≤ P i i * P⁻¹ i i := by
  have h0 : (0 : Matrix n n ℝ) ≤ P := hP.posSemidef.nonneg
  set S : Matrix n n ℝ := CFC.sqrt P with hSdef
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P h0
  have hSherm : S.IsHermitian := (CFC.sqrt_nonneg P).posSemidef.1
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff P h0).mpr hP.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  have hSinvherm : S⁻¹.IsHermitian := hSherm.inv
  have hmulinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hPinv : S⁻¹ * S⁻¹ = P⁻¹ := by rw [← hSS, Matrix.mul_inv_rev]
  have hsymmS : ∀ k, S k i = S i k := fun k => by have := hSherm.apply i k; simpa using this
  have hsymmSinv : ∀ k, S⁻¹ k i = S⁻¹ i k := fun k => by
    have := hSinvherm.apply i k; simpa using this
  have hff : ∑ k, S i k ^ 2 = P i i := by
    rw [← hSS, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [hsymmS k, sq])
  have hgg : ∑ k, S⁻¹ i k ^ 2 = P⁻¹ i i := by
    rw [← hPinv, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [hsymmSinv k, sq])
  have hfg : ∑ k, S i k * S⁻¹ i k = 1 := by
    have hentry : (S * S⁻¹) i i = ∑ k, S i k * S⁻¹ i k := by
      rw [Matrix.mul_apply]; exact Finset.sum_congr rfl (fun k _ => by rw [hsymmSinv k])
    rw [← hentry, hmulinv, Matrix.one_apply_eq]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => S i k) (fun k => S⁻¹ i k)
  rw [hfg, hff, hgg] at hCS
  simpa using hCS

/-- The trace of `diag(p) * P` is the `p`-weighted sum of the diagonal entries of `P`,
`tr(diag(p) · P) = ∑ᵢ pᵢ Pᵢᵢ`. The Alberti functional at a diagonal `ρ = diag(p)` is
built from this. -/
theorem trace_diagonal_mul {n : Type*} [Fintype n] [DecidableEq n]
    (p : n → ℝ) (P : Matrix n n ℝ) :
    (diagonal p * P).trace = ∑ i, p i * P i i := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Finset.sum_ite_eq]

/-- **Alberti's lower bound for commuting states, over all positive `P`.** For diagonal
density matrices `ρ = diag(p)`, `σ = diag(q)` (`p, q ≥ 0`) and *every* invertible
positive `P`, `F(ρ, σ)² ≤ tr(ρ P) tr(σ P⁻¹)`. With `aᵢ = pᵢ Pᵢᵢ`, `bᵢ = qᵢ (P⁻¹)ᵢᵢ`,
`√(aᵢ)√(bᵢ) = √(pᵢqᵢ) · √(Pᵢᵢ(P⁻¹)ᵢᵢ) ≥ √(pᵢqᵢ)` (by `posDef_one_le_diag_mul_inv_diag`), so
`F = ∑ √(pᵢqᵢ) ≤ ∑ √(aᵢ)√(bᵢ)`; the Cauchy–Schwarz bound
`(∑ √(aᵢ)√(bᵢ))² ≤ (∑ aᵢ)(∑ bᵢ) = tr(ρ P) tr(σ P⁻¹)` then closes it. That the bound holds
for *non-diagonal* `P` too is what pins the infimum (a diagonal-only bound would leave a
non-diagonal `P` free to undercut `F²`). -/
theorem albertiProduct_diagonal_ge_fidelity_sq {n : Type*} [Fintype n] [DecidableEq n]
    (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (P : Matrix n n ℝ) (hP : P.PosDef) :
    matrixFidelity (diagonal p) (diagonal q) ^ 2
      ≤ albertiProduct (diagonal p) (diagonal q) P := by
  set a : n → ℝ := fun i => p i * P i i with ha_def
  set b : n → ℝ := fun i => q i * P⁻¹ i i with hb_def
  have ha : ∀ i, 0 ≤ a i := fun i => mul_nonneg (hp i) (hP.posSemidef.diag_nonneg)
  have hb : ∀ i, 0 ≤ b i := fun i => mul_nonneg (hq i) (hP.inv.posSemidef.diag_nonneg)
  have hAP : albertiProduct (diagonal p) (diagonal q) P = (∑ i, a i) * (∑ i, b i) := by
    unfold albertiProduct
    rw [trace_diagonal_mul, trace_diagonal_mul]
  have key : ∀ i, Real.sqrt (p i * q i) ≤ Real.sqrt (a i) * Real.sqrt (b i) := by
    intro i
    have hab : Real.sqrt (a i) * Real.sqrt (b i)
        = Real.sqrt (p i * q i) * Real.sqrt (P i i * P⁻¹ i i) := by
      rw [← Real.sqrt_mul (ha i), ← Real.sqrt_mul (mul_nonneg (hp i) (hq i))]
      congr 1
      simp only [ha_def, hb_def]; ring
    rw [hab]
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _)
      (Real.one_le_sqrt.mpr (posDef_one_le_diag_mul_inv_diag P hP i))
  have hFsum : matrixFidelity (diagonal p) (diagonal q) = ∑ i, Real.sqrt (p i * q i) :=
    matrixFidelity_diagonal p q hp hq
  have hF_nonneg : 0 ≤ matrixFidelity (diagonal p) (diagonal q) := by
    rw [hFsum]; exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hF_le : matrixFidelity (diagonal p) (diagonal q)
      ≤ ∑ i, Real.sqrt (a i) * Real.sqrt (b i) := by
    rw [hFsum]; exact Finset.sum_le_sum (fun i _ => key i)
  have hStepB : (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2 ≤ (∑ i, a i) * (∑ i, b i) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => ha i) (fun i _ => hb i)
      (fun i _ => by rw [mul_pow, Real.sq_sqrt (ha i), Real.sq_sqrt (hb i)])
  calc matrixFidelity (diagonal p) (diagonal q) ^ 2
      ≤ (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2 := by gcongr
    _ ≤ (∑ i, a i) * (∑ i, b i) := hStepB
    _ = albertiProduct (diagonal p) (diagonal q) P := hAP.symm

/-- **The Alberti minimizer for commuting states.** For strictly positive spectra
`p, q > 0`, the diagonal weight `P = diag(√(qᵢ/pᵢ))` attains the lower bound:
`tr(ρ P) tr(σ P⁻¹) = F(ρ, σ)²`. Indeed `pᵢ √(qᵢ/pᵢ) = √(pᵢqᵢ) = qᵢ / √(qᵢ/pᵢ)`, so both
traces equal `∑ᵢ √(pᵢqᵢ) = F`. -/
theorem albertiProduct_diagonal_minimizer_eq_fidelity_sq {n : Type*} [Fintype n]
    [DecidableEq n] (p q : n → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    albertiProduct (diagonal p) (diagonal q)
        (diagonal (fun i => Real.sqrt (q i / p i)))
      = matrixFidelity (diagonal p) (diagonal q) ^ 2 := by
  set w : n → ℝ := fun i => Real.sqrt (q i / p i) with hw_def
  have hw : ∀ i, 0 < w i := fun i => Real.sqrt_pos.mpr (div_pos (hq i) (hp i))
  have hPinv : (diagonal w)⁻¹ = diagonal (fun i => (w i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (ne_of_gt (hw i))
  have hpw : ∀ i, p i * w i = Real.sqrt (p i * q i) := by
    intro i
    have hsq : (p i * w i) ^ 2 = p i * q i := by
      rw [hw_def, mul_pow, Real.sq_sqrt (div_nonneg (hq i).le (hp i).le)]
      field_simp
    rw [← hsq, Real.sqrt_sq (mul_nonneg (hp i).le (hw i).le)]
  have hqw : ∀ i, q i * (w i)⁻¹ = Real.sqrt (p i * q i) := by
    intro i
    have hsq : (q i * (w i)⁻¹) ^ 2 = p i * q i := by
      rw [hw_def, mul_pow, inv_pow, Real.sq_sqrt (div_nonneg (hq i).le (hp i).le)]
      rw [inv_div]; field_simp
    rw [← hsq, Real.sqrt_sq (mul_nonneg (hq i).le (inv_nonneg.mpr (hw i).le))]
  have hAP : albertiProduct (diagonal p) (diagonal q) (diagonal w)
      = (∑ i, p i * w i) * (∑ i, q i * (w i)⁻¹) := by
    unfold albertiProduct
    rw [trace_diagonal_mul, trace_diagonal_mul, hPinv]
    simp only [Matrix.diagonal_apply_eq]
  rw [hAP, Finset.sum_congr rfl (fun i _ => hpw i),
    Finset.sum_congr rfl (fun i _ => hqw i),
    matrixFidelity_diagonal p q (fun i => (hp i).le) (fun i => (hq i).le)]
  ring

/-- **Alberti's theorem for commuting states (the corrected `(9.145)`).** For commuting
density matrices `ρ = diag(p)`, `σ = diag(q)` with strictly positive spectra, the squared
fidelity `F(ρ, σ)²` is the *least* value of the Alberti functional `P ↦ tr(ρ P) tr(σ P⁻¹)`
over all invertible positive `P` — attained at `P = diag(√(qᵢ/pᵢ))`. This is the genuine
identity that N&C's `(9.145)` garbles: the right-hand side is `F²`, not `F`. -/
theorem isLeast_albertiProduct_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (p q : n → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    IsLeast
      {y | ∃ P : Matrix n n ℝ, P.PosDef ∧ albertiProduct (diagonal p) (diagonal q) P = y}
      (matrixFidelity (diagonal p) (diagonal q) ^ 2) := by
  constructor
  · exact ⟨diagonal (fun i => Real.sqrt (q i / p i)),
      Matrix.PosDef.diagonal (fun i => Real.sqrt_pos.mpr (div_pos (hq i) (hp i))),
      albertiProduct_diagonal_minimizer_eq_fidelity_sq p q hp hq⟩
  · rintro y ⟨P, hP, rfl⟩
    exact albertiProduct_diagonal_ge_fidelity_sq p q
      (fun i => (hp i).le) (fun i => (hq i).le) P hP

/-! ### The concrete qubit counterexample refuting N&C `(9.145)` -/

/-- The eigenvalue vector of the first density matrix, `ρ = diag(9/10, 1/10)`. -/
noncomputable def rhoDiagVec : Fin 2 → ℝ := ![9 / 10, 1 / 10]

/-- The eigenvalue vector of the second density matrix, `σ = diag(1/10, 9/10)`. -/
noncomputable def sigmaDiagVec : Fin 2 → ℝ := ![1 / 10, 9 / 10]

/-- The witnessing positive weight vector, `P = diag(1/9, 1)`. -/
noncomputable def weightVec : Fin 2 → ℝ := ![1 / 9, 1]

/-- First density matrix of the counterexample, `ρ = diag(9/10, 1/10)`. -/
noncomputable def rhoEx : Matrix (Fin 2) (Fin 2) ℝ := diagonal rhoDiagVec

/-- Second density matrix of the counterexample, `σ = diag(1/10, 9/10)`. -/
noncomputable def sigmaEx : Matrix (Fin 2) (Fin 2) ℝ := diagonal sigmaDiagVec

/-- The witnessing invertible positive matrix `P = diag(1/9, 1)`. -/
noncomputable def weightEx : Matrix (Fin 2) (Fin 2) ℝ := diagonal weightVec

/-- The inverse of the weight matrix is `P⁻¹ = diag(9, 1)`, proved by exhibiting
the two-sided inverse. -/
theorem weightEx_inv : weightEx⁻¹ = diagonal ![(9 : ℝ), 1] := by
  apply Matrix.inv_eq_right_inv
  rw [weightEx, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [weightVec]

/-- The witness `P = diag(1/9, 1)` is **positive definite** — a positive diagonal
matrix — hence an admissible `P` in N&C `(9.145)`'s index set of *invertible
positive* matrices. This membership is load-bearing: only because `weightEx` lies
in the infimum's domain does `tr(ρ P) tr(σ P⁻¹) = 9/25 < 3/5` force the infimum
below `F(ρ, σ)`. -/
theorem weightEx_posDef : weightEx.PosDef := by
  rw [weightEx]
  exact Matrix.PosDef.diagonal (fun i => by fin_cases i <;> norm_num [weightVec])

/-- **The fidelity of the counterexample states is `3/5`.** Via
`matrixFidelity_diagonal`, `F(ρ, σ) = √(9/100) + √(9/100) = 3/10 + 3/10 = 3/5`. -/
theorem matrixFidelity_qubitDiagExample : matrixFidelity rhoEx sigmaEx = 3 / 5 := by
  rw [rhoEx, sigmaEx,
    matrixFidelity_diagonal rhoDiagVec sigmaDiagVec
      (fun i => by fin_cases i <;> norm_num [rhoDiagVec])
      (fun i => by fin_cases i <;> norm_num [sigmaDiagVec])]
  rw [Fin.sum_univ_two, rhoDiagVec, sigmaDiagVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (9 / 10 * (1 / 10) : ℝ) = (3 / 10) ^ 2 by norm_num,
    show (1 / 10 * (9 / 10) : ℝ) = (3 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **The Alberti functional at the witness `P` is `9/25`.**
`tr(ρ P) = 1/10 + 1/10 = 1/5` and `tr(σ P⁻¹) = 9/10 + 9/10 = 9/5`, so the product
is `9/25`. -/
theorem albertiProduct_qubitDiagExample :
    albertiProduct rhoEx sigmaEx weightEx = 9 / 25 := by
  unfold albertiProduct
  rw [weightEx_inv, rhoEx, sigmaEx, weightEx, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.trace_diagonal,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rhoDiagVec, sigmaDiagVec, weightVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The witnessed value `9/25` is exactly `F(ρ, σ)² = (3/5)²`, i.e. the Alberti
minimum — showing N&C `(9.145)` is off precisely by a square. -/
theorem albertiProduct_qubitDiagExample_eq_fidelity_sq :
    albertiProduct rhoEx sigmaEx weightEx = (matrixFidelity rhoEx sigmaEx) ^ 2 := by
  rw [albertiProduct_qubitDiagExample, matrixFidelity_qubitDiagExample]
  norm_num

/-- The strict inequality witnessing the failure: the Alberti functional at `P`
is strictly below the fidelity, `9/25 < 3/5`. -/
theorem albertiProduct_qubitDiagExample_lt_fidelity :
    albertiProduct rhoEx sigmaEx weightEx < matrixFidelity rhoEx sigmaEx := by
  rw [albertiProduct_qubitDiagExample, matrixFidelity_qubitDiagExample]
  norm_num

/-- **An admissible witness beats the fidelity.** There is a *positive definite*
(hence invertible positive, so admissible in N&C `(9.145)`) matrix `P` — namely
`P = diag(1/9, 1)` — with `tr(ρ P) tr(σ P⁻¹) = 9/25 < 3/5 = F(ρ, σ)`. This is the
witness that pulls the infimum strictly below `F`. -/
theorem exists_posDef_albertiProduct_lt_fidelity :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧
      albertiProduct rhoEx sigmaEx P < matrixFidelity rhoEx sigmaEx :=
  ⟨weightEx, weightEx_posDef, albertiProduct_qubitDiagExample_lt_fidelity⟩

/-- **Refutation of Nielsen & Chuang `(9.145)`.** If the fidelity equalled the
infimum `inf_P tr(ρ P) tr(σ P⁻¹)` over invertible positive `P`, then in particular
`F(ρ, σ)` would be a *lower bound* of `P ↦ tr(ρ P) tr(σ P⁻¹)` **on that index
set**. It is not: the positive definite witness `P = diag(1/9, 1)`
(`weightEx_posDef`) gives value `9/25 < 3/5 = F(ρ, σ)`. Hence the printed identity
`(9.145)` is false; the correct statement (Alberti's theorem) has `F(ρ, σ)²` on
the left.

The quantifier is restricted to `P.PosDef` — N&C's *invertible positive* index
set — precisely so the refutation engages `(9.145)`'s actual domain: the
unrestricted `¬ ∀ P, F ≤ g P` would be vacuously discharged by junk such as
`P = 0` (`0⁻¹ = 0`, so `g(0) = 0 < F`), which is outside the infimum's range. -/
theorem fidelity_not_lower_bound_of_albertiProduct :
    ¬ ∀ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef →
      matrixFidelity rhoEx sigmaEx ≤ albertiProduct rhoEx sigmaEx P := by
  intro h
  exact absurd (h weightEx weightEx_posDef)
    (not_le.mpr albertiProduct_qubitDiagExample_lt_fidelity)

/-- **The Alberti infimum for the counterexample states is exactly `F² = 9/25`.** Applying
`isLeast_albertiProduct_diagonal` to `ρ = diag(9/10, 1/10)`, `σ = diag(1/10, 9/10)` pins the
greatest lower bound of `P ↦ tr(ρ P) tr(σ P⁻¹)` over *all* invertible positive `P` at
`F(ρ, σ)² = (3/5)² = 9/25`. Together with `matrixFidelity_qubitDiagExample`
(`F = 3/5`) this makes the "off by a square" concrete: the true infimum `9/25` sits strictly
below the value `3/5` that the printed `(9.145)` claims for it — the sharp, quantitative
form of the refutation `fidelity_not_lower_bound_of_albertiProduct`. -/
theorem isLeast_albertiProduct_qubitDiagExample :
    IsLeast
      {y | ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧ albertiProduct rhoEx sigmaEx P = y}
      (matrixFidelity rhoEx sigmaEx ^ 2) :=
  isLeast_albertiProduct_diagonal rhoDiagVec sigmaDiagVec
    (fun i => by fin_cases i <;> norm_num [rhoDiagVec])
    (fun i => by fin_cases i <;> norm_num [sigmaDiagVec])

end AxQM.Concrete
