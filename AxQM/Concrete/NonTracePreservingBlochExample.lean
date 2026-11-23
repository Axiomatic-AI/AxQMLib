/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.PauliOuterProduct

/-!
# Concrete: a non-trace-preserving qubit operation with no affine Bloch-sphere picture

This file supplies the mathematical content behind **Nielsen & Chuang, Exercise 8.16 (p. 378)**.

## Context in N&C

For a *trace-preserving* single-qubit quantum operation `E`, N&C (§8.3.2, eq. 8.89) shows the
induced action on the Bloch representation `ρ = ½(I + r·σ)` is an **affine map**

`r ↦ M r + c`   (`M` a real `3 × 3` matrix, `c ∈ ℝ³`),

read — via the polar decomposition `M = O S` (Exercise 8.12) — as a *deformation* of the Bloch
sphere along the principal axes of the symmetric `S`, followed by a *proper rotation* `O`, followed
by a *displacement* `c`. This "graphical method" is the source of Figures 8.8–8.11.

Find a non-trace-preserving operation not expressible as Bloch deformation+rotation+displacement.

## The example, and why it defeats the affine picture

The affine map `r ↦ M r + c` is by construction a self-map of the family of density matrices
`ρ = ½(I + r·σ)`: every such `ρ` has **trace one**, so the description `E(ρ_r) = ρ_{M r + c}`
forces `E` to preserve the trace. (Indeed N&C's derivation of `c` uses the completeness relation
`∑ᵢ Eᵢ† Eᵢ = I`, i.e. trace preservation.) A genuinely *non-trace-preserving* operation therefore
cannot fit the picture: its outputs leave the trace-one slice and are no longer Bloch vectors.

The explicit witness is the single-Kraus operation

`E(ρ) = P₀ ρ P₀†`,   `P₀ = |0⟩⟨0|`   (the canonical computational-basis projector `ketBra 0 0`),

i.e. a projective measurement of the qubit in the computational basis, keeping only outcome `0`.
It is a bona fide quantum operation — an operator sum with one operation element, hence completely
positive and positivity-preserving (`projZeroOp_posSemidef`) — but it is *not* trace-preserving:
`P₀† P₀ = P₀ ≠ I` (`projZero_adjoint_mul_self_ne_one`), and concretely `tr E(ρ_r) = ½(1 + r₂)`
(`projZeroOp_blochMatrix_trace`, the outcome-`0` probability `⟨0|ρ|0⟩`), which is `≠ 1` in general
(`projZeroOp_not_tracePreserving`). Since every Bloch matrix has trace one, no affine `(M, c)` can
satisfy `E(ρ_r) = ρ_{M r + c}` for all physical `r` (`projZeroOp_not_blochAffine`): the state
`ρ = |1⟩⟨1|` (Bloch vector `r = (0, 0, -1)`) is annihilated, `E(ρ) = 0`, with trace `0 ≠ 1`.

## Scope

Every statement is about raw matrix data (`Matrix`, `Concrete.blochMatrix`, `Matrix.trace`,
`Matrix.PosSemidef`). Compare the operator-sum exercises 8.4 and 8.12. The statement of
Exercise 8.16 is in `AxQM/NC/Ch8/Exercise8_16.lean`.

## Design notes

* **The operation element is the canonical projector.** `projZero` is defined as
  `Concrete.ketBra 0 0` (`Concrete.PauliOuterProduct`, N&C Exercise 2.9), the shared `|0⟩⟨0|` —
  reused rather than re-spelled as a raw `!![…]` literal, matching the idiom of the sibling
  operator-sum items (`SpinFlipOperatorSum`, `ControlledFlipOperatorSum`). Its entries are the
  `ketBra_apply` value `δ`, which is what the elementary proofs below reduce through.
* **The operation as an operator sum.** `projZeroOp` is the conjugation `A ↦ P₀ A P₀†`, which *is*
  N&C's operator-sum form (§8.2.3) with the single operation element `P₀`; this is the faithful
  certificate that it is a quantum operation. Complete positivity of a one-element operator sum is
  automatic (the operator-sum representation being N&C Theorem 8.1's characterization of quantum
  operations); the physically essential positivity-preservation is recorded as
  `projZeroOp_posSemidef`, via Mathlib's `Matrix.PosSemidef.mul_mul_conjTranspose_same`.
* **Non-trace-preservation, twice.** `projZero_adjoint_mul_self_ne_one` is the operator-sum-level
  certificate (`∑ Eᵢ† Eᵢ = P₀ ≠ I`, N&C's completeness relation failing);
  `projZeroOp_not_tracePreserving` is its physical face (`tr E(ρ) = tr ρ` fails for some state).
  Both are the two readings of "non-trace-preserving".
* **Faithfulness of the statement.** `projZeroOp_not_blochAffine` negates the existence of *any*
  affine map `(M, c)` — and since every real `3 × 3` `M` factors as `O S` (polar decomposition),
  the affine maps are exactly N&C's "deformation + rotation + displacement", so this is precisely
  the exercise's claim, neither more nor less. The universally-quantified `r` is restricted to the
  physical Bloch ball `‖r‖² ≤ 1` (the states the picture is about), the honest reading; the witness
  `r = (0, 0, -1)` is a pure state on the ball, so the impossibility already holds over physical
  states.
-/

namespace AxQM.Concrete

open Matrix
open scoped ComplexOrder

/-- The computational-basis projector `P₀ = |0⟩⟨0| = !![1, 0; 0, 0]`, the single operation element
of the non-trace-preserving qubit operation of Nielsen & Chuang, Exercise 8.16. This is the shared
`Concrete.ketBra 0 0` of `Concrete.PauliOuterProduct` (N&C Exercise 2.9), reused here rather than
re-spelled as a raw matrix literal; recall `ketBra 0 0 = ½(pauliI + pauliZ)`
(`pauliI_eq_ketBra`/`pauliZ_eq_ketBra`), i.e. `P₀ = ½(I + Z)`. -/
noncomputable def projZero : Matrix (Fin 2) (Fin 2) ℂ := ketBra 0 0

/-- The **quantum operation** `E(ρ) = P₀ ρ P₀†` with the single operation element `P₀ = |0⟩⟨0|`
(`projZero`): the operator-sum representation with one Kraus operator, realising a
computational-basis projective measurement post-selected on the outcome `0`. Non-trace-preserving
(Nielsen & Chuang, Exercise 8.16). -/
noncomputable def projZeroOp (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  projZero * A * projZeroᴴ

/-- `P₀† = P₀`: the projector `|0⟩⟨0|` is self-adjoint (real diagonal, zero off-diagonal). -/
@[simp] theorem projZero_conjTranspose : projZeroᴴ = projZero := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [projZero, ketBra_apply, Matrix.conjTranspose_apply]

/-- **Non-trace-preservation, operator-sum form.** The single operation element `P₀` fails N&C's
completeness relation `∑ᵢ Eᵢ† Eᵢ = I`: `P₀† P₀ = P₀ ≠ I` (the `(1,1)` entry is `0`, not `1`). This
is exactly what makes `projZeroOp` a *non-trace-preserving* quantum operation. -/
theorem projZero_adjoint_mul_self_ne_one : projZeroᴴ * projZero ≠ 1 := by
  rw [projZero_conjTranspose]
  intro h
  have := congrFun (congrFun h 1) 1
  simp [projZero, Matrix.mul_apply, ketBra_apply] at this

/-- **`projZeroOp` is positivity-preserving:** `E(A) = P₀ A P₀†` is positive semidefinite whenever
`A` is. This is the physically essential half of "`E` is a quantum operation": it maps
(subnormalized) density matrices to (subnormalized) density matrices. Immediate from Mathlib's
Gram-conjugation lemma `Matrix.PosSemidef.mul_mul_conjTranspose_same`. (Full complete positivity is
automatic for a one-element operator sum.) -/
theorem projZeroOp_posSemidef {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) :
    (projZeroOp A).PosSemidef :=
  hA.mul_mul_conjTranspose_same projZero

/-- **The output trace is the outcome-`0` probability** `tr E(ρ_r) = ⟨0|ρ_r|0⟩ = ½(1 + r₂)`.
Computing `P₀ (½(I + r·σ)) P₀†` keeps only the `(0,0)` entry `½(1 + r₂)` of the Bloch matrix, so the
trace of the output is that entry. In particular the trace depends on `r` and is `< 1` unless
`r₂ = 1`, which is why `projZeroOp` is not trace-preserving. -/
theorem projZeroOp_blochMatrix_trace (r : Fin 3 → ℝ) :
    (projZeroOp (blochMatrix r)).trace = (2⁻¹ : ℂ) * (1 + (r 2 : ℂ)) := by
  rw [projZeroOp, projZero_conjTranspose, projZero, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ketBra_apply, blochMatrix_eq]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  norm_num

/-- **Non-trace-preservation, physical form.** `projZeroOp` does not preserve the trace: there is a
density matrix whose image has a different trace. Concretely `tr E(|1⟩⟨1|) = 0 ≠ 1 = tr |1⟩⟨1|`,
using the Bloch matrix of `r = (0, 0, -1)` (state `|1⟩⟨1|`) and `projZeroOp_blochMatrix_trace`. -/
theorem projZeroOp_not_tracePreserving :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℂ, (projZeroOp A).trace = A.trace := by
  intro h
  have := h (blochMatrix ![0, 0, -1])
  rw [projZeroOp_blochMatrix_trace, blochMatrix_trace] at this
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
  norm_num at this

/-- **Nielsen & Chuang, Exercise 8.16 (the answer).** The non-trace-preserving quantum operation
`E(ρ) = P₀ ρ P₀†` **cannot** be described as an affine map of the Bloch sphere — a deformation `S`,
followed by a rotation `O`, followed by a displacement `c` — i.e. there is **no** real `3 × 3`
matrix `M` and vector `c` with `E(ρ_r) = ρ_{M r + c}` for all Bloch vectors `r` of physical states
(`‖r‖² ≤ 1`). (Since every real `M` factors as `M = O S` by polar decomposition, ranging over all
affine `(M, c)` is exactly ranging over all deformation-rotation-displacement maps.)

Were such an `(M, c)` to exist, taking traces of `E(ρ_r) = ρ_{M r + c}` at the pure state
`r = (0, 0, -1)` (i.e. `|1⟩⟨1|`) would give `tr E(ρ_r) = ½(1 + r₂) = 0` on the left
(`projZeroOp_blochMatrix_trace`) but `tr ρ_{M r + c} = 1` on the right (`blochMatrix_trace`) — a
contradiction. The obstruction is exactly the failure of trace preservation. -/
theorem projZeroOp_not_blochAffine :
    ¬ ∃ (M : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ),
      ∀ r : Fin 3 → ℝ, r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1 →
        projZeroOp (blochMatrix r) = blochMatrix (M *ᵥ r + c) := by
  rintro ⟨M, c, h⟩
  have hr : (![0, 0, -1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, -1] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 0, -1] : Fin 3 → ℝ) 2 ^ 2 ≤ 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]; norm_num
  have heq := h ![0, 0, -1] hr
  have htr := congrArg Matrix.trace heq
  rw [projZeroOp_blochMatrix_trace, blochMatrix_trace] at htr
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at htr
  norm_num at htr

end AxQM.Concrete
