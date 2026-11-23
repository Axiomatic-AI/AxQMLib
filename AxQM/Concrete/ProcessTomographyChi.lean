/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Data.Matrix.Block
import ToMathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete: single-qubit process tomography, the amplitude-damping χ matrix (N&C Ex 8.35)

This file treats explicit `2 × 2` / `4 × 4` complex
matrices and one matrix identity. It formalizes the single-qubit quantum-process-tomography
computation of Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Box 8.5**
(p. 393) and the worked **Exercise 8.35** (p. 394).

## Box 8.5 — the χ matrix by matrix multiplication

Fixing the operator basis `Ẽ₀ = I`, `Ẽ₁ = X`, `Ẽ₂ = -iY`, `Ẽ₃ = Z` (eqs. 8.169–8.172), the process
matrix `χ` of an arbitrary single-qubit operation `E` (`E(ρ) = ∑ₘₙ χₘₙ Ẽₘ ρ Ẽₙ†`) can be read off
four measured output density matrices `ρ'₁,…,ρ'₄` by a single block-matrix product (eqs. 8.178–9)

`χ = Λ [[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]] Λ`,   where   `Λ = ½ [[I, X], [X, -I]]`.

Here `[[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]]` and `Λ` are `4 × 4` matrices written in `2 × 2` blocks (`ρ'ⱼ` and
`I`, `X` are `2 × 2`). We model the `4 × 4` block index as `Fin 2 ⊕ Fin 2` and assemble the blocks
with `Matrix.fromBlocks`, matching N&C's block presentation literally; the product then unfolds via
`Matrix.fromBlocks_multiply`.

* `processTomographyΛ` — the fixed matrix `Λ = ½[[I, X], [X, -I]]` (eq. 8.178).
* `singleQubitProcessChi ρ' = Λ ρ' Λ` — the Box 8.5 reconstruction map (eq. 8.179), taking the
  `4 × 4` block of measured matrices to the process matrix `χ`.

## Exercise 8.35 — the amplitude-damping example

A one-qubit black box `E₁` of unknown dynamics is measured (following eqs. 8.173–8.176) to give
(eqs. 8.182–8.185)

`ρ'₁ = [[1,0],[0,0]]`,  `ρ'₂ = [[0,√(1-γ)],[0,0]]`,  `ρ'₃ = [[0,0],[√(1-γ),0]]`,
`ρ'₄ = [[γ,0],[0,1-γ]]`,

with `γ` a numerical parameter: the ground state `|0⟩` is left invariant, the excited state `|1⟩`
partially decays to the ground state, and superposition states are damped — the signature of
**amplitude damping** (N&C §8.3.5). Feeding these into the Box 8.5 formula determines the χ matrix:

`χ = ¼ [[(1+√(1-γ))², 0, 0, γ], [0, γ, -γ, 0], [0, -γ, γ, 0], [γ, 0, 0, (1-√(1-γ))²]]`.

* `ampDampMeasuredBlock γ` — the block `[[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]]` of the four measured matrices.
* `ampDampChiMatrix γ` — the resulting `χ` above (the answer to "determine the χ matrix").
* `ampDampChiMatrix_eq` — **the determination**: `singleQubitProcessChi (ampDampMeasuredBlock γ) =
  ampDampChiMatrix γ`, i.e. the Box 8.5 product `Λ ρ' Λ` equals the stated `χ` (for `γ ≤ 1`).
* `ampDampChiMatrix_trace` — `tr χ = 1`, corroborating that the determined `χ` is a legitimate,
  correctly normalized process matrix of a trace-preserving operation.

The hypothesis `γ ≤ 1` is used only to turn `(√(1-γ))² = 1-γ` (`Real.sq_sqrt`); it is weaker than
the physical amplitude-damping range `0 ≤ γ ≤ 1`, so the statement is not specialized beyond N&C. In
the diagonal corners `(1±√(1-γ))² = 2 ± 2√(1-γ) - γ`; the off-diagonal amplitudes `√(1-γ)` never get
squared in the product `Λ ρ' Λ`, so `hγ` is genuinely needed only to present the answer in N&C's
`(1±√(1-γ))²` form.

## Related files

The χ matrix, `Λ`, and the measured density matrices are concrete `4 × 4` matrices. Compare the
channel computations of Exercise 8.29 (`AxQM/Concrete/ChannelUnitality.lean`) and Exercise 8.22
(`AxQM/Concrete/AmplitudeDampingDensityMatrix.lean`). The statement of Exercise 8.35 is in
`AxQM/NC/Ch8/Exercise8_35.lean`.

The reusable `processTomographyΛ` and `singleQubitProcessChi` capture Box 8.5's general single-qubit
procedure and are the natural building blocks for the two-qubit extension (Exercise 8.34, `Λ₂ =
Λ ⊗ Λ`).
-/

open Matrix Complex

namespace AxQM.Concrete

/-- The fixed single-qubit process-tomography matrix `Λ = ½[[I, X], [X, -I]]` of Nielsen & Chuang,
Box 8.5 (eq. 8.178): a `4 × 4` matrix written in `2 × 2` blocks, with the identity and Pauli `X` in
the corners. It lets the process matrix be recovered by the block product `χ = Λ ρ' Λ`
(`singleQubitProcessChi`); its Kronecker square `Λ ⊗ Λ` is the two-qubit tomography matrix `Λ₂` of
Exercise 8.34. The `4 × 4` block index is modelled as `Fin 2 ⊕ Fin 2`. -/
noncomputable def processTomographyΛ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks ((1 / 2 : ℂ) • 1) ((1 / 2 : ℂ) • pauliX) ((1 / 2 : ℂ) • pauliX)
    ((1 / 2 : ℂ) • (-1))

/-- The Box 8.5 process-matrix reconstruction (eq. 8.179): from the `4 × 4` block `ρ'` of measured
output density matrices, the χ matrix of a single-qubit operation is `χ = Λ ρ' Λ`, with
`Λ = processTomographyΛ`. -/
noncomputable def singleQubitProcessChi
    (rho' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  processTomographyΛ * rho' * processTomographyΛ

/-- The `4 × 4` block `ρ' = [[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]]` of the four density matrices measured from the
amplitude-damping black box of Nielsen & Chuang, Exercise 8.35 (eqs. 8.182–8.185): `ρ'₁ = [[1,0],
[0,0]]` (`|0⟩` is left invariant), `ρ'₂ = [[0,√(1-γ)],[0,0]]` and `ρ'₃ = [[0,0],[√(1-γ),0]]`
(superpositions are damped), `ρ'₄ = [[γ,0],[0,1-γ]]` (`|1⟩` partially decays to `|0⟩`). -/
noncomputable def ampDampMeasuredBlock (γ : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    !![1, 0; 0, 0]
    !![0, (Real.sqrt (1 - γ) : ℂ); 0, 0]
    !![0, 0; (Real.sqrt (1 - γ) : ℂ), 0]
    !![(γ : ℂ), 0; 0, ((1 - γ : ℝ) : ℂ)]

/-- The χ matrix determined for the amplitude-damping black box of Nielsen & Chuang, Exercise 8.35,
written as a `4 × 4` matrix in `2 × 2` blocks:
`χ = ¼[[(1+√(1-γ))², 0, 0, γ], [0, γ, -γ, 0], [0, -γ, γ, 0], [γ, 0, 0, (1-√(1-γ))²]]`.
This is `ampDampChiMatrix_eq`'s value of the Box 8.5 product `Λ ρ' Λ`. -/
noncomputable def ampDampChiMatrix (γ : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  (1 / 4 : ℂ) • Matrix.fromBlocks
    !![(1 + (Real.sqrt (1 - γ) : ℂ)) ^ 2, 0; 0, (γ : ℂ)]
    !![0, (γ : ℂ); -(γ : ℂ), 0]
    !![0, -(γ : ℂ); (γ : ℂ), 0]
    !![(γ : ℂ), 0; 0, (1 - (Real.sqrt (1 - γ) : ℂ)) ^ 2]

/-- For `γ ≤ 1`, the complex square of the real amplitude `√(1-γ)` collapses to `1 - γ`:
`(√(1-γ) : ℂ)² = 1 - γ`. The shared square-root fact behind both the χ determination
(`ampDampChiMatrix_eq`) and its unit trace (`ampDampChiMatrix_trace`). -/
theorem ofReal_sq_sqrt_one_sub (γ : ℝ) (hγ : γ ≤ 1) :
    (Real.sqrt (1 - γ) : ℂ) ^ 2 = (1 : ℂ) - (γ : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring

/-- **Nielsen & Chuang, Exercise 8.35 (determine the χ matrix).** Applying the Box 8.5 process
formula `χ = Λ ρ' Λ` to the four measured density matrices of the amplitude-damping black box yields
the stated χ matrix: `singleQubitProcessChi (ampDampMeasuredBlock γ) = ampDampChiMatrix γ`, for
`γ ≤ 1`. The proof expands the two block products with `Matrix.fromBlocks_multiply` and computes
each `2 × 2` block, using `(√(1-γ))² = 1-γ` to write the diagonal corners as `(1±√(1-γ))²`. -/
theorem ampDampChiMatrix_eq (γ : ℝ) (hγ : γ ≤ 1) :
    singleQubitProcessChi (ampDampMeasuredBlock γ) = ampDampChiMatrix γ := by
  have hs := ofReal_sq_sqrt_one_sub γ hγ
  simp only [singleQubitProcessChi, processTomographyΛ, ampDampMeasuredBlock, ampDampChiMatrix,
    Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_smul]
  congr 1 <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauliX, Matrix.add_apply, Matrix.smul_apply] <;> ring_nf)
  all_goals linear_combination (-1 / 4 : ℂ) * hs

/-- The determined amplitude-damping χ matrix has unit trace, `tr χ = 1` (for `γ ≤ 1`): the
diagonal corners `(1±√(1-γ))²` sum to `2 + 2(1-γ)` and, with the two `γ`'s, give `4`, times the
`¼` normalization. This corroborates that `ampDampChiMatrix` is the process matrix of a genuine
trace-preserving quantum operation (N&C's normalization has `tr χ = 1` for such operations). -/
theorem ampDampChiMatrix_trace (γ : ℝ) (hγ : γ ≤ 1) :
    (ampDampChiMatrix γ).trace = 1 := by
  have hs := ofReal_sq_sqrt_one_sub γ hγ
  rw [ampDampChiMatrix, Matrix.trace_smul, smul_eq_mul]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring_nf; rw [hs]; ring

end AxQM.Concrete
