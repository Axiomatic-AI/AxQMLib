/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ProcessTomographyChi

/-!
# Nielsen & Chuang, Exercise 8.35 (Process tomography example)

*(N&C p. 394.)*

Determine χ matrix for a one-qubit black box from four measured density matrices (amplitude
damping).

## The computation

This is the worked example of the single-qubit process-tomography procedure of **Box 8.5**: with the
fixed operator basis `Ẽ₀ = I`, `Ẽ₁ = X`, `Ẽ₂ = -iY`, `Ẽ₃ = Z`, the process matrix is recovered from
the block of measured density matrices by `χ = Λ [[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]] Λ` with
`Λ = ½[[I, X], [X, -I]]` (eqs. 8.178–8.179). Substituting the four measured matrices gives the
amplitude-damping process matrix

`χ = ¼ [[(1+√(1-γ))², 0, 0, γ], [0, γ, -γ, 0], [0, -γ, γ, 0], [γ, 0, 0, (1-√(1-γ))²]]`.

## The formalisation

The formal content of Exercise 8.35 is a concrete matrix computation: the χ matrix, `Λ`, and the
measured density matrices are all `Matrix` data. Compare Exercise 8.22
(`AxQM/Concrete/AmplitudeDampingDensityMatrix.lean`) and Exercise 8.29
(`AxQM/Concrete/ChannelUnitality.lean`).

The formalisation is in `AxQM/Concrete/ProcessTomographyChi.lean`:


* `AxQM.Concrete.processTomographyΛ` — the Box 8.5 matrix `Λ = ½[[I, X], [X, -I]]`
  (eq. 8.178).
* `AxQM.Concrete.singleQubitProcessChi` — the Box 8.5 reconstruction `χ = Λ ρ' Λ`
  (eq. 8.179).
* `AxQM.Concrete.ampDampMeasuredBlock` — the block `[[ρ'₁, ρ'₂], [ρ'₃, ρ'₄]]` of the four
  measured density matrices (eqs. 8.182–8.185).
* `AxQM.Concrete.ampDampChiMatrix` — the determined χ matrix (the answer).
* `AxQM.Concrete.ampDampChiMatrix_eq` — **the determination**:
  `singleQubitProcessChi (ampDampMeasuredBlock γ) = ampDampChiMatrix γ`, i.e. `Λ ρ' Λ` equals the
  stated χ (for `γ ≤ 1`).
* `AxQM.Concrete.ampDampChiMatrix_trace` — `tr χ = 1`, corroborating that the determined χ
  is a correctly normalized process matrix of a trace-preserving operation.

See the module docstring of `AxQM/Concrete/ProcessTomographyChi.lean` for the full argument.
-/
