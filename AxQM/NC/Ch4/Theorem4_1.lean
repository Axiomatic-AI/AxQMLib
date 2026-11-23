/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecomposition

/-!
# Nielsen & Chuang, Theorem 4.1 (Z–Y decomposition for a single qubit)

Z-Y decomposition: any single-qubit unitary U=e^{i a}R_z(b)R_y(g)R_z(d).

The statement is a fact of `2 × 2` complex linear algebra: an arbitrary matrix
`U ∈ Matrix.unitaryGroup (Fin 2) ℂ` (N&C's definition of a single-qubit gate — a norm-preserving
`2 × 2` matrix, `Uᴴ U = I`) factors as a phase times a product of the concrete rotation matrices
`R_z`, `R_y`.

## The formalisation

The Z–Y decomposition lives in `AxQM/Concrete/RotationDecomposition.lean`, built on the
rotation matrices of `AxQM/Concrete/Rotation.lean`:

* `AxQM.Concrete.rotY` / `AxQM.Concrete.rotZ` (in `Concrete/Rotation.lean`) —
  the single-qubit rotation matrices `R_y(θ)`, `R_z(θ)` (N&C eqs. 4.5, 4.6), defined as
  `R_n̂(θ) ≡ exp(-iθ(n·σ)/2)` at the coordinate axes, with explicit-matrix forms `rotY_eq`,
  `rotZ_eq`. These are shared infrastructure for all of Chapter 4's single-qubit decompositions.
* `AxQM.Concrete.rotZ_mul_rotY_mul_rotZ` — the closed form of the product
  `R_z(β) R_y(γ) R_z(δ)` as the single matrix of N&C eq. (4.12) (up to the global phase); the
  reusable computational core of the decomposition.
* `AxQM.Concrete.exists_zy_decomposition` — **Theorem 4.1 itself**: for
  `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` there exist real `α, β, γ, δ` with
  `U = e^{iα} • (R_z(β) R_y(γ) R_z(δ))`.

The theorem is stated for *all* of `U(2)` (no determinant or dimension is fixed), matching N&C's
generality. The angles are read off the entries of `U`: `α = arg(det U)/2`,
`β = arg U₁₀ - arg U₀₀`, `γ = 2 arccos ‖U₀₀‖`, `δ = arg(det U) - arg U₀₀ - arg U₁₀`; unitarity
forces `‖U₀₀‖² + ‖U₁₀‖² = 1`, `U₁₁ = det U · conj U₀₀`, `U₀₁ = -det U · conj U₁₀`, and each entry
then matches the closed form via the polar decomposition `z = ‖z‖ e^{i arg z}`.

The rotation matrices `rotY`/`rotZ` and `rotZ_mul_rotY_mul_rotZ` are shared infrastructure for the
rest of Chapter 4 — Corollary 4.2 (the `A X B X C` decomposition of controlled operations) and
Exercises 4.3, 4.4, 4.14 — which build on them.
-/
