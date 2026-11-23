/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliFunctionalCalculus

/-!
# Nielsen & Chuang, Problem 2.1 (Functions of the Pauli matrices)

Functions of the Pauli matrices: f(theta n.sigma) = ((f(theta)+f(-theta))/2)I +
((f(theta)-f(-theta))/2) n.sigma.

The formalisation is in `AxQM/Concrete/PauliFunctionalCalculus.lean` (which
builds on the `n·σ` algebra of `AxQM/Concrete/Pauli.lean`):

* `AxQM.Concrete.functionOfHermitian` — the spectral functional calculus
  `f(A) = U · diagonal (f ∘ eigenvalues) · U†` of a Hermitian matrix for a
  **complex-valued** `f : ℂ → ℂ`. This is the `ℂ`-valued analogue of Mathlib's
  `Matrix.IsHermitian.cfc` (which is `ℝ → ℝ`); the complex codomain is required to
  capture N&C's "any function from complex numbers to complex numbers" (e.g. the
  `exp(i θ n·σ)` of Exercise 2.35), and matches N&C's own definition
  `f(A) = Σₐ f(a) |a⟩⟨a|` (Box 2.2).
* `AxQM.Concrete.functionOfHermitian_id` — `functionOfHermitian hA id = A`
  (a sanity/faithfulness lemma: `functionOfHermitian` is a genuine functional calculus).
* `AxQM.Concrete.pauliDot_smul_isHermitian` — `θ • (n·σ)` is Hermitian.
* `AxQM.Concrete.pauliDot_smul_eigenvalues_sq` — every eigenvalue `λ` of
  `θ • (n·σ)` satisfies `λ² = θ²` (i.e. `λ ∈ {θ, -θ}`), the spectral input to (2.231).
* `AxQM.Concrete.functionOfPauliDot_decomposition` — the exercise's claim
  `f(θ n·σ) = ((f(θ)+f(-θ))/2) I + ((f(θ)-f(-θ))/2) n·σ`.
-/
