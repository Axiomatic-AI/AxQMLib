/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingDensityMatrix

/-!
# Nielsen & Chuang, Exercise 8.22 (amplitude damping of a single-qubit density matrix)

*(N&C p. 381.)*

Show amplitude damping of general single-qubit ρ gives the stated damped density matrix.

## The computation

The **amplitude-damping channel** `E_AD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (N&C eqs. 8.107–8.108) has
operation elements `E₀ = diag(1, √(1-γ))` and `E₁ = √γ |0⟩⟨1|`. Applying it to a general qubit
operator `ρ` and reading off the computational-basis matrix gives, entry by entry,

`⟨0|E_AD(ρ)|0⟩ = a + γc`,   `⟨0|E_AD(ρ)|1⟩ = √(1-γ) b`,
`⟨1|E_AD(ρ)|0⟩ = √(1-γ) b*`,   `⟨1|E_AD(ρ)|1⟩ = (1-γ) c`.

For a genuine density matrix `tr ρ = a + c = 1`, so `c = 1 - a` and the `(0,0)` entry `a + γc`
becomes N&C's `1 - (1-γ)(1-a)` — exactly eq. 8.112. The identity in fact holds for *every* operator
`ρ` (the channel is linear), so no positivity/Hermiticity is needed; only `0 ≤ γ ≤ 1`, N&C's
physical range for the damping probability, enters, via the squares `(√γ)² = γ`, `(√(1-γ))² = 1-γ`.

## Scope

The formal content of Exercise 8.22 is pure linear algebra about a `2 × 2` operator and its matrix
(`LinearMap`, `OrthonormalBasis`, `inner`, `LinearMap.toMatrixOrthonormal`). Compare Exercises 8.16
and 8.17. The channel and its operation elements are those of the amplitude-damping channel
(`AxQM/Concrete/AmplitudeDampingChannel.lean`).

## The formalisation

The formalisation is in `AxQM/Concrete/AmplitudeDampingDensityMatrix.lean`:

* `AxQM/Concrete/AmplitudeDampingDensityMatrix.lean`:
  * `AxQM.Concrete.inner_ampDampChannel` — the structural matrix-element decomposition
    `⟨x, E_AD(ρ) y⟩ = ⟨E₀ x, ρ (E₀ y)⟩ + ⟨E₁† x, ρ (E₁† y)⟩`.
  * `AxQM.Concrete.ampDampKrausZero_apply_basisZero`, `…_basisOne`,
    `AxQM.Concrete.adjoint_ampDampKrausOne_apply_basisZero`, `…_basisOne` — the action of
    `E₀` and the raising adjoint `E₁†` on the computational basis.
  * `AxQM.Concrete.ampDampChannel_inner_zero_zero`, `…_zero_one`, `…_one_zero`,
    `…_one_one` — the four matrix entries `a + γc`, `√(1-γ) b`, `√(1-γ) b*`, `(1-γ) c`.
  * `AxQM.Concrete.ampDampChannel_toMatrixOrthonormal` — **the exercise, general form**:
    the computational-basis matrix of `E_AD(ρ)` for any operator `ρ` (`0 ≤ γ ≤ 1`).
  * `AxQM.Concrete.ampDampChannel_toMatrixOrthonormal_of_trace_one` — **eq. 8.112**:
    the same matrix with the `(0,0)` entry in N&C's `1 - (1-γ)(1-a)` form, for a trace-one state.

See the module docstring of `AxQM/Concrete/AmplitudeDampingDensityMatrix.lean` for the full
argument.
-/
