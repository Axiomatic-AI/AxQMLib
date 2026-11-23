/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import ToMathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.Basic
import ToMathlib.Algebra.BigOperators.Fin

/-!
# Concrete: the antisymmetric `SO(3)` generators and the Werner–Holevo operator sum

This file defines the three real
antisymmetric `3 × 3` generators

* `A₀ = E₀₁ − E₁₀`, `A₁ = E₀₂ − E₂₀`, `A₂ = E₁₂ − E₂₁`  (`wernerHolevoGen`)

— the basis of the Lie algebra `𝔰𝔬(3)` of `3 × 3` real antisymmetric matrices — and proves the
two algebraic facts that make them the Kraus data of the **Werner–Holevo qutrit channel**
`Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` (the Landau–Streater counterexample of Nielsen & Chuang, Problem 8.3):

* `wernerHolevoGen_conjTranspose` — each generator is antisymmetric, `Aₐᴴ = −Aₐ` (the entries are
  real, so the conjugate transpose is the transpose).
* `wernerHolevoGen_sum_conj` — the **operator-sum identity**
  `∑ₐ Aₐ ρ Aₐᴴ = tr(ρ)·I − ρᵀ` for every `3 × 3` complex matrix `ρ`. This is the Choi computation
  for the antisymmetric-subspace projector, written entrywise: with Kraus operators `Aₐ/√2` it
  gives the trace-preserving Werner–Holevo channel `½(tr(ρ)·I − ρᵀ)`.
* `wernerHolevoGen_conjTranspose_mul_self_sum` — the **completeness relation**
  `∑ₐ Aₐᴴ Aₐ = 2·I`, so the scaled family `Aₐ/√2` satisfies `∑ₐ (Aₐ/√2)ᴴ (Aₐ/√2) = I` and the
  channel is trace-preserving.

## Design notes

* The generators are given as explicit `!![…]` matrices, and every fact below is proved by
  reducing to entrywise computation (`Matrix.ext` + `Fin.sum_univ_three` + `simp`/`ring`), the
  same style as `Concrete/Pauli.lean`.
* `wernerHolevoGen_sum_conj` uses the plain transpose `ρᵀ` (`Matrix.transpose`), which is the
  correct target: the Choi matrix of `ρ ↦ tr(ρ)·I − ρᵀ` is `2·P_antisym ≥ 0`, so the map is
  completely positive; the sign is fixed by the sample check `Φ(E₀₀) = E₁₁ + E₂₂ = I − E₀₀`.
-/

namespace AxQM.Concrete

open Matrix

/-- The three real antisymmetric `3 × 3` generators `A₀ = E₀₁ − E₁₀`, `A₁ = E₀₂ − E₂₀`,
`A₂ = E₁₂ − E₂₁` — a basis of the Lie algebra `𝔰𝔬(3)`. Scaled by `1/√2` they are the Kraus
operators of the Werner–Holevo qutrit channel `Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` (Nielsen & Chuang,
Problem 8.3). -/
def wernerHolevoGen : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 1, 0; -1, 0, 0; 0, 0, 0]
  | 1 => !![0, 0, 1; 0, 0, 0; -1, 0, 0]
  | 2 => !![0, 0, 0; 0, 0, 1; 0, -1, 0]

/-- Each Werner–Holevo generator is antisymmetric: `Aₐᴴ = −Aₐ`. The entries are real (`0, ±1`),
so the conjugate transpose coincides with the transpose, and each `Aₐ` is skew. -/
theorem wernerHolevoGen_conjTranspose (a : Fin 3) :
    (wernerHolevoGen a)ᴴ = - wernerHolevoGen a := by
  fin_cases a <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [wernerHolevoGen, Matrix.conjTranspose_apply, Matrix.neg_apply]

/-- **The Werner–Holevo operator-sum identity.** For every `3 × 3` complex matrix `ρ`,
`∑ₐ Aₐ ρ Aₐᴴ = tr(ρ)·I − ρᵀ`, where `Aₐ = wernerHolevoGen a` are the three antisymmetric
generators. This is the Choi computation for the antisymmetric-subspace projector, written
entrywise; with Kraus operators `Aₐ/√2` it realises the Werner–Holevo channel `½(tr(ρ)·I − ρᵀ)`. -/
theorem wernerHolevoGen_sum_conj (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ a, wernerHolevoGen a * ρ * (wernerHolevoGen a)ᴴ
      = ρ.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - ρᵀ := by
  rw [Fin.sum_univ_three]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.transpose_apply, Matrix.trace_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp [wernerHolevoGen] <;> ring

/-- **The Werner–Holevo completeness relation** `∑ₐ Aₐᴴ Aₐ = 2·I`. Since each `Aₐᴴ = −Aₐ` and
`Aₐ² = −(Eᵢᵢ + Eⱼⱼ)`, the sum `∑ₐ Aₐᴴ Aₐ = −∑ₐ Aₐ² = 2·I`. Consequently the scaled Kraus family
`Aₐ/√2` obeys `∑ₐ (Aₐ/√2)ᴴ (Aₐ/√2) = I`, so the Werner–Holevo channel is trace-preserving. -/
theorem wernerHolevoGen_conjTranspose_mul_self_sum :
    ∑ a, (wernerHolevoGen a)ᴴ * wernerHolevoGen a
      = (2 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [Fin.sum_univ_three]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [wernerHolevoGen] <;> ring

end AxQM.Concrete
