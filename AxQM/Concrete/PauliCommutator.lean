/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Analysis.Complex.Basic

/-!
# Concrete: multiplication and commutation relations for the Pauli matrices (N&C Ex. 2.40, 2.43)

This file verifies the Pauli-matrix commutation relations of Nielsen & Chuang, Exercise 2.40, and
the full multiplication relation of Exercise 2.43, over the concrete `2 × 2` complex matrices
`pauliX`, `pauliY`, `pauliZ` from `AxQM.Concrete.Pauli`.

N&C, Exercise 2.40, asks to verify the three commutation relations (eq. 2.73)

`[X, Y] = 2iZ,   [Y, Z] = 2iX,   [Z, X] = 2iY`,

and remarks that they are written elegantly with the Levi-Civita symbol `ε_{jkl}` (eq. 2.74)

`[σⱼ, σₖ] = 2i Σₗ ε_{jkl} σₗ`.

Here `[A, B] = AB − BA` is the ring commutator, which on matrices is exactly Mathlib's Lie
bracket `⁅A, B⁆` (`Ring.lie_def`), matching N&C's notation.

Exercise 2.43 asks to verify the **full multiplication relation** (eq. 2.78), for `j, k = 1, 2, 3`,

`σⱼ σₖ = δ_{jk} I + i Σₗ ε_{jkl} σₗ`,

whose symmetric part `δ_{jk} I` is the anticommutator content (eqs. 2.75–2.76) and whose
antisymmetric part `i Σₗ ε_{jkl} σₗ` is the commutator content (eq. 2.74). It is thus the most
fundamental of the three: the commutation relation `pauliSigma_lie` is recovered from it as the
antisymmetric part (`σⱼσₖ − σₖσⱼ`, where the `δ` terms cancel and `ε` doubles), and the
anticommutator `{σⱼ, σₖ} = 2 δ_{jk} I` as the symmetric part.

## The declarations

* `leviCivita3` — the totally antisymmetric symbol `ε` on three `Fin 3` indices, `+1` on the
  cyclic orderings, `-1` on the anticyclic ones, `0` when any two indices coincide.
* `pauliSigma` — the family `σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ` indexing the three
  non-identity Pauli matrices, with unfolding lemmas `pauliSigma_zero/one/two`.
* `pauliSigma_lie` — the elegant commutator tensor form (eq. 2.74): `⁅σⱼ, σₖ⁆ = 2i Σₗ ε_{jkl} σₗ`.
* `pauliSigma_mul` — the full multiplication relation (Exercise 2.43, eq. 2.78):
  `σⱼ σₖ = δ_{jk} I + i Σₗ ε_{jkl} σₗ`.
* `pauliX_lie_pauliY`, `pauliY_lie_pauliZ`, `pauliZ_lie_pauliX` — the three explicit relations
  (eq. 2.73), derived as the cyclic instances of `pauliSigma_lie`.

## Design notes

* **Index convention.** N&C numbers the Paulis `σ₁ = X`, `σ₂ = Y`, `σ₃ = Z` with `ε_{123} = 1`;
  here `Fin 3` is `0`-based, so `pauliSigma i` is N&C's `σ_{i+1}` and `leviCivita3 j k l` is
  N&C's `ε_{(j+1)(k+1)(l+1)}`. This is a faithful reindexing, not a weakening: the full
  antisymmetric structure is preserved, only shifted by one.
* **`ε` as a lookup table.** `leviCivita3` is given as a nested `![…]` vector so that, after
  `fin_cases` on the indices, each entry reduces definitionally; the tensor form is then a
  finite `2 × 2` matrix computation over the nine `(j, k)` cases.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The totally antisymmetric Levi-Civita symbol `ε` on three `Fin 3` indices (Nielsen & Chuang,
eq. 2.74). It is `+1` on the cyclic orderings `(0,1,2), (1,2,0), (2,0,1)`, `-1` on the anticyclic
orderings `(2,1,0), (1,0,2), (0,2,1)`, and `0` whenever two indices coincide. With `Fin 3`
`0`-based, `leviCivita3 j k l` is N&C's `ε_{(j+1)(k+1)(l+1)}`. -/
def leviCivita3 : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- The family `σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ` indexing the three non-identity Pauli
matrices: `pauliSigma 0 = X`, `pauliSigma 1 = Y`, `pauliSigma 2 = Z` (N&C's `σ₁, σ₂, σ₃`). -/
def pauliSigma : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliX, pauliY, pauliZ]

/-- `pauliSigma 0 = X`. -/
@[simp] theorem pauliSigma_zero : pauliSigma 0 = pauliX := rfl

/-- `pauliSigma 1 = Y`. -/
@[simp] theorem pauliSigma_one : pauliSigma 1 = pauliY := rfl

/-- `pauliSigma 2 = Z`. -/
@[simp] theorem pauliSigma_two : pauliSigma 2 = pauliZ := rfl

/-- **Commutation relations for the Pauli matrices, elegant form** (Nielsen & Chuang,
Exercise 2.40, eq. 2.74): `⁅σⱼ, σₖ⁆ = 2i Σₗ ε_{jkl} σₗ`, where `⁅·,·⁆` is the matrix commutator
`AB − BA`. Proved by checking all nine `(j, k)` cases as explicit `2 × 2` matrix computations. -/
theorem pauliSigma_lie (j k : Fin 3) :
    ⁅pauliSigma j, pauliSigma k⁆ =
      (2 * I) • ∑ l, (leviCivita3 j k l : ℂ) • pauliSigma l := by
  fin_cases j <;> fin_cases k <;>
    simp only [pauliSigma, leviCivita3, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Ring.lie_def, pauliX, pauliY, pauliZ] <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff]) <;> ring

/-- **Full multiplication relation for the Pauli matrices** (Nielsen & Chuang, Exercise 2.43,
eq. 2.78): for `j, k = 1, 2, 3`, `σⱼ σₖ = δ_{jk} I + i Σₗ ε_{jkl} σₗ`, where `δ_{jk}` is the
Kronecker delta (here `if j = k then 1 else 0`) and `I` the identity matrix. This unifies the
commutation relations (its antisymmetric part, `pauliSigma_lie`, eq. 2.74) and the
anticommutation relations (its symmetric part, `{σⱼ, σₖ} = 2 δ_{jk} I`, eqs. 2.75–2.76): both are
corollaries of this single identity. Proved by checking all nine `(j, k)` cases as explicit
`2 × 2` matrix computations. -/
theorem pauliSigma_mul (j k : Fin 3) :
    pauliSigma j * pauliSigma k =
      (if j = k then (1 : ℂ) else 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + I • ∑ l, (leviCivita3 j k l : ℂ) • pauliSigma l := by
  fin_cases j <;> fin_cases k <;>
    simp only [pauliSigma, leviCivita3, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      pauliX, pauliY, pauliZ] <;>
    (ext a b; fin_cases a <;> fin_cases b <;> simp)

/-- **`[X, Y] = 2iZ`** (Nielsen & Chuang, Exercise 2.40, eq. 2.73), the cyclic instance
`⁅σ₁, σ₂⁆ = 2i σ₃` of `pauliSigma_lie`. -/
theorem pauliX_lie_pauliY : ⁅pauliX, pauliY⁆ = (2 * I) • pauliZ := by
  simpa [leviCivita3, Fin.sum_univ_three] using pauliSigma_lie 0 1

/-- **`[Y, Z] = 2iX`** (Nielsen & Chuang, Exercise 2.40, eq. 2.73), the cyclic instance
`⁅σ₂, σ₃⁆ = 2i σ₁` of `pauliSigma_lie`. -/
theorem pauliY_lie_pauliZ : ⁅pauliY, pauliZ⁆ = (2 * I) • pauliX := by
  simpa [leviCivita3, Fin.sum_univ_three] using pauliSigma_lie 1 2

/-- **`[Z, X] = 2iY`** (Nielsen & Chuang, Exercise 2.40, eq. 2.73), the cyclic instance
`⁅σ₃, σ₁⁆ = 2i σ₂` of `pauliSigma_lie`. -/
theorem pauliZ_lie_pauliX : ⁅pauliZ, pauliX⁆ = (2 * I) • pauliY := by
  simpa [leviCivita3, Fin.sum_univ_three] using pauliSigma_lie 2 0

/-- Each entry of `n·σ = pauliDot n` is the linear form `∑ₐ (σ^a)ᵢⱼ nₐ` in the components of `n`
(with `σ^a = pauliSigma a`). A general property of `pauliDot`/`pauliSigma`. -/
theorem pauliDot_entry_eq_sum (n : Fin 3 → ℝ) (i j : Fin 2) :
    (pauliDot n) i j = ∑ a, pauliSigma a i j * (n a : ℂ) := by
  simp only [pauliDot, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three,
    pauliSigma_zero, pauliSigma_one, pauliSigma_two]
  ring

/-- Each entry of `n·σ = pauliDot n` is continuous in `n` (a linear form in the components). -/
theorem continuous_pauliDot_entry (i j : Fin 2) :
    Continuous (fun n : Fin 3 → ℝ => (pauliDot n) i j) := by
  simp_rw [pauliDot_entry_eq_sum]; fun_prop

end AxQM.Concrete
