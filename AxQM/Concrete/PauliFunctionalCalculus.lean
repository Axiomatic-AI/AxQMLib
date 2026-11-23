/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Matrix.Spectrum
import AxQM.Concrete.Pauli

/-!
# Concrete: functions of the Pauli combination `θ n·σ` (Nielsen & Chuang, Problem 2.1)

This file formalises **Nielsen & Chuang, Problem 2.1 ("Functions of the Pauli
matrices")**: for *any* function `f : ℂ → ℂ`, a real angle `θ`, and a normalized
real three-vector `n`,

`f(θ n·σ) = ((f(θ) + f(-θ))/2) I + ((f(θ) - f(-θ))/2) n·σ`.  (N&C (2.231))

It builds on the `n·σ` algebra of `AxQM/Concrete/Pauli.lean` — in particular
`pauliDot_mul_self_of_unit`, `(n·σ)² = I` for a unit vector.

## What "a function of an operator" means

Following N&C's own definition of functions of a normal operator (Box 2.2,
`f(A) ≡ Σₐ f(a) |a⟩⟨a|` over the spectral decomposition `A = Σₐ a|a⟩⟨a|`), we apply
`f` to a Hermitian matrix through its spectral theorem: `f(A) = U f(Λ) U†`, where
`A = U Λ U†` is the unitary diagonalization and `Λ` the diagonal of eigenvalues.

Mathlib already has this construction for **real-valued** functions,
`Matrix.IsHermitian.cfc : (ℝ → ℝ) → Matrix n n 𝕜`. N&C, however, states the problem
for `f : ℂ → ℂ` — and this generality is genuinely used elsewhere in the chapter
(e.g. `exp(i θ n·σ)`, Exercise 2.35, needs a complex-valued `f`), so the real-codomain
`cfc` is too weak. We therefore define `functionOfHermitian`, the exact **complex**
analogue of Mathlib's `Matrix.IsHermitian.cfc`: the same triple product
`U · diagonal (f ∘ eigenvalues) · U†`, but with `f : ℂ → ℂ` (evaluated at the real
eigenvalues, coerced into `ℂ`). No continuity hypothesis is needed — every function is
continuous on the finite spectrum of a matrix — so this faithfully captures N&C's
"any function from complex numbers to complex numbers".

`functionOfHermitian` is stated for an arbitrary index type.

## Proof of the decomposition

Write `M = θ • (n·σ)`. From `(n·σ)² = I` we get `M² = θ² • I`, hence every eigenvalue
`λ` of `M` satisfies `λ² = θ²`, i.e. `λ ∈ {θ, -θ}` (`pauliDot_smul_eigenvalues_sq`).
On that two-point spectrum `f` agrees with the affine function
`z ↦ (f(θ)+f(-θ))/2 + ((f(θ)-f(-θ))/(2θ)) z`, so — pushing the affine combination
through the unitary conjugation (a `⋆`-algebra automorphism, hence `ℂ`-linear and
unital) and using the spectral theorem `U Λ U† = M` — `f(M)` collapses to
`((f(θ)+f(-θ))/2) I + ((f(θ)-f(-θ))/2) n·σ`. The degenerate case `θ = 0` (where the
affine slope is undefined) is handled separately: there `M = 0`, every eigenvalue is
`0`, and both sides equal `f(0) I`.
-/

namespace AxQM.Concrete

open Matrix Complex

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The **spectral functional calculus** of a Hermitian matrix for a complex-valued
function `f : ℂ → ℂ`: the triple product `U · diagonal (f ∘ eigenvalues) · U†` from the
spectral theorem, evaluating `f` at the (coerced) real eigenvalues. This is the
`ℂ`-valued analogue of `Matrix.IsHermitian.cfc` (which is restricted to `ℝ → ℝ`), and it
matches Nielsen & Chuang's definition `f(A) = Σₐ f(a) |a⟩⟨a|` of a function of a normal
operator. -/
noncomputable def functionOfHermitian {A : Matrix m m ℂ} (hA : A.IsHermitian)
    (f : ℂ → ℂ) : Matrix m m ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ)) hA.eigenvectorUnitary
    (Matrix.diagonal fun i => f (hA.eigenvalues i))

/-- Applying the identity function recovers the matrix: `functionOfHermitian hA id = A`.
This is a restatement of the spectral theorem, and confirms that `functionOfHermitian`
is a genuine functional calculus (the variable `z` maps to `A` itself). -/
theorem functionOfHermitian_id {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    functionOfHermitian hA (fun z => z) = A := by
  rw [functionOfHermitian]
  exact hA.spectral_theorem.symm

/-- `functionOfHermitian` depends only on the values of `f` on the spectrum: two functions
agreeing on the eigenvalues produce the same operator. -/
theorem functionOfHermitian_congr {A : Matrix m m ℂ} (hA : A.IsHermitian) {f g : ℂ → ℂ}
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    functionOfHermitian hA f = functionOfHermitian hA g := by
  unfold functionOfHermitian
  congr 1
  exact congrArg Matrix.diagonal (funext h)

/-- `functionOfHermitian` of an affine function `z ↦ a + b z` is that affine combination of
`A`: `functionOfHermitian hA (a + b ·) = a • I + b • A`. This is the linearity+unitality of the
functional calculus (the `⋆`-algebra automorphism is `ℂ`-linear and unital), and is exactly the
"agrees with an affine map on the spectrum" pattern used to prove decompositions such as (2.231)
and `exp(iθ n·σ)` (Exercise 2.35). -/
theorem functionOfHermitian_affine {A : Matrix m m ℂ} (hA : A.IsHermitian) (a b : ℂ) :
    functionOfHermitian hA (fun z => a + b * z) = a • (1 : Matrix m m ℂ) + b • A := by
  have hdiag : (Matrix.diagonal fun i => a + b * ((hA.eigenvalues i : ℝ) : ℂ))
      = a • (1 : Matrix m m ℂ)
        + b • Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hij]
  have hid : (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ)) hA.eigenvectorUnitary
      (Matrix.diagonal fun i => ((hA.eigenvalues i : ℝ) : ℂ)) = A := functionOfHermitian_id hA
  rw [functionOfHermitian, hdiag, map_add, map_smul, map_one, map_smul, hid]

/-- `θ • (n·σ)` is Hermitian, since `n·σ` is Hermitian and `θ` is real. -/
theorem pauliDot_smul_isHermitian (θ : ℝ) (n : Fin 3 → ℝ) :
    ((θ : ℂ) • pauliDot n).IsHermitian :=
  (pauliDot_isHermitian n).smul (Complex.conj_ofReal θ)

/-- Every eigenvalue `λ` of `M = θ • (n·σ)` (for a unit vector `n`) satisfies `λ² = θ²`,
because `M² = θ² • I`. -/
theorem pauliDot_smul_eigenvalues_sq {θ : ℝ} {n : Fin 3 → ℝ}
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (i : Fin 2) :
    (pauliDot_smul_isHermitian θ n).eigenvalues i ^ 2 = θ ^ 2 := by
  set hM := pauliDot_smul_isHermitian θ n with hM_def
  -- `M * M = (θ * θ) • 1`.
  have hMM : ((θ : ℂ) • pauliDot n) * ((θ : ℂ) • pauliDot n)
      = ((θ : ℂ) * (θ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, pauliDot_mul_self_of_unit h]
  -- Conjugating by `U†` diagonalizes; squaring the diagonal gives `(θ*θ) • 1`.
  have hDD : Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
        * Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
      = ((θ : ℂ) * (θ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← hM.conjStarAlgAut_star_eigenvectorUnitary, ← map_mul, hMM, map_smul, map_one]
  rw [Matrix.diagonal_mul_diagonal] at hDD
  -- Read off the `(i, i)` entry.
  have hii := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i i) hDD
  simp only [Matrix.diagonal_apply_eq, Function.comp_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at hii
  -- `RCLike.ofReal` on `ℂ` is defeq to the `ℝ → ℂ` coercion; retype accordingly, then descend.
  have hii2 : ((hM.eigenvalues i : ℝ) : ℂ) * ((hM.eigenvalues i : ℝ) : ℂ)
      = ((θ : ℝ) : ℂ) * ((θ : ℝ) : ℂ) := hii
  rw [pow_two, pow_two]
  exact_mod_cast hii2

/-- **Nielsen & Chuang, Problem 2.1 (Functions of the Pauli matrices).** For any
`f : ℂ → ℂ`, real `θ`, and normalized real three-vector `n`,

`f(θ n·σ) = ((f(θ) + f(-θ))/2) I + ((f(θ) - f(-θ))/2) n·σ`.

Here `f(θ n·σ)` is the spectral functional calculus `functionOfHermitian` of the
Hermitian matrix `θ • (n·σ)`. -/
theorem functionOfPauliDot_decomposition (f : ℂ → ℂ) (θ : ℝ) {n : Fin 3 → ℝ}
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    functionOfHermitian (pauliDot_smul_isHermitian θ n) f =
      ((f θ + f (-θ)) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + ((f θ - f (-θ)) / 2) • pauliDot n := by
  set hM := pauliDot_smul_isHermitian θ n with hM_def
  -- Every eigenvalue satisfies `λ² = θ²` (rephrased against the abbreviation `hM`).
  have hsq : ∀ i, hM.eigenvalues i ^ 2 = θ ^ 2 := by
    intro i; rw [hM_def]; exact pauliDot_smul_eigenvalues_sq h i
  by_cases hθ : θ = 0
  · -- Degenerate case `θ = 0`: every eigenvalue is `0`, so `f` agrees with the constant
    -- (slope-0 affine) map `z ↦ f 0 + 0·z`; reuse `_congr` + `_affine` as in the generic branch.
    have hev : ∀ i, hM.eigenvalues i = 0 := by
      intro i
      have h2 : hM.eigenvalues i ^ 2 = 0 := by rw [hsq i, hθ]; ring
      exact pow_eq_zero_iff (by norm_num) |>.mp h2
    rw [functionOfHermitian_congr hM (g := fun z => f 0 + 0 * z) (fun i => by rw [hev i]; simp),
      functionOfHermitian_affine hM (f 0) 0, hθ]
    simp only [Complex.ofReal_zero, neg_zero]
    module
  · -- Generic case `θ ≠ 0`: `f` agrees on the spectrum `{θ, -θ}` with the affine map
    -- `z ↦ α + β z`, so `functionOfHermitian` collapses via `_congr` then `_affine`.
    have hθc : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
    set α := (f θ + f (-θ)) / 2 with hα
    set β := (f θ - f (-θ)) / (2 * (θ : ℂ)) with hβ
    -- On the spectrum `{θ, -θ}`, `f` agrees with the affine function `z ↦ α + β z`.
    have hpt : ∀ i, f ((hM.eigenvalues i : ℝ) : ℂ) = α + β * ((hM.eigenvalues i : ℝ) : ℂ) := by
      intro i
      have hfac : (hM.eigenvalues i - θ) * (hM.eigenvalues i + θ) = 0 := by
        linear_combination hsq i
      rcases mul_eq_zero.mp hfac with he | he
      · have hlam : hM.eigenvalues i = θ := sub_eq_zero.mp he
        rw [hlam, hα, hβ]; field_simp; ring
      · have hlam : hM.eigenvalues i = -θ := eq_neg_of_add_eq_zero_left he
        rw [hlam, hα, hβ]; push_cast; field_simp; ring
    have hcoef : β * (θ : ℂ) = (f θ - f (-θ)) / 2 := by rw [hβ]; field_simp
    rw [functionOfHermitian_congr hM (g := fun z => α + β * z) hpt,
      functionOfHermitian_affine hM α β, smul_smul, hcoef]

end AxQM.Concrete
