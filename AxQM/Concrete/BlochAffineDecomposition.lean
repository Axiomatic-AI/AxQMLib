/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Concrete: the `O S` decomposition of the Bloch affine map (`det O = 1`, `det S` unsigned)

This file supplies the mathematical content behind **Nielsen & Chuang, Exercises 8.12 and 8.14
(p. 375)** — two companion facts about the `M = O S` factorization (N&C (8.93)) of the Bloch
affine-map matrix.

## Context in N&C

A trace-preserving quantum operation on a single qubit acts on the Bloch vector as an affine map
`r ↦ M r + c` with `M` a real `3 × 3` matrix (N&C (8.89)). Writing the polar decomposition of `M`
and using that `M` is real, N&C obtains the factorization (N&C (8.93))

> `M = O S`,   `O` a real orthogonal matrix with determinant `1` (a *proper rotation*),
> `S` a real symmetric matrix,

reading the map as a deformation along the principal axes of `S`, followed by the proper rotation
`O`, followed by the displacement `c`. **Exercise 8.12** asks *why* one may always take `det O = 1`.

## The answer, formalized

An orthogonal matrix has `det = ±1` (`det (Oᵀ O) = det 1` forces `(det O)² = 1`), so the polar
factor `O` is orthogonal but possibly *improper* (`det O = -1`). The freedom that rescues
`det O = 1` is the choice to relax `S` from *positive semidefinite* (the polar factor `√(Mᵀ M)`) to
*symmetric*: negating **both** factors, `M = (-O)(-S)`, leaves `-S` symmetric and — because the
Bloch space has **odd** dimension `3` — flips the determinant,
`det (-O) = (-1)³ det O = -det O`, turning an improper `O` into a proper one. (In even dimension the
sign would not flip; Mathlib records this asymmetry by defining `Neg` on `SpecialLinearGroup` only
under `Fact (Even (Fintype.card n))`.) The price is that `S` need no longer be positive
semidefinite — precisely the observation of the companion Exercise 8.14 (`det S` need not be
positive).

## Exercise 8.14: `det S` need not be positive

Once the orthogonal factor is forced to be a proper rotation (`det O = 1`, Exercise 8.12), the
symmetric factor loses positivity. The reason is a one-line determinant identity: for any
factorization `M = O S` with `O ∈ SO(n)`,

> `det S = det O · det S = det (O S) = det M`,

so the sign of `det S` is *pinned* to the sign of `det M` and cannot be chosen — `det S` is
positive only when the Bloch map preserves orientation (`det M > 0`). Whenever the map is
orientation-reversing (`det M < 0`) the proper-rotation factorization is forced to have
`det S < 0`. A concrete witness is the reflection `M = diag(1, 1, -1)` (`det M = -1`): its improper
polar factor `U = M` with positive semidefinite `|M| = √(Mᵀ M) = I` (so the *polar* `S = |M|` has
`det = +1 > 0`) is normalized as in Exercise 8.12 to `O = -U = diag(-1, -1, 1) ∈ SO(3)`,
`S = -|M| = -I`, and now `det S = det(-I) = (-1)³ = -1 < 0`. (This file constructs the witness
directly; the positive-semidefinite polar factor `|M|` is described here but not itself built, as
Exercise 8.14 only needs the existence of *some* `O S` factorization with `det S < 0`.)

## Related items

The statements of Exercises 8.12 and 8.14 are in `AxQM/NC/Ch8/Exercise8_12.lean` and
`AxQM/NC/Ch8/Exercise8_14.lean`. The affine map
`r ↦ M r + c` itself is not constructed here: Exercises 8.12 and 8.14 take the `O S` factorization
(8.93) as given and ask only about the freedom in it, so the results below quantify over an
arbitrary real `3 × 3` matrix `M` presented in that factored form.
-/

namespace AxQM.Concrete

open Matrix

/-- An orthogonal matrix over `ℝ` has determinant `±1`: from `Oᵀ O = 1` we get
`(det O)² = det (Oᵀ O) = 1`, whence `det O = 1` or `det O = -1`. -/
theorem det_eq_one_or_neg_one_of_mem_orthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ Matrix.orthogonalGroup n ℝ) : O.det = 1 ∨ O.det = -1 := by
  have hOtO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hO
  have h : O.det * O.det = 1 := by
    have := congrArg Matrix.det hOtO
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  exact mul_self_eq_one_iff.mp h

/-- **Nielsen & Chuang, Exercise 8.12.** In the factorization `M = O S` of the real `3 × 3` Bloch
affine-map matrix into an orthogonal `O` and a symmetric `S` (N&C (8.93)), the orthogonal factor may
always be taken to be a *proper rotation*, `O ∈ SO(3)` (i.e. `det O = 1`), while keeping the other
factor symmetric.

If `O` is already proper we keep `(O, S)`. Otherwise `det O = -1`, and we replace `(O, S)` by
`(-O, -S)`: `-S` is again symmetric, and in the odd dimension `3` one has
`det (-O) = (-1)³ det O = 1`, so `-O ∈ SO(3)`, while `(-O)(-S) = O S = M`. (Symmetry of `S` — not
positive semidefiniteness — is all that is used, which is why `S` may fail to be positive
semidefinite after the normalization; cf. Exercise 8.14.) -/
theorem exists_mem_specialOrthogonalGroup_symmetric_factor
    {M O S : Matrix (Fin 3) (Fin 3) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hS : Sᵀ = S) (hM : M = O * S) :
    ∃ O' S' : Matrix (Fin 3) (Fin 3) ℝ,
      O' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ S'ᵀ = S' ∧ M = O' * S' := by
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup hO with hd | hd
  · exact ⟨O, S, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hO, hd⟩, hS, hM⟩
  · refine ⟨-O, -S, ?_, ?_, ?_⟩
    · refine Matrix.mem_specialOrthogonalGroup_iff.mpr
        ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr ?_, ?_⟩
      · rw [Matrix.transpose_neg, neg_mul_neg]
        exact (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO
      · rw [Matrix.det_neg, hd, Fintype.card_fin]; norm_num
    · rw [Matrix.transpose_neg, hS]
    · rw [hM, neg_mul_neg]

/-- In a factorization `M = O S` whose left factor `O` is a *proper rotation*
(`O ∈ SO(n)`, i.e. `det O = 1`), the determinant of the right factor equals `det M`:
`det M = det (O S) = det O · det S = det S`. Hence the sign of `det S` is pinned to that of
`det M` and cannot be chosen — this is the reason forcing `det O = 1` in the Bloch decomposition
(Exercise 8.12) costs the positivity of the symmetric factor `S` (Exercise 8.14). -/
theorem det_right_eq_det_of_mem_specialOrthogonalGroup
    {n : Type*} [Fintype n] [DecidableEq n] {M O S : Matrix n n ℝ}
    (hO : O ∈ Matrix.specialOrthogonalGroup n ℝ) (hM : M = O * S) : S.det = M.det := by
  have hdet : O.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp hO).2
  rw [hM, Matrix.det_mul, hdet, one_mul]

/-- **Nielsen & Chuang, Exercise 8.14.** In the `M = O S` decomposition of the real `3 × 3` Bloch
affine-map matrix into a *proper rotation* `O ∈ SO(3)` and a symmetric `S` (N&C (8.93), with `O`
normalized to `det O = 1` as in Exercise 8.12), the symmetric factor `S` need **not** be positive:
there is a factorization of this form with `det S < 0`.

Witness: the orientation-reversing reflection `M = diag(1, 1, -1)` factors as `O = diag(-1, -1, 1)`
(a proper rotation, `det O = 1`) times `S = -I` (symmetric), and `det S = det(-I) = (-1)³ = -1 < 0`.
By `det_right_eq_det_of_mem_specialOrthogonalGroup` this `det S = det M = -1` is forced: no
proper-rotation factorization of an orientation-reversing Bloch map can have `det S ≥ 0`. -/
theorem exists_specialOrthogonalGroup_symmetric_factor_det_neg :
    ∃ M O S : Matrix (Fin 3) (Fin 3) ℝ,
      O ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ Sᵀ = S ∧ M = O * S ∧ S.det < 0 := by
  refine ⟨_, Matrix.diagonal ![-1, -1, 1], -1, ?_, ?_, rfl, ?_⟩
  · rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ, Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      ext i
      fin_cases i <;> norm_num
    · simp [Matrix.det_diagonal, Fin.prod_univ_three]
  · rw [Matrix.transpose_neg, Matrix.transpose_one]
  · rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num

end AxQM.Concrete
