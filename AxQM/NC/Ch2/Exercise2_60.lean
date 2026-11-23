/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliEigen

/-!
# Nielsen & Chuang, Exercise 2.60 (eigenvalues and eigenprojectors of `v⃗ · σ⃗`)

Show v.sigma has eigenvalues ±1 and projectors P±=(I±v.sigma)/2.

For a real **unit** vector `v⃗` (`§2.2.5`, eq. 2.116), `v⃗ · σ⃗ = v₀X + v₁Y + v₂Z` is the *spin
along the `v⃗` axis* — the `Observable qubit` `pauliObservable v`. Being Hermitian with
`(v⃗·σ⃗)² = I` (a self-adjoint involution, `pauliObservable_op_mul_self`), its eigenvalues are
exactly `±1`, and the two eigenprojectors are `P± = (I ± v⃗·σ⃗)/2`.

* `pauliObservable_hasEigenstate_one` / `_neg_one` — `v⃗·σ⃗` genuinely **has** `+1` and `−1` as
  eigenvalues (each exhibits an eigenstate). The witnesses come from the nonvanishing of the
  eigenprojectors `P±`: a nonzero projector onto the `±1` eigenspace realizes that eigenvalue.
* `pauliObservable_eigenvalue_eq_one_or_neg_one` — **exhaustiveness:** *every* eigenvalue of
  `v⃗·σ⃗` is `+1` or `−1` (from `(v⃗·σ⃗)² = I`, so `μ² = 1`). Together with the two witnesses, the
  eigenvalues are exactly `{+1, −1}` — the full answer to "what eigenvalues does `v⃗·σ⃗` have?".

The **eigenprojectors** `P± = (I ± v⃗·σ⃗)/2` — the second half of the exercise — are
operator identities (they involve the operator `Observable.op`), and are formalised in:

* `Observable.projPlus` / `projMinus` (`= ½(1 ± A)`) with `…_isSelfAdjoint`, `…_mul_self` (they are
  orthogonal projectors) and the two-outcome projective `Observable.signMeasurement` are in
  `AxQM/Postulates/API/PauliMeasurement.lean` (shared with Exercise 2.61);
* that they project onto the `±1` **eigenspaces** exactly (`op_mul_projPlus`/`…Minus`:
  `A·P₊ = P₊`, `A·P₋ = −P₋`; `…_apply_eq_self`: `A u = ±u → P± u = u`), together with orthogonality
  (`projPlus_mul_projMinus`: `P₊ P₋ = 0`) and the spectral decomposition
  (`projPlus_sub_projMinus`: `P₊ − P₋ = A`), are in
  `AxQM/Postulates/API/PauliEigen.lean`, reusable for any self-adjoint involution.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.60 (`+1`).** For a unit vector `v⃗`, the spin observable
`v⃗ · σ⃗` has `+1` as an eigenvalue: there is a pure state `ψ` with `(v⃗·σ⃗) ψ = ψ`. The eigenstate
is produced from the nonzero `+1` eigenprojector `P₊ = ½(1 + v⃗·σ⃗)`. -/
theorem pauliObservable_hasEigenstate_one {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    ∃ ψ : PureState qubit, (pauliObservable v).HasEigenstate 1 ψ :=
  (pauliObservable v).exists_hasEigenstate_one_of_projPlus_ne_zero
    (pauliObservable_op_mul_self hv) (pauliObservable_projPlus_ne_zero v)

/-- **Nielsen & Chuang, Exercise 2.60 (`−1`).** For a unit vector `v⃗`, the spin observable
`v⃗ · σ⃗` has `−1` as an eigenvalue: there is a pure state `ψ` with `(v⃗·σ⃗) ψ = −ψ`. The eigenstate
is produced from the nonzero `−1` eigenprojector `P₋ = ½(1 − v⃗·σ⃗)`. -/
theorem pauliObservable_hasEigenstate_neg_one {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    ∃ ψ : PureState qubit, (pauliObservable v).HasEigenstate (-1) ψ :=
  (pauliObservable v).exists_hasEigenstate_neg_one_of_projMinus_ne_zero
    (pauliObservable_op_mul_self hv) (pauliObservable_projMinus_ne_zero v)

/-- **Nielsen & Chuang, Exercise 2.60 (exhaustiveness).** For a unit vector `v⃗`, every eigenvalue
of the spin observable `v⃗ · σ⃗` is `+1` or `−1`: if some pure state `ψ` is a `μ`-eigenstate then
`μ = 1` or `μ = −1`. This is the `⊆` half of "the eigenvalues are `±1`", from the involution
`(v⃗·σ⃗)² = I` (which forces `μ² = 1`); combined with `pauliObservable_hasEigenstate_one` and
`_neg_one` it pins the spectrum to exactly `{+1, −1}`. -/
theorem pauliObservable_eigenvalue_eq_one_or_neg_one {v : Fin 3 → ℝ}
    (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) (μ : ℝ) (ψ : PureState qubit)
    (h : (pauliObservable v).HasEigenstate μ ψ) : μ = 1 ∨ μ = -1 :=
  Observable.eigenvalue_eq_of_op_mul_self (pauliObservable_op_mul_self hv) h

end AxQM
