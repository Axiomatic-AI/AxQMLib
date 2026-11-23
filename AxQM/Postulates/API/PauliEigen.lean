/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliMeasurement
import AxQM.Postulates.API.HadamardEigen

/-!
# AxQM.Postulates.API — the eigenprojectors of `v · σ` project onto its `±1` eigenspaces

Results on the **second half of Nielsen & Chuang Exercise 2.60** ("the
projectors onto the corresponding eigenspaces are `P± = (I ± v⃗·σ⃗)/2`", §2.2.5, p. 90) and the
eigenvalue-existence witnesses behind its first half.

The eigenprojectors themselves — `Observable.projPlus A = (I + A)/2`, `Observable.projMinus A =
(I − A)/2`, their self-adjointness/idempotence, `P₊ + P₋ = 1`, and the two-outcome projective
`Observable.signMeasurement` — are in `AxQM/Postulates/API/PauliMeasurement.lean` (used
there for Exercise 2.61). This file adds what Exercise 2.60 additionally asserts of them, for an
arbitrary self-adjoint involution observable `A` (`A² = 1`):

* `op_mul_projPlus` / `op_mul_projMinus` (`A·P₊ = P₊`, `A·P₋ = −P₋`) — the range of `P±` lies in
  the `±1` eigenspace; with `projPlus_apply_eq_self` / `projMinus_apply_eq_self`
  (`A u = ±u → P± u = u`) — the `±1` eigenspace lies in the range of `P±`; together `range P±` is
  *exactly* the `(±1)`-eigenspace, i.e. `P±` **are** the projectors onto the eigenspaces;
* `projPlus_mul_projMinus` (`P₊ P₋ = 0`, orthogonal complementary) and
  `projPlus_sub_projMinus` (`P₊ − P₋ = A`, the spectral decomposition `A = (+1)P₊ + (−1)P₋`);
* `exists_hasEigenstate_{one,neg_one}_of_proj…_ne_zero` — a nonvanishing eigenprojector realizes
  its eigenvalue: `range P±` is the eigenspace, so a nonzero `P±` supplies a unit `±1`-eigenstate.

Instantiated at `v · σ` (for any `v`): `pauliObservable_proj{Plus,Minus}_ne_zero` (both
eigenprojectors are nonzero — else `v · σ` would be the scalar `∓1`, contradicting the traceless
diagonal, via `Concrete.pauliDot_ne_{neg_one,one}`), from which
`AxQM/NC/Ch2/Exercise2_60.lean` derives that `v · σ` has both `±1` as eigenvalues.

The statement that `v · σ` has eigenvalues *exactly* `±1` is in terms of
`Observable.HasEigenstate` in `AxQM/NC/Ch2/Exercise2_60.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

open ContinuousLinearMap Matrix

variable {S : QSystem}

/-! ### The eigenprojectors project onto the `±1` eigenspaces -/

/-- **`P₊` projects into the `+1` eigenspace:** `A · P₊ = P₊`, so `A(P₊ w) = P₊ w` for every `w`.
From `A² = 1`: `A·½(1+A) = ½(A + A²) = ½(A + 1) = ½(1 + A)`. -/
theorem Observable.op_mul_projPlus (A : Observable S) (hinv : A.op * A.op = 1) :
    A.op * A.projPlus = A.projPlus := by
  simp only [Observable.projPlus, mul_smul_comm, mul_add, mul_one, hinv]
  match_scalars <;> ring

/-- **`P₋` projects into the `−1` eigenspace:** `A · P₋ = −P₋`, so `A(P₋ w) = −(P₋ w)` for every
`w`. From `A² = 1`: `A·½(1−A) = ½(A − A²) = ½(A − 1) = −½(1 − A)`. -/
theorem Observable.op_mul_projMinus (A : Observable S) (hinv : A.op * A.op = 1) :
    A.op * A.projMinus = -A.projMinus := by
  simp only [Observable.projMinus, mul_smul_comm, mul_sub, mul_one, hinv]
  match_scalars <;> ring

/-- **The `+1` eigenspace lies in the range of `P₊`:** if `A u = u` then `P₊ u = u`. With
`op_mul_projPlus` this pins `range P₊` to the `+1` eigenspace exactly. -/
theorem Observable.projPlus_apply_eq_self (A : Observable S) {u : S.space} (hu : A.op u = u) :
    A.projPlus u = u := by
  simp only [Observable.projPlus, _root_.smul_apply, _root_.add_apply,
    one_apply_eq_self, hu]
  module

/-- **The `−1` eigenspace lies in the range of `P₋`:** if `A u = −u` then `P₋ u = u`. With
`op_mul_projMinus` this pins `range P₋` to the `−1` eigenspace exactly. -/
theorem Observable.projMinus_apply_eq_self (A : Observable S) {u : S.space} (hu : A.op u = -u) :
    A.projMinus u = u := by
  simp only [Observable.projMinus, _root_.smul_apply, _root_.sub_apply,
    one_apply_eq_self, hu]
  module

/-- **`P₊` on a `c`-eigenvector:** if `A u = c • u` then `P₊ u = ½(1 + c) • u`. The
general-eigenvalue form of `projPlus_apply_eq_self` (its `c = 1` case), giving the
`+1`-measurement coefficient on any eigenvector of a `±1` observable. -/
theorem Observable.projPlus_apply_smul (A : Observable S) {v : S.space} {c : ℂ}
    (h : A.op v = c • v) : A.projPlus v = (2⁻¹ * (1 + c)) • v := by
  rw [Observable.projPlus, _root_.smul_apply, _root_.add_apply,
    one_apply_eq_self, h]
  module

/-- **`P₋` on a `c`-eigenvector:** if `A u = c • u` then `P₋ u = ½(1 − c) • u`. The
general-eigenvalue form of `projMinus_apply_eq_self` (its `c = −1` case), giving the
`−1`-measurement coefficient on any eigenvector of a `±1` observable. -/
theorem Observable.projMinus_apply_smul (A : Observable S) {v : S.space} {c : ℂ}
    (h : A.op v = c • v) : A.projMinus v = (2⁻¹ * (1 - c)) • v := by
  rw [Observable.projMinus, _root_.smul_apply, _root_.sub_apply,
    one_apply_eq_self, h]
  module

/-- **Orthogonality of the eigenprojectors:** `P₊ P₋ = 0` (their ranges — the `±1` eigenspaces —
are orthogonal). From `A² = 1`: `¼(1 + A)(1 − A) = ¼(1 − A²) = 0`. -/
theorem Observable.projPlus_mul_projMinus (A : Observable S) (hinv : A.op * A.op = 1) :
    A.projPlus * A.projMinus = 0 := by
  simp only [Observable.projPlus, Observable.projMinus, smul_mul_smul_comm, mul_sub, add_mul,
    one_mul, mul_one, hinv]
  match_scalars <;> ring

/-- **Spectral decomposition:** `P₊ − P₋ = A`, i.e. `A = (+1)P₊ + (−1)P₋`. -/
theorem Observable.projPlus_sub_projMinus (A : Observable S) :
    A.projPlus - A.projMinus = A.op := by
  simp only [Observable.projPlus, Observable.projMinus]
  match_scalars <;> ring

/-! ### Existence of eigenstates from nonvanishing eigenprojectors -/

/-- **A nonzero `+1` eigenprojector realizes the eigenvalue `+1`.** If `P₊ ≠ 0` then `A` has a
`+1` eigenstate: pick `x` with `P₊ x ≠ 0`; then `A(P₊ x) = P₊ x` (as `A · P₊ = P₊`), so the
normalized `P₊ x` (via the shared `PureState.normalize`) is a unit `+1` eigenstate. -/
theorem Observable.exists_hasEigenstate_one_of_projPlus_ne_zero (A : Observable S)
    (hinv : A.op * A.op = 1) (hne : A.projPlus ≠ 0) :
    ∃ ψ : PureState S, A.HasEigenstate 1 ψ := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hne
  rw [_root_.zero_apply] at hx
  have hAu : A.op (A.projPlus x) = A.projPlus x := by
    have := congrArg (fun T : S.space →L[ℂ] S.space => T x) (A.op_mul_projPlus hinv)
    simpa [mul_apply_eq_comp] using this
  refine ⟨PureState.normalize _ hx, A.hasEigenstate_of_smul
    (c := ((‖A.projPlus x‖ : ℝ) : ℂ)⁻¹) (v := A.projPlus x) rfl ?_⟩
  rw [hAu]; norm_num

/-- **A nonzero `−1` eigenprojector realizes the eigenvalue `−1`.** If `P₋ ≠ 0` then `A` has a
`−1` eigenstate: pick `x` with `P₋ x ≠ 0`; then `A(P₋ x) = −(P₋ x)` (as `A · P₋ = −P₋`), so the
normalized `P₋ x` (via the shared `PureState.normalize`) is a unit `−1` eigenstate. -/
theorem Observable.exists_hasEigenstate_neg_one_of_projMinus_ne_zero (A : Observable S)
    (hinv : A.op * A.op = 1) (hne : A.projMinus ≠ 0) :
    ∃ ψ : PureState S, A.HasEigenstate (-1) ψ := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hne
  rw [_root_.zero_apply] at hx
  have hAu : A.op (A.projMinus x) = -(A.projMinus x) := by
    have := congrArg (fun T : S.space →L[ℂ] S.space => T x) (A.op_mul_projMinus hinv)
    simpa [mul_apply_eq_comp] using this
  refine ⟨PureState.normalize _ hx, A.hasEigenstate_of_smul
    (c := ((‖A.projMinus x‖ : ℝ) : ℂ)⁻¹) (v := A.projMinus x) rfl ?_⟩
  rw [hAu]; push_cast; module

/-! ### The eigenprojectors of `v · σ` are nonzero -/

/-- **The `+1` eigenprojector of `v · σ` is nonzero** (for any `v`, in particular a unit vector).
Were `½(1 + v·σ) = 0` then `v · σ = −1` as an operator; injectivity of `Matrix.toEuclideanCLM`
forces `pauliDot v = −1`, impossible for the traceless diagonal `(v₂, −v₂)`
(`Concrete.pauliDot_ne_neg_one`). Hence (for a unit vector) `+1` is an eigenvalue of `v · σ`. -/
theorem pauliObservable_projPlus_ne_zero (v : Fin 3 → ℝ) :
    (pauliObservable v).projPlus ≠ 0 := by
  intro h
  rw [Observable.projPlus, smul_eq_zero] at h
  rcases h with h | h
  · norm_num at h
  rw [pauliObservable_op] at h
  refine Concrete.pauliDot_ne_neg_one v ?_
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective
  rw [map_neg, map_one]
  exact eq_neg_of_add_eq_zero_right h

/-- **The `−1` eigenprojector of `v · σ` is nonzero** (for any `v`, in particular a unit vector).
Were `½(1 − v·σ) = 0` then `v · σ = 1`; injectivity forces `pauliDot v = 1`, impossible for the
traceless diagonal `(v₂, −v₂)` (`Concrete.pauliDot_ne_one`). Hence (for a unit vector) `−1` is an
eigenvalue of `v · σ`. -/
theorem pauliObservable_projMinus_ne_zero (v : Fin 3 → ℝ) :
    (pauliObservable v).projMinus ≠ 0 := by
  intro h
  rw [Observable.projMinus, smul_eq_zero] at h
  rcases h with h | h
  · norm_num at h
  rw [pauliObservable_op] at h
  refine Concrete.pauliDot_ne_one v ?_
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective
  rw [map_one]
  exact (sub_eq_zero.mp h).symm

end AxQM
