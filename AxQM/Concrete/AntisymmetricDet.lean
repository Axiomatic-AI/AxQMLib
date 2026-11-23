/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Concrete: no antisymmetric invertible matrix in odd dimension

This file contains elementary matrix facts about
antisymmetric (skew-symmetric) matrices and their determinants. Its purpose is
the **contradiction infrastructure** for the Werner–Holevo counterexample of
Nielsen & Chuang, **Problem 8.3** (a unital channel in dimension `3` that is *not* random-unitary):
the pure-state evaluation of a hypothetical random-unitary representation of `Φ(ρ) = ½(tr(ρ)I − ρᵀ)`
forces each conjugating unitary `U` to satisfy `ψᵀ U ψ = 0` for every vector `ψ`, and this file
shows that an *invertible* (in particular unitary) matrix in **odd** dimension cannot do that.

The chain is entirely classical linear algebra:

* `AxQM.Concrete.transpose_eq_neg_of_forall_dotProduct_mulVec_self_eq_zero` —
  **polarization:**
  if the quadratic form `ψ ⬝ᵥ M.mulVec ψ` vanishes for *every* `ψ`, then `M` is antisymmetric,
  `Mᵀ = −M` (over any commutative ring). Plug the standard basis vectors `eᵢ` and their sums
  `eᵢ + eⱼ`: the diagonal entries vanish and each `Mᵢⱼ + Mⱼᵢ = 0`.
* `AxQM.Concrete.det_eq_zero_of_transpose_eq_neg` — **odd antisymmetric ⟹ singular:** an
  antisymmetric `n × n` complex matrix with `n` odd has determinant `0`. Indeed
  `det M = det Mᵀ = det (−M) = (−1)ⁿ det M = −det M`, so `2 · det M = 0`, hence `det M = 0`
  (`ℂ` is `2`-torsion-free). *(Holds over any field / integral domain of characteristic ≠ 2; stated
  over `ℂ` here, the working ring.)*
* `AxQM.Concrete.det_eq_zero_of_forall_dotProduct_mulVec_self_eq_zero` — the composition:
  an odd-dimensional complex matrix whose quadratic form vanishes identically is singular.
* `AxQM.Concrete.not_forall_dotProduct_mulVec_self_eq_zero_of_isUnit_det` — the
  **contradiction:** an odd-dimensional complex matrix with invertible determinant
  (`IsUnit M.det`) — in particular any unitary, since a unitary matrix has `IsUnit M.det`
  (`Matrix.UnitaryGroup.det_isUnit`) — cannot have its quadratic form vanish on every vector. This
  is the statement the Problem 8.3 counterexample applies to each hypothetical conjugating unitary.

## Design notes

* Everything is stated for a general index type `n` with `Fintype n`, so the "odd dimension"
  hypothesis is `Odd (Fintype.card n)`; the Werner–Holevo application instantiates `n := Fin 3`
  (`Fintype.card (Fin 3) = 3` is odd).
* The polarization lemma is over an arbitrary `CommRing` (no division needed — only the two basis
  evaluations `eᵢ` and `eᵢ + eⱼ`); the determinant lemmas specialize to `ℂ` because they use that
  `2 ≠ 0` and `ℂ` has no zero divisors.
-/

open Matrix

namespace AxQM.Concrete

/-- **Polarization: a matrix with an identically-vanishing quadratic form is antisymmetric.** If
`ψ ⬝ᵥ M.mulVec ψ = 0` for every vector `ψ`, then `Mᵀ = −M`. Over any commutative ring: evaluating
at the standard basis vector `eᵢ` gives `Mᵢᵢ = 0`, and at `eᵢ + eⱼ` gives
`Mᵢᵢ + Mᵢⱼ + Mⱼᵢ + Mⱼⱼ = 0`, whence `Mᵢⱼ + Mⱼᵢ = 0`, i.e. `Mᵀ = −M`.

This is the first step of the Werner–Holevo counterexample of Nielsen & Chuang, Problem 8.3: the
pure-state evaluation forces `ψᵀ U ψ = ⟨ψ̄, U ψ⟩ = 0` for every `ψ`, so each conjugating unitary is
antisymmetric. -/
theorem transpose_eq_neg_of_forall_dotProduct_mulVec_self_eq_zero {n : Type*} [Fintype n]
    {R : Type*} [CommRing R] {M : Matrix n n R}
    (h : ∀ v : n → R, v ⬝ᵥ M.mulVec v = 0) : Mᵀ = -M := by
  classical
  -- The quadratic form evaluated at basis vectors reads off the entries of `M`.
  have hbasis : ∀ i j, (Pi.single i (1 : R)) ⬝ᵥ M.mulVec (Pi.single j 1) = M i j := by
    intro i j
    rw [dotProduct_mulVec, single_one_vecMul, dotProduct_single, mul_one, Matrix.row_apply]
  ext i j
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [mulVec_add, add_dotProduct, dotProduct_add, hbasis] at hij
  have hi : M i i = 0 := (hbasis i i).symm.trans (h (Pi.single i 1))
  have hj : M j j = 0 := (hbasis j j).symm.trans (h (Pi.single j 1))
  linear_combination hij - hi - hj

/-- **An antisymmetric matrix in odd dimension is singular.** If `Mᵀ = −M` and `Fintype.card n` is
odd, then `M.det = 0` (over `ℂ`). Proof: `det M = det Mᵀ = det (−M) = (−1)^card · det M = −det M`
(the card is odd), so `2 · det M = 0`, hence `det M = 0`.

This is the odd-dimension obstruction behind the Werner–Holevo counterexample of Nielsen & Chuang,
Problem 8.3. (The argument works over any field / integral domain of characteristic ≠ 2; it is
stated over `ℂ` here, the working ring of the counterexample.) -/
theorem det_eq_zero_of_transpose_eq_neg {n : Type*} [Fintype n] [DecidableEq n]
    (hn : Odd (Fintype.card n)) {M : Matrix n n ℂ} (hM : Mᵀ = -M) : M.det = 0 := by
  have h1 : M.det = -M.det :=
    calc M.det = Mᵀ.det := (Matrix.det_transpose M).symm
      _ = (-M).det := by rw [hM]
      _ = (-1) ^ Fintype.card n * M.det := Matrix.det_neg M
      _ = -M.det := by rw [hn.neg_one_pow, neg_one_mul]
  have h2 : (2 : ℂ) * M.det = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **An odd-dimensional complex matrix whose quadratic form vanishes identically is singular.** If
`ψ ⬝ᵥ M.mulVec ψ = 0` for every `ψ` and `Fintype.card n` is odd, then `M.det = 0`. The composition
of `transpose_eq_neg_of_forall_dotProduct_mulVec_self_eq_zero` (`M` is antisymmetric) and
`det_eq_zero_of_transpose_eq_neg` (odd antisymmetric ⟹ singular). -/
theorem det_eq_zero_of_forall_dotProduct_mulVec_self_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (hn : Odd (Fintype.card n)) {M : Matrix n n ℂ} (h : ∀ v : n → ℂ, v ⬝ᵥ M.mulVec v = 0) :
    M.det = 0 :=
  det_eq_zero_of_transpose_eq_neg hn
    (transpose_eq_neg_of_forall_dotProduct_mulVec_self_eq_zero h)

/-- **An odd-dimensional invertible matrix cannot have a vanishing
quadratic form.** If `Fintype.card n` is odd and `M.det` is invertible (`IsUnit M.det`) — in
particular for any unitary `M`, since a unitary matrix has `IsUnit M.det`
(`Matrix.UnitaryGroup.det_isUnit`) — then it is *not* the case that `ψ ⬝ᵥ M.mulVec ψ = 0` for all
`ψ`. Equivalently: no invertible odd-dimensional matrix is antisymmetric.

This is the fact the Werner–Holevo counterexample of Nielsen & Chuang, Problem 8.3, applies to each
conjugating unitary `Uₖ` of a hypothetical random-unitary representation: the pure-state evaluation
would force `ψᵀ Uₖ ψ = 0` for all `ψ`, impossible for the invertible `Uₖ` in odd dimension `3`. -/
theorem not_forall_dotProduct_mulVec_self_eq_zero_of_isUnit_det {n : Type*} [Fintype n]
    [DecidableEq n] (hn : Odd (Fintype.card n)) {M : Matrix n n ℂ} (hM : IsUnit M.det) :
    ¬ ∀ v : n → ℂ, v ⬝ᵥ M.mulVec v = 0 := fun h =>
  hM.ne_zero (det_eq_zero_of_forall_dotProduct_mulVec_self_eq_zero hn h)

end AxQM.Concrete
