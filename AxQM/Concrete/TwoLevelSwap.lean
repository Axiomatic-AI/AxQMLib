/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QFTTwoLevel
import Mathlib.LinearAlgebra.Matrix.Swap

/-!
# Concrete: the basis-transposition swap as a two-level unitary (N&C §4.5.2)

Nielsen & Chuang §4.5.2 (p. 191–193) realises an arbitrary two-level unitary on `n` qubits — one
acting non-trivially only on the two computational basis states `|s⟩` and `|t⟩` — as a circuit of
single-qubit and `CNOT` gates by *walking a Gray code* from `s` to `t`. Each one-bit step of the
code is a **swap** of two neighbouring basis states, performed by a (multiply-)controlled bit flip;
the swaps shuffle `|s⟩` next to `|t⟩`, a single controlled-`Ũ` acts, and the swaps are undone.

This file supplies the matrix-level engine of that swap stage: at the level of `d × d` complex
matrices, "swap the basis states `|p⟩` and `|q⟩`" is the **basis transposition** permutation matrix
`Matrix.swap ℂ p q`, and each Gray-code step conjugates the two-level unitary by one such swap. We
prove the two facts §4.5.2 uses:

* `isTwoLevelUnitary_swap` — the basis transposition `Matrix.swap ℂ p q` is itself a two-level
  unitary (it acts non-trivially only on `{p, q}`); it is the elementary swap the Gray-code walk is
  built from.
* `IsTwoLevelUnitary.swap_conj` — **conjugation by a basis transposition relocates the support**:
  if `U` is a two-level unitary with distinguished pair `{a, b}`, then
  `Matrix.swap ℂ p q * U * Matrix.swap ℂ p q` is again a two-level unitary, now with pair
  `{swap p q a, swap p q b}`. Iterating this along a Gray code moves the two active states
  until they differ in a single bit — the point at which the two-level unitary is a plain
  controlled single-qubit gate.

The workhorse is the entry-reindex identity `swap_conj_apply`:
`(Matrix.swap ℂ p q * U * Matrix.swap ℂ p q) i j = U (Equiv.swap p q i) (Equiv.swap p q j)`, i.e.
conjugation by the transposition permutes both the row and column indices by `Equiv.swap p q`. It is
derived from the one-sided reindex identities `swap_mul_apply_eq` / `mul_swap_apply_eq`, which
package Mathlib's pointwise `Matrix.swap_mul_apply_*` / `Matrix.mul_swap_apply_*` lemmas into a
single "multiply by a swap ↦ reindex by `Equiv.swap`" statement.

## Use

This is the shared swap lemma of the §4.5.2 two-level → single-qubit + `CNOT` reduction used by
Exercise 4.43's `n`-qubit lift; the statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **Left multiplication by a basis transposition reindexes the rows.** For any `d × d` matrix `A`,
`(Matrix.swap ℂ p q * A) a b = A (Equiv.swap p q a) b`: multiplying on the left by the transposition
of `p` and `q` permutes the row index by `Equiv.swap p q`. Packages the pointwise
`Matrix.swap_mul_apply_left/right/of_ne` lemmas into one reindex identity. -/
theorem swap_mul_apply_eq (A : Matrix (Fin d) (Fin d) ℂ) (p q a b : Fin d) :
    (Matrix.swap ℂ p q * A) a b = A (Equiv.swap p q a) b := by
  by_cases hap : a = p
  · subst hap; rw [Matrix.swap_mul_apply_left, Equiv.swap_apply_left]
  · by_cases haq : a = q
    · subst haq; rw [Matrix.swap_mul_apply_right, Equiv.swap_apply_right]
    · rw [Matrix.swap_mul_of_ne hap haq, Equiv.swap_apply_of_ne_of_ne hap haq]

/-- **Right multiplication by a basis transposition reindexes the columns.** For any `d × d` matrix
`A`, `(A * Matrix.swap ℂ p q) a b = A a (Equiv.swap p q b)`: multiplying on the right by the
transposition of `p` and `q` permutes the column index by `Equiv.swap p q`. Packages the pointwise
`Matrix.mul_swap_apply_left/right/of_ne` lemmas into one reindex identity. -/
theorem mul_swap_apply_eq (A : Matrix (Fin d) (Fin d) ℂ) (p q a b : Fin d) :
    (A * Matrix.swap ℂ p q) a b = A a (Equiv.swap p q b) := by
  by_cases hbp : b = p
  · subst hbp; rw [Matrix.mul_swap_apply_left, Equiv.swap_apply_left]
  · by_cases hbq : b = q
    · subst hbq; rw [Matrix.mul_swap_apply_right, Equiv.swap_apply_right]
    · rw [Matrix.mul_swap_of_ne hbp hbq, Equiv.swap_apply_of_ne_of_ne hbp hbq]

/-- Entry of a basis transposition, reindexed by rows: `Matrix.swap ℂ p q i j = 1 (swap p q i) j`.
The transposition matrix is the identity with its rows permuted by `Equiv.swap p q`. -/
theorem swap_apply_eq_one_row (p q i j : Fin d) :
    Matrix.swap ℂ p q i j = (1 : Matrix (Fin d) (Fin d) ℂ) (Equiv.swap p q i) j := by
  conv_lhs => rw [← Matrix.mul_one (Matrix.swap ℂ p q)]
  rw [swap_mul_apply_eq]

/-- Entry of a basis transposition, reindexed by columns:
`Matrix.swap ℂ p q i j = 1 i (swap p q j)`. The transposition matrix is the identity with its
columns permuted by `Equiv.swap p q`. -/
theorem swap_apply_eq_one_col (p q i j : Fin d) :
    Matrix.swap ℂ p q i j = (1 : Matrix (Fin d) (Fin d) ℂ) i (Equiv.swap p q j) := by
  conv_lhs => rw [← Matrix.one_mul (Matrix.swap ℂ p q)]
  rw [mul_swap_apply_eq]

/-- **The basis transposition `Matrix.swap ℂ p q` is a two-level unitary.** It is unitary — being a
self-inverse (`Matrix.swap_mul_self`), self-adjoint (`Matrix.conjTranspose_swap`) permutation
matrix — and it acts non-trivially only on the two basis states `{p, q}`: outside the
`{p,q} × {p,q}` block it agrees with the identity. This is the elementary swap the §4.5.2 Gray-code
walk is built from (the `p = q` case is the identity, still two-level). -/
theorem isTwoLevelUnitary_swap (p q : Fin d) : IsTwoLevelUnitary (Matrix.swap ℂ p q) := by
  refine ⟨?_, p, q, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_swap]
    exact Matrix.swap_mul_self p q
  · intro i j h
    rcases h with ⟨hip, hiq⟩ | ⟨hjp, hjq⟩
    · rw [swap_apply_eq_one_row, Equiv.swap_apply_of_ne_of_ne hip hiq]
    · rw [swap_apply_eq_one_col, Equiv.swap_apply_of_ne_of_ne hjp hjq]

/-- **Conjugating by a basis transposition reindexes both indices.**
`(Matrix.swap ℂ p q * U * Matrix.swap ℂ p q) i j = U (Equiv.swap p q i) (Equiv.swap p q j)`: the
transposition permutes the row and column indices of `U` by `Equiv.swap p q`. This is the matrix
identity behind "swap the basis states `|p⟩` and `|q⟩`" in the §4.5.2 circuit. -/
theorem swap_conj_apply (U : Matrix (Fin d) (Fin d) ℂ) (p q i j : Fin d) :
    (Matrix.swap ℂ p q * U * Matrix.swap ℂ p q) i j
      = U (Equiv.swap p q i) (Equiv.swap p q j) := by
  rw [mul_swap_apply_eq, swap_mul_apply_eq]

/-- **Conjugation by a basis transposition relocates the support — with explicit witnesses.** If `U`
is unitary and acts non-trivially only on the two basis states `{a, b}` (its entries outside the
`{a,b} × {a,b}` block agree with the identity), then `Matrix.swap ℂ p q * U * Matrix.swap ℂ p q` is
unitary and acts non-trivially only on `{Equiv.swap p q a, Equiv.swap p q b}` — the images of `a`
and `b` under the transposition. This is the explicit-support form of the swap-reduction step: the
distinguished pair is named, not merely existentially quantified. `IsTwoLevelUnitary.swap_conj` is
its existential repackaging, and folding it along a list gives
`AxQM.Concrete.swapConj_unitary_support`. -/
theorem swap_conj_support {U : Matrix (Fin d) (Fin d) ℂ} {a b : Fin d}
    (hunit : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b) →
      U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) (p q : Fin d) :
    Matrix.swap ℂ p q * U * Matrix.swap ℂ p q ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      ∀ i j : Fin d,
        (i ≠ Equiv.swap p q a ∧ i ≠ Equiv.swap p q b) ∨
            (j ≠ Equiv.swap p q a ∧ j ≠ Equiv.swap p q b) →
          (Matrix.swap ℂ p q * U * Matrix.swap ℂ p q) i j
            = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  refine ⟨mul_mem (mul_mem (isTwoLevelUnitary_swap p q).1 hunit)
    (isTwoLevelUnitary_swap p q).1, ?_⟩
  -- `x ≠ swap p q y ↔ swap p q x ≠ y`, the negation of Mathlib's `Equiv.swap_apply_eq_iff`.
  have hconv : ∀ x y : Fin d, x ≠ Equiv.swap p q y ↔ Equiv.swap p q x ≠ y :=
    fun _ _ => not_congr Equiv.swap_apply_eq_iff.symm
  intro i j h
  rw [swap_conj_apply, hsupp _ _ ?_]
  · simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
  · rcases h with ⟨hia, hib⟩ | ⟨hja, hjb⟩
    · exact Or.inl ⟨(hconv i a).mp hia, (hconv i b).mp hib⟩
    · exact Or.inr ⟨(hconv j a).mp hja, (hconv j b).mp hjb⟩

/-- **Conjugation by a basis transposition relocates the support of a two-level unitary.** If `U` is
a two-level unitary with distinguished pair `{a, b}`, then
`Matrix.swap ℂ p q * U * Matrix.swap ℂ p q` is again a two-level unitary, with distinguished pair
`{Equiv.swap p q a, Equiv.swap p q b}`. Walking
a Gray code — conjugating by one such swap per one-bit step — moves the two active basis states of a
two-level unitary until they differ in a single bit, at which point it is a controlled single-qubit
gate. This is the §4.5.2 swap-reduction step at the matrix level, the existential repackaging of
`swap_conj_support`. -/
theorem IsTwoLevelUnitary.swap_conj {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : IsTwoLevelUnitary U) (p q : Fin d) :
    IsTwoLevelUnitary (Matrix.swap ℂ p q * U * Matrix.swap ℂ p q) := by
  obtain ⟨hunit, a, b, hab⟩ := hU
  obtain ⟨hu, hs⟩ := swap_conj_support hunit hab p q
  exact ⟨hu, Equiv.swap p q a, Equiv.swap p q b, hs⟩

end AxQM.Concrete
