/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelControlledIdentification

/-!
# Concrete: the §4.5.2 realisation of a two-level unitary, assembled at the matrix level

(Nielsen & Chuang §4.5.2, p. 191–193.)

The §4.5.2 realisation of a two-level unitary `U` (acting non-trivially only on two computational
basis states `|s⟩`, `|t⟩`) as a circuit has two stages: **walk a Gray code** to relocate the two
active states onto a bit-adjacent pair (a sequence of basis-state swaps), then apply a **controlled
single-qubit gate**, then undo the swaps. The junction
`swapConj_swapChain_grayCode_eq_ctrlSingleQubit` established that conjugating `U` by the Gray-code
swap chain produces, verbatim, a controlled single-qubit gate. This file assembles that into the
decomposition of `U` itself, and shows the swaps are themselves controlled single-qubit gates.

## The pieces

* `AxQM.Concrete.swap_eq_twoLevelEmbed_swapTwo` — a basis transposition is the two-level
  embedding of the elementary `2 × 2` swap:
  `Matrix.swap ℂ p q = twoLevelEmbed p q (Matrix.swap ℂ 0 1)` (`p ≠ q`).
* `AxQM.Concrete.swap_eq_ctrlSingleQubit` — **a bit-adjacent basis transposition is a
  controlled single-qubit gate.** For `differsInOneBit a b`, `Matrix.swap ℂ (enc a) (enc b)` equals
  `ctrlSingleQubit enc j c (Matrix.swap ℂ 0 1)` — the swap that shuffles the two active states is a
  controlled-`NOT` (the `2 × 2` block `Matrix.swap ℂ 0 1` is the `X`/`NOT` gate), so each swap of
  the Gray-code walk is one of the same family of controlled single-qubit gates as the final
  controlled-`Ũ`. Its block is unitary (`swapTwo_mem_unitaryGroup`).
* `AxQM.Concrete.swapConj_reverse_swapConj` — conjugating by the reversed list undoes
  conjugating by the list (`swapConj L.reverse (swapConj L U) = U`); the swaps are involutions, so
  the walk is invertible.
* `AxQM.Concrete.twoLevelUnitary_eq_swapConj_ctrlSingleQubit` — **the assembled
  decomposition**: a two-level unitary `U` supported on `{enc s, enc t}` (`s ≠ t`) *equals* the
  swap-conjugate (by the reversed Gray-code chain) of a controlled single-qubit gate
  `ctrlSingleQubit enc j c Ũ` with `Ũ` a `2 × 2` unitary. Combined with `swap_eq_ctrlSingleQubit`
  (each chain swap is itself a controlled single-qubit gate) this exhibits `U` as built entirely
  from controlled single-qubit gates — the §4.5.2 conclusion at the matrix level.

## Use

This is used in the §4.5.2 development of Exercise 4.43's `n`-qubit lift; the statement of
Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- The elementary `2 × 2` basis transposition `Matrix.swap ℂ 0 1` (the `X`/`NOT` gate) is
unitary. -/
theorem swapTwo_mem_unitaryGroup :
    Matrix.swap ℂ (0 : Fin 2) 1 ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (isTwoLevelUnitary_swap 0 1).1

/-- **A basis transposition is the two-level embedding of the elementary `2 × 2` swap.** For
`p ≠ q`, `Matrix.swap ℂ p q = twoLevelEmbed p q (Matrix.swap ℂ 0 1)`: placing the `2 × 2` swap
`!![0, 1; 1, 0]` into the `{p, q}` block reproduces the `d × d` transposition. -/
theorem swap_eq_twoLevelEmbed_swapTwo {p q : Fin d} (hpq : p ≠ q) :
    Matrix.swap ℂ p q = twoLevelEmbed p q (Matrix.swap ℂ (0 : Fin 2) 1) := by
  have s00 : Matrix.swap ℂ (0 : Fin 2) 1 0 0 = 0 := by
    rw [swap_apply_eq_one_row, Equiv.swap_apply_left]; exact Matrix.one_apply_ne (by decide)
  have s01 : Matrix.swap ℂ (0 : Fin 2) 1 0 1 = 1 := by
    rw [swap_apply_eq_one_row, Equiv.swap_apply_left]; exact Matrix.one_apply_eq _
  have s10 : Matrix.swap ℂ (0 : Fin 2) 1 1 0 = 1 := by
    rw [swap_apply_eq_one_row, Equiv.swap_apply_right]; exact Matrix.one_apply_eq _
  have s11 : Matrix.swap ℂ (0 : Fin 2) 1 1 1 = 0 := by
    rw [swap_apply_eq_one_row, Equiv.swap_apply_right]; exact Matrix.one_apply_ne (by decide)
  ext i j
  rw [swap_apply_eq_one_row, twoLevelEmbed_apply, s00, s01, s10, s11]
  rcases eq_or_ne i p with hip | hip
  · rw [hip, Equiv.swap_apply_left, ite_eq_left rfl]
    rcases eq_or_ne j p with hjp | hjp
    · rw [hjp, ite_eq_left rfl]; exact Matrix.one_apply_ne (Ne.symm hpq)
    · rw [ite_eq_right hjp]
      rcases eq_or_ne j q with hjq | hjq
      · rw [hjq, ite_eq_left rfl]; exact Matrix.one_apply_eq _
      · rw [ite_eq_right hjq]; exact Matrix.one_apply_ne (Ne.symm hjq)
  · rcases eq_or_ne i q with hiq | hiq
    · rw [ite_eq_right hip, hiq, Equiv.swap_apply_right, ite_eq_left rfl]
      rcases eq_or_ne j p with hjp | hjp
      · rw [hjp, ite_eq_left rfl]; exact Matrix.one_apply_eq _
      · rw [ite_eq_right hjp]
        rcases eq_or_ne j q with hjq | hjq
        · rw [hjq, ite_eq_left rfl]; exact Matrix.one_apply_ne hpq
        · rw [ite_eq_right hjq]; exact Matrix.one_apply_ne (Ne.symm hjp)
    · rw [ite_eq_right hip, ite_eq_right hiq, Equiv.swap_apply_of_ne_of_ne hip hiq]
      exact Matrix.one_apply

variable {m : ℕ}

/-- **A bit-adjacent basis transposition is a controlled single-qubit gate.** Fix an encoding
`enc : (Fin m → Fin 2) ≃ Fin d`. For bit-strings `a`, `b` differing in exactly one bit
(`differsInOneBit a b`), the basis transposition `Matrix.swap ℂ (enc a) (enc b)` equals a controlled
single-qubit gate `ctrlSingleQubit enc j c (Matrix.swap ℂ 0 1)` — a controlled-`NOT` with the target
on the single differing bit `j`. So each swap of the §4.5.2 Gray-code walk belongs to the same
family of controlled single-qubit gates as the final controlled-`Ũ`. -/
theorem swap_eq_ctrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) {a b : Fin m → Fin 2}
    (hab : differsInOneBit a b) :
    ∃ (j : Fin m) (c : Fin m → Fin 2),
      Matrix.swap ℂ (enc a) (enc b)
        = ctrlSingleQubit enc j c (Matrix.swap ℂ (0 : Fin 2) 1) := by
  obtain ⟨j, hj, hoff⟩ := hab
  refine ⟨j, a, ?_⟩
  have hne : a ≠ b := fun h => hj (by rw [h])
  have hencne : enc a ≠ enc b := enc.injective.ne hne
  rw [ctrlSingleQubit_eq_twoLevelEmbed]
  rcases update_zero_one_eq_pair hj hoff with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]; exact swap_eq_twoLevelEmbed_swapTwo hencne
  · rw [h0, h1, ← swap_eq_twoLevelEmbed_swapTwo hencne.symm]
    exact Matrix.swap_comm (enc a) (enc b)

/-- Conjugating `X` by the transposition `Matrix.swap ℂ p q` twice returns `X`: the swap is an
involution (`Matrix.swap_mul_self`), so the double conjugation collapses. -/
theorem swap_swap_conj (p q : Fin d) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.swap ℂ p q * (Matrix.swap ℂ p q * X * Matrix.swap ℂ p q) * Matrix.swap ℂ p q
      = X := by
  set s := Matrix.swap ℂ p q with hs_def
  have hs : s * s = 1 := by rw [hs_def]; exact Matrix.swap_mul_self p q
  have hre : s * (s * X * s) * s = s * s * X * (s * s) := by noncomm_ring
  rw [hre, hs, one_mul, mul_one]

/-- **Conjugating by the reversed list undoes conjugating by the list**:
`swapConj L.reverse (swapConj L U) = U`. Each basis transposition is an involution, so the reversed
Gray-code walk inverts the forward walk. This is what turns the junction (which conjugates `U`
into a controlled single-qubit gate) into a decomposition of `U` itself. -/
theorem swapConj_reverse_swapConj (L : List (Fin d × Fin d)) (U : Matrix (Fin d) (Fin d) ℂ) :
    swapConj L.reverse (swapConj L U) = U := by
  induction L with
  | nil => rfl
  | cons pq L ih =>
    rw [List.reverse_cons, swapConj_cons, swapConj_append, swapConj_cons, swapConj_nil,
      swap_swap_conj, ih]

/-- **The §4.5.2 decomposition of a two-level unitary, assembled.** A two-level unitary `U`
supported on `{enc s, enc t}` (`s ≠ t`) equals the swap-conjugate — by the *reversed* Gray chain —
of a controlled single-qubit gate `ctrlSingleQubit enc j c Ũ` with `Ũ` a `2 × 2` unitary:
`U = swapConj (swapChain ((grayCode s t).dropLast.map enc)).reverse (ctrlSingleQubit enc j c Ũ)`.
Chains the junction `swapConj_swapChain_grayCode_eq_ctrlSingleQubit` (which conjugates `U` into a
controlled single-qubit gate) with `swapConj_reverse_swapConj` (which inverts the conjugation).
Since each swap of the chain is itself a controlled single-qubit gate (`swap_eq_ctrlSingleQubit`),
this exhibits `U` as built entirely from controlled single-qubit gates — the §4.5.2 conclusion. -/
theorem twoLevelUnitary_eq_swapConj_ctrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d)
    {s t : Fin m → Fin 2} (hst : s ≠ t) {U : Matrix (Fin d) (Fin d) ℂ}
    (hunit : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ enc s ∧ i ≠ enc t) ∨ (j ≠ enc s ∧ j ≠ enc t) →
      U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    ∃ (j : Fin m) (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ),
      Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        U = swapConj (swapChain ((grayCode s t).dropLast.map enc)).reverse
              (ctrlSingleQubit enc j c Ũ) := by
  obtain ⟨j, c, Ũ, hŨ, heq⟩ :=
    swapConj_swapChain_grayCode_eq_ctrlSingleQubit enc hst hunit hsupp
  exact ⟨j, c, Ũ, hŨ, by rw [← heq, swapConj_reverse_swapConj]⟩

end AxQM.Concrete
