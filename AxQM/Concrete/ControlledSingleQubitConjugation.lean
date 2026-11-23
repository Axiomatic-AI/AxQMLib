/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.TwoLevelControlledDecomposition

/-!
# Concrete: control-pattern normalisation of a controlled single-qubit gate (N&C §4.3)

(Nielsen & Chuang §4.3, §4.5.2, p. 182–193 — the reduction of a controlled gate to single-qubit and
`CNOT` gates.)

The §4.5 decomposition (`Concrete/UnitaryControlledProduct.lean`) writes any register unitary as a
product of **controlled single-qubit gates** `ctrlSingleQubit enc j c Ũ` — apply `Ũ` to bit `j` when
the *other* bits match a control pattern `c`. Nielsen & Chuang's §4.3 reduces such a multiply-
controlled gate to a circuit of uncontrolled single-qubit gates on wires and `CNOT`s. The very first
move of that reduction is **control-pattern normalisation**: by conjugating a control wire with a
`NOT` gate, the value the control is conditioned on flips, so an arbitrary control pattern can be
brought to a canonical one (e.g. all controls conditioned on `1`). This file supplies that step at
the matrix level.

## The construction

Fix an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the `m`-bit strings as the `d = 2 ^ m` basis
indices. The `NOT` (`X`) gate on wire `k` is the uncontrolled single-qubit gate
`singleQubitOnWire enc k (Matrix.swap ℂ 0 1)` — already in the target gate family, unitary
(`singleQubitOnWire_mem_unitaryGroup` with `swapTwo_mem_unitaryGroup`), and an involution
(`singleQubitOnWire_swap_mul_self`).

* `AxQM.Concrete.flipWire enc k` — the basis-index involution that flips bit `k` of the
  encoded bit-string (`|enc x⟩ ↦ |enc x'⟩` with `x'` equal to `x` with bit `k` negated). The `X`-on-
  wire gate is exactly its permutation matrix (`singleQubitOnWire_swap_apply`).
* `AxQM.Concrete.singleQubitOnWire_swap_conj` — **conjugation by the `X`-on-wire gate is a
  reindexing.** `Wₖ * M * Wₖ = M.submatrix (flipWire enc k) (flipWire enc k)` for any `d × d` matrix
  `M`: sandwiching `M` between two `X`-on-wire gates permutes both indices by the wire-`k` flip. A
  reusable matrix identity (the analogue of `swap_conj_apply` for the wire-flip permutation).
* `AxQM.Concrete.ctrlSingleQubit_conj_singleQubitOnWire_swap` — **the headline: conjugating
  by the `X`-on-wire gate flips the control bit.** For `k ≠ j`,
  `Wₖ * ctrlSingleQubit enc j c Ũ * Wₖ = ctrlSingleQubit enc j (c[k ↦ ¬c k]) Ũ`: the controlled gate
  is unchanged except that the value control wire `k` is conditioned on is negated. Iterating this
  over the wires where `c` is `0` normalises any control pattern to all-`1` controls — the §4.3
  reduction's first step.

Used by the §4.3 reduction of Exercise 4.43's `n`-qubit lift; the statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The basis-index involution flipping bit `k`.** Relative to an encoding
`enc : (Fin m → Fin 2) ≃ Fin d`, it sends `|enc x⟩` to `|enc x'⟩` where `x'` is `x` with bit `k`
negated (`Equiv.swap 0 1`). It is exactly the permutation the `X`-on-wire gate
`singleQubitOnWire enc k (Matrix.swap ℂ 0 1)` realises (`singleQubitOnWire_swap_apply`). -/
def flipWire (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m) (i : Fin d) : Fin d :=
  enc (Function.update (enc.symm i) k (Equiv.swap 0 1 (enc.symm i k)))

/-- The bit-string underlying `flipWire enc k i` is `enc.symm i` with bit `k` negated. -/
theorem enc_symm_flipWire (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m) (i : Fin d) :
    enc.symm (flipWire enc k i)
      = Function.update (enc.symm i) k (Equiv.swap 0 1 (enc.symm i k)) := by
  rw [flipWire, Equiv.symm_apply_apply]

/-- **`flipWire enc k` is an involution.** Flipping bit `k` twice restores the original bit-string
(`Equiv.swap 0 1` is an involution), hence the original basis index. -/
theorem flipWire_involutive (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m) :
    Function.Involutive (flipWire enc k) := by
  intro i
  rw [flipWire, enc_symm_flipWire, Function.update_self, Equiv.swap_apply_self,
    Function.update_idem, Function.update_eq_self, Equiv.apply_symm_apply]

/-- **The `X`-on-wire gate is the wire-`k`-flip permutation matrix.** The entry of
`singleQubitOnWire enc k (Matrix.swap ℂ 0 1)` at `(i, a)` is `1` exactly when `a = flipWire enc k i`
(and `0` otherwise): it is the `0/1` permutation matrix of `flipWire enc k`. -/
theorem singleQubitOnWire_swap_apply (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m) (i a : Fin d) :
    singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) i a
      = if a = flipWire enc k i then 1 else 0 := by
  rw [singleQubitOnWire_apply]
  by_cases hoff : ∀ l, l ≠ k → enc.symm i l = enc.symm a l
  · rw [ite_eq_left hoff, swap_apply_eq_one_row, Matrix.one_apply]
    have hkey : (a = flipWire enc k i)
        ↔ (Equiv.swap 0 1 (enc.symm i k) = enc.symm a k) := by
      constructor
      · intro ha; rw [ha, enc_symm_flipWire, Function.update_self]
      · intro hP
        apply enc.symm.injective
        rw [enc_symm_flipWire]
        funext l
        rcases eq_or_ne l k with rfl | hl
        · rw [Function.update_self, hP]
        · rw [Function.update_of_ne hl, hoff l hl]
    by_cases hP : Equiv.swap 0 1 (enc.symm i k) = enc.symm a k
    · rw [ite_eq_left hP, ite_eq_left (hkey.mpr hP)]
    · rw [ite_eq_right hP, ite_eq_right (fun h => hP (hkey.mp h))]
  · rw [ite_eq_right hoff]
    have hne : ¬ (a = flipWire enc k i) := by
      intro ha
      apply hoff
      intro l hl
      rw [ha, enc_symm_flipWire, Function.update_of_ne hl]
    rw [ite_eq_right hne]

/-- **The `X`-on-wire gate is an involution**: `Wₖ * Wₖ = 1`. It is `singleQubitOnWire enc k`
applied to the involution `Matrix.swap ℂ 0 1`, and `singleQubitOnWire enc k` is a `*`-homomorphism
on the block. -/
theorem singleQubitOnWire_swap_mul_self (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m) :
    singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1)
        * singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) = 1 := by
  rw [singleQubitOnWire_mul, Matrix.swap_mul_self, singleQubitOnWire_one]

/-- **Conjugation by the `X`-on-wire gate reindexes both matrix indices by the wire-`k` flip.** For
any `d × d` matrix `M`, `Wₖ * M * Wₖ = M.submatrix (flipWire enc k) (flipWire enc k)`, where
`Wₖ = singleQubitOnWire enc k (Matrix.swap ℂ 0 1)`. Since `Wₖ` is a `0/1` permutation matrix
(`singleQubitOnWire_swap_apply`) of the involution `flipWire enc k` (`flipWire_involutive`),
sandwiching `M` between two copies permutes its rows and columns by that flip. This is the analogue
of `swap_conj_apply` for the wire-flip permutation, and the engine behind the control-bit flip. -/
theorem singleQubitOnWire_swap_conj (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) * M
        * singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1)
      = M.submatrix (flipWire enc k) (flipWire enc k) := by
  ext i i'
  rw [Matrix.submatrix_apply, Matrix.mul_apply]
  have hb0 : ∀ b ∈ (Finset.univ : Finset (Fin d)), b ≠ flipWire enc k i' →
      (singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) * M) i b
        * singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) b i' = 0 := by
    intro b _ hb
    have hbne : ¬ (i' = flipWire enc k b) := by
      intro h; exact hb (by rw [h, flipWire_involutive])
    rw [singleQubitOnWire_swap_apply, ite_eq_right hbne, mul_zero]
  rw [Finset.sum_eq_single (flipWire enc k i') hb0 (fun h => absurd (Finset.mem_univ _) h),
    singleQubitOnWire_swap_apply, flipWire_involutive, ite_eq_left rfl, mul_one, Matrix.mul_apply]
  have ha0 : ∀ a ∈ (Finset.univ : Finset (Fin d)), a ≠ flipWire enc k i →
      singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) i a * M a (flipWire enc k i') = 0 := by
    intro a _ ha
    rw [singleQubitOnWire_swap_apply, ite_eq_right ha, zero_mul]
  rw [Finset.sum_eq_single (flipWire enc k i) ha0 (fun h => absurd (Finset.mem_univ _) h),
    singleQubitOnWire_swap_apply, ite_eq_left rfl, one_mul]

/-- **Conjugating a controlled single-qubit gate by the `X`-on-wire gate flips its control bit.**
For a control wire `k ≠ j` (the target),
`Wₖ * ctrlSingleQubit enc j c Ũ * Wₖ = ctrlSingleQubit enc j (c[k ↦ ¬c k]) Ũ`, where
`Wₖ = singleQubitOnWire enc k (Matrix.swap ℂ 0 1)` and `c[k ↦ ¬c k]` is `c` with the value at bit
`k` negated (`Equiv.swap 0 1`). The controlled gate is unchanged except that the value control wire
`k` is conditioned on is flipped — N&C §4.3's control-pattern normalisation, one wire at a time.
Iterating over the wires where `c` is `0` brings any control pattern to all-`1` controls. -/
theorem ctrlSingleQubit_conj_singleQubitOnWire_swap (enc : (Fin m → Fin 2) ≃ Fin d)
    {j k : Fin m} (hkj : k ≠ j) (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) * ctrlSingleQubit enc j c Ũ
        * singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1)
      = ctrlSingleQubit enc j (Function.update c k (Equiv.swap 0 1 (c k))) Ũ := by
  rw [singleQubitOnWire_swap_conj]
  ext i i'
  rw [Matrix.submatrix_apply]
  simp only [ctrlSingleQubit, Matrix.of_apply, enc_symm_flipWire]
  have hjx : Function.update (enc.symm i) k (Equiv.swap 0 1 (enc.symm i k)) j = enc.symm i j :=
    Function.update_of_ne (Ne.symm hkj) _ _
  have hjx' : Function.update (enc.symm i') k (Equiv.swap 0 1 (enc.symm i' k)) j = enc.symm i' j :=
    Function.update_of_ne (Ne.symm hkj) _ _
  have hiff1 : (∀ l, l ≠ j → Function.update (enc.symm i) k (Equiv.swap 0 1 (enc.symm i k)) l
        = Function.update (enc.symm i') k (Equiv.swap 0 1 (enc.symm i' k)) l)
      ↔ (∀ l, l ≠ j → enc.symm i l = enc.symm i' l) := by
    constructor
    · intro h l hl
      have hl' := h l hl
      rcases eq_or_ne l k with rfl | hlk
      · rwa [Function.update_self, Function.update_self,
          (Equiv.swap (0 : Fin 2) 1).injective.eq_iff] at hl'
      · rwa [Function.update_of_ne hlk, Function.update_of_ne hlk] at hl'
    · intro h l hl
      rcases eq_or_ne l k with rfl | hlk
      · rw [Function.update_self, Function.update_self, h l hl]
      · rw [Function.update_of_ne hlk, Function.update_of_ne hlk]; exact h l hl
  have hiff2 : (∀ l, l ≠ j → Function.update (enc.symm i) k (Equiv.swap 0 1 (enc.symm i k)) l = c l)
      ↔ (∀ l, l ≠ j → enc.symm i l = Function.update c k (Equiv.swap 0 1 (c k)) l) := by
    constructor
    · intro h l hl
      have hl' := h l hl
      rcases eq_or_ne l k with rfl | hlk
      · rw [Function.update_self] at hl'
        rw [Function.update_self, ← hl', Equiv.swap_apply_self]
      · rw [Function.update_of_ne hlk] at hl'
        rw [Function.update_of_ne hlk]; exact hl'
    · intro h l hl
      have hl' := h l hl
      rcases eq_or_ne l k with rfl | hlk
      · rw [Function.update_self] at hl' ⊢
        rw [hl', Equiv.swap_apply_self]
      · rw [Function.update_of_ne hlk] at hl' ⊢
        exact hl'
  rw [hjx, hjx']
  exact if_congr hiff1 (if_congr hiff2 rfl rfl) rfl

end AxQM.Concrete
