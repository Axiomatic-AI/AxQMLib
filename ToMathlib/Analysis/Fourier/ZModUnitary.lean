/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import ToMathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.LinearAlgebra.UnitaryGroup
public import ToMathlib.Data.Real.Sqrt

/-!
# Unitarity of the discrete / quantum Fourier transform matrix

This file defines the symmetrically normalized discrete Fourier transform matrix on `ZMod N`
— the matrix underlying the *quantum Fourier transform* — and gives a direct proof that it is
unitary.

## Main definitions

* `ZMod.dftMatrix N` : the `N × N` complex matrix with entries
  `(dftMatrix N) j k = N⁻¹ᐟ² · exp (2πijk / N)`, indexed by `ZMod N`.  This is exactly the
  linear operator whose action on basis states is `|j⟩ ↦ N⁻¹ᐟ² ∑ₖ exp(2πijk/N) |k⟩`.

## Main statements

* `ZMod.sum_stdAddChar_mul` : the orthogonality relation
  `∑ₖ stdAddChar (m · k) = if m = 0 then N else 0`, the geometric-sum-of-roots-of-unity fact
  at the heart of the direct proof.
* `ZMod.dftMatrix_mem_unitaryGroup` : `dftMatrix N` is unitary, i.e. it lies in
  `Matrix.unitaryGroup (ZMod N) ℂ`.

The proof is direct: the `(j₁, j₂)` entry of `(dftMatrix N)ᴴ * dftMatrix N` is
`N⁻¹ ∑ₖ exp(2πi k (j₂ - j₁)/N)`, which is `1` when `j₁ = j₂` and `0` otherwise by the
orthogonality of the standard additive character `ZMod.stdAddChar`.
-/

@[expose] public section

open scoped BigOperators

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- **Orthogonality of the standard additive character.** For `m : ZMod N`, the sum
`∑ₖ stdAddChar (m · k)` equals `N` if `m = 0` and `0` otherwise. This is the `ZMod`-shaped
specialisation of the general primitive-character orthogonality `AddChar.sum_mulShift`
(`stdAddChar` is primitive by `ZMod.isPrimitive_stdAddChar`, and `Fintype.card (ZMod N) = N`
by `ZMod.card`). -/
theorem sum_stdAddChar_mul (m : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (m * k) = if m = 0 then (N : ℂ) else 0 := by
  simp_rw [mul_comm m]
  rw [AddChar.sum_mulShift m (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

/-- The symmetrically normalized discrete Fourier transform matrix on `ZMod N`, i.e. the
**quantum Fourier transform** matrix.  Its `(j, k)` entry is `N⁻¹ᐟ² · stdAddChar (j · k)`, and
since `stdAddChar (j · k) = exp (2πijk / N)` this is `N⁻¹ᐟ² · exp (2πijk / N)`, matching the
Nielsen & Chuang definition `|j⟩ ↦ N⁻¹ᐟ² ∑ₖ exp(2πijk/N) |k⟩`. -/
noncomputable def dftMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun j k => (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (j * k)

@[simp]
theorem dftMatrix_apply (j k : ZMod N) :
    dftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (j * k) := rfl

/-- **The quantum Fourier transform is unitary** (Nielsen & Chuang, Exercise 5.1). A direct proof
that the DFT matrix `dftMatrix N` lies in the unitary group: computing `(dftMatrix N)ᴴ *
dftMatrix N` entrywise reduces to the orthogonality relation `sum_stdAddChar_mul`. -/
theorem dftMatrix_mem_unitaryGroup (N : ℕ) [NeZero N] :
    dftMatrix N ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  have hcstar : star ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ := by
    rw [star_inv₀, ← starRingEnd_apply, Complex.conj_ofReal]
  have hstar : ∀ x : ZMod N, star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := fun x => by
    rw [AddChar.map_neg_eq_conj, starRingEnd_apply]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [Matrix.mem_unitaryGroup_iff']
  ext j₁ j₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ k : ZMod N,
      (star (dftMatrix N)) j₁ k * dftMatrix N k j₂
        = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) * ZMod.stdAddChar ((j₂ - j₁) * k) := by
    intro k
    rw [Matrix.star_apply, dftMatrix_apply, dftMatrix_apply, star_mul', hcstar, hstar,
      mul_mul_mul_comm, ← AddChar.map_add_eq_mul,
      show -(k * j₁) + k * j₂ = (j₂ - j₁) * k from by ring]
  simp_rw [key]
  rw [← Finset.mul_sum, sum_stdAddChar_mul]
  have hsqrt : (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N),
      Complex.ofReal_natCast]
  rw [hsqrt]
  rcases eq_or_ne j₁ j₂ with h | h
  · subst h
    rw [sub_self, ite_eq_left rfl, ite_eq_left rfl, inv_mul_cancel₀ hN]
  · rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm h)), ite_eq_right h, mul_zero]

end ZMod
