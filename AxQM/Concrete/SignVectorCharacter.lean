/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.LinearCombination

/-!
# Sign vectors and their character-orthogonality sum

Pure combinatorial mathematics supporting the
sign-unitary decomposition of the pinching map in `AxQM/Postulates/API/ProjectorPinching`
(Nielsen & Chuang, Exercise 11.20). A **sign vector** is an `ε : ι → Bool`, read as the `±1`-vector
`i ↦ sgnBool (ε i)`; the key fact is the **character-orthogonality** relation

`Σ_{ε : ι → Bool} (sgnBool εᵢ)(sgnBool εⱼ) = 2^|ι| · δᵢⱼ`

(`sum_sgnBool_mul_sgnBool`), the discrete analogue of orthogonality of the `±1` characters of
`(ℤ/2)^ι`. It is used in the construction in `AxQM/Postulates/API/ProjectorPinching`.
-/

open scoped BigOperators

namespace AxQM.Concrete

/-- The `±1` complex scalar of a boolean: `sgnBool true = 1`, `sgnBool false = -1`. It labels the
sign `εᵢ` of the `i`-th slot of a sign vector `ε : ι → Bool`. -/
def sgnBool (b : Bool) : ℂ := if b then 1 else -1

/-- A sign squares to one: `(±1)² = 1`. -/
theorem sgnBool_mul_self (b : Bool) : sgnBool b * sgnBool b = 1 := by cases b <;> simp [sgnBool]

/-- A `±1` sign is self-conjugate (real): `conj (±1) = ±1`. -/
theorem sgnBool_star (b : Bool) : star (sgnBool b) = sgnBool b := by cases b <;> simp [sgnBool]

variable {ι : Type*} [Fintype ι]

/-- **Character-orthogonality of the sign functions:**
`Σ_ε (sgnBool εᵢ)(sgnBool εⱼ) = if i = j then 2^|ι| else 0`, summing over all sign vectors
`ε : ι → Bool`. On the diagonal every summand is `(±1)² = 1`; off it (`i ≠ j`) flipping the `i`-th
coordinate (an involution of `ι → Bool`) negates the summand, so the sum equals its own negative and
vanishes. -/
theorem sum_sgnBool_mul_sgnBool [DecidableEq ι] (i j : ι) :
    ∑ ε : ι → Bool, sgnBool (ε i) * sgnBool (ε j)
      = if i = j then (Fintype.card (ι → Bool) : ℂ) else 0 := by
  classical
  by_cases hij : i = j
  · subst hij
    have hone : ∀ ε : ι → Bool, sgnBool (ε i) * sgnBool (ε i) = 1 :=
      fun ε => by cases (ε i) <;> simp [sgnBool]
    simp [hone, Finset.card_univ]
  · rw [ite_eq_right hij]
    -- flipping the `i`-th coordinate is a sign-negating involution
    let flip : (ι → Bool) → (ι → Bool) := fun ε => Function.update ε i (!(ε i))
    have hflip : ∀ ε, flip (flip ε) = ε := by
      intro ε; funext k
      by_cases hk : k = i
      · subst hk; simp [flip]
      · simp [flip, Function.update_of_ne hk]
    let e : (ι → Bool) ≃ (ι → Bool) := ⟨flip, flip, hflip, hflip⟩
    have hkey : ∀ ε, sgnBool ((flip ε) i) * sgnBool ((flip ε) j)
        = -(sgnBool (ε i) * sgnBool (ε j)) := by
      intro ε
      have h1 : (flip ε) i = !(ε i) := by simp [flip]
      have h2 : (flip ε) j = ε j := by simp [flip, Function.update_of_ne (Ne.symm hij)]
      rw [h1, h2]; cases (ε i) <;> cases (ε j) <;> simp [sgnBool]
    have hsum : (∑ ε : ι → Bool, sgnBool (ε i) * sgnBool (ε j))
        = ∑ ε : ι → Bool, sgnBool ((flip ε) i) * sgnBool ((flip ε) j) :=
      (Equiv.sum_comp e (fun ε => sgnBool (ε i) * sgnBool (ε j))).symm
    simp only [hkey, Finset.sum_neg_distrib] at hsum
    linear_combination ((1 : ℂ) / 2) * hsum

end AxQM.Concrete
