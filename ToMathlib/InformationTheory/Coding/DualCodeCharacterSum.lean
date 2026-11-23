/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.DualCode
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The character sum of a binary linear code and its dual

For a binary linear code `C ⊆ (ι → ZMod 2)` and a word `x`, the **character sum**
`∑_{y ∈ C} (-1)^{x · y}` (with `x · y` the standard dot product in `ZMod 2` and `(-1)^{·}` read as a
real number) is a dual-code indicator: it equals the number of codewords `|C|` when `x` is
orthogonal to every codeword — i.e. `x ∈ C⊥` — and vanishes otherwise (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 10.25, p. 450). This is the orthogonality relation
that turns the Hadamard-transformed CSS state (10.70) into a sum over the dual code `C₂⊥` (10.71),
the classical identity at the heart of CSS phase-flip correction.

## Main results

* `neg_one_pow_zmod2_val_add`: the sign map `a ↦ (-1)^{a.val}` on `ZMod 2` is an
  additive-to-multiplicative homomorphism, `(-1)^{(a+b).val} = (-1)^{a.val} · (-1)^{b.val}`. This is
  the special feature of `ZMod 2` (it fails for `ZMod n`, `n > 2`) that makes `y ↦ (-1)^{x·y}` a
  group character on `C`.
* `LinearCode.sum_neg_one_pow_dotProduct_of_mem_dual`: if `x ∈ C⊥` then every summand is `1`, so
  `∑_{y ∈ C} (-1)^{x·y} = |C|`.
* `LinearCode.sum_neg_one_pow_dotProduct_of_not_mem_dual`: if `x ∉ C⊥` then the sum vanishes,
  `∑_{y ∈ C} (-1)^{x·y} = 0`.
* `LinearCode.sum_neg_one_pow_dotProduct`: the two cases combined into the single indicator form
  `∑_{y ∈ C} (-1)^{x·y} = if x ∈ C⊥ then |C| else 0`.
* `LinearCode.sum_neg_one_pow_dotProduct_complex`: the same indicator identity with the signs taken
  in `ℂ` (with an explicit `[DecidablePred (· ∈ C)]` binder), for use where the codomain is `ℂ` —
  e.g. amplitudes of Hadamard-transformed CSS states.

## Implementation notes

The sum ranges over the subtype `↥C` of codewords (`∑ y : ↥C, …`), and `|C|` is `Nat.card ↥C`; the
`Fintype ↥C` instance needed to form the sum is supplied classically (`open scoped Classical`), as
submodule membership carries no decidability instance. The values `(-1)^{(x ⬝ᵥ y).val}` are taken in
`ℝ`, matching the real `±1` of the textbook; only the codomain being a characteristic-zero domain is
used, via the vanishing `2 ≠ 0` in the `x ∉ C⊥` case.

The `x ∉ C⊥` case is the classical character-orthogonality argument: `y ↦ (-1)^{x·y}` is a group
homomorphism `↥C → ℝˣ` (`neg_one_pow_zmod2_val_add` composed with additivity of the dot product),
and picking a codeword `y₀` with `x · y₀ = 1` gives a value `-1 ≠ 1`; translating the summation
index by `y₀` (a bijection of the group `↥C`) shows `(-1) · S = S`, whence `S = 0`.
-/

open Matrix

@[expose] public section

/-- On `ZMod 2` the **sign map** `a ↦ (-1)^{a.val}` is an additive-to-multiplicative homomorphism:
`(-1)^{(a+b).val} = (-1)^{a.val} · (-1)^{b.val}` in any ring `R`. This is special to `ZMod 2` — for
`ZMod n` with `n > 2` the exponent `a.val` is not additive mod `2` — and is exactly what makes
`y ↦ (-1)^{x·y}` a character on a binary linear code. The proof reduces the exponent
`(a+b).val = (a.val + b.val) % 2` and uses that `(-1)^{·}` depends only on the parity of the
exponent. -/
theorem neg_one_pow_zmod2_val_add {R : Type*} [Ring R] (a b : ZMod 2) :
    (-1 : R) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

namespace LinearCode

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **Character sum, orthogonal case** (Nielsen & Chuang, Exercise 10.25). If `x` lies in the dual
code `C⊥` — i.e. `x` is orthogonal to every codeword — then `(-1)^{x·y} = 1` for every `y ∈ C`, so
the character sum counts the codewords: `∑_{y ∈ C} (-1)^{x·y} = |C|`. -/
theorem sum_neg_one_pow_dotProduct_of_mem_dual
    (C : LinearCode (ZMod 2) ι) {x : ι → ZMod 2} (hx : x ∈ C.dual) :
    ∑ y : ↥C, (-1 : ℝ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val = (Nat.card ↥C : ℝ) := by
  have hone : ∀ y : ↥C, (-1 : ℝ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val = 1 := by
    intro y
    have hz : x ⬝ᵥ (y : ι → ZMod 2) = 0 := by
      rw [dotProduct_comm]; exact mem_dual_iff.1 hx _ y.2
    rw [hz, ZMod.val_zero, pow_zero]
  rw [Finset.sum_congr rfl (fun y _ => hone y)]
  simp [Finset.card_univ, Nat.card_eq_fintype_card]

open Classical in
/-- **Character sum, non-orthogonal case** (Nielsen & Chuang, Exercise 10.25). If `x` is *not* in
the dual code `C⊥`, then some codeword `y₀` has `x · y₀ = 1`, so the character `y ↦ (-1)^{x·y}` is a
nontrivial homomorphism on `C`; translating the summation index by `y₀` gives `(-1)·S = S`, hence
the character sum vanishes: `∑_{y ∈ C} (-1)^{x·y} = 0`. -/
theorem sum_neg_one_pow_dotProduct_of_not_mem_dual
    (C : LinearCode (ZMod 2) ι) {x : ι → ZMod 2} (hx : x ∉ C.dual) :
    ∑ y : ↥C, (-1 : ℝ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val = 0 := by
  rw [mem_dual_iff] at hx
  push Not at hx
  obtain ⟨z, hz, hznz⟩ := hx
  set y₀ : ↥C := ⟨z, hz⟩ with hy0
  set f : ↥C → ℝ := fun y => (-1 : ℝ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val with hf
  -- In `ZMod 2` a nonzero element is `1`, so `x · y₀ = 1` and the character takes the value `-1`.
  have hzmod : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hxy0 : x ⬝ᵥ (y₀ : ι → ZMod 2) = 1 := by
    rw [dotProduct_comm]; exact hzmod _ hznz
  have hf0 : f y₀ = -1 := by
    have hval : (x ⬝ᵥ (y₀ : ι → ZMod 2)).val = 1 := by rw [hxy0]; decide
    simp only [hf, hval, pow_one]
  -- `f` is a homomorphism from the additive group `↥C` to `ℝ`.
  have hom : ∀ a b : ↥C, f (a + b) = f a * f b := by
    intro a b
    simp only [hf, Submodule.coe_add, dotProduct_add]
    exact neg_one_pow_zmod2_val_add _ _
  set S := ∑ y : ↥C, f y with hS
  -- Translating the index by the fixed codeword `y₀` is a bijection of `↥C`, so `f y₀ * S = S`.
  have key : f y₀ * S = S := by
    rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft y₀) f]
    exact Finset.sum_congr rfl fun y _ => (hom y₀ y).symm
  rw [hf0] at key
  linarith [key]

open Classical in
/-- **Character sum of a binary linear code** (Nielsen & Chuang, Exercise 10.25, p. 450). For a
binary linear code `C` and a word `x`,
`∑_{y ∈ C} (-1)^{x·y} = |C|` if `x ∈ C⊥` and `= 0` otherwise. Combines the orthogonal and
non-orthogonal cases into the single dual-code indicator form. -/
theorem sum_neg_one_pow_dotProduct (C : LinearCode (ZMod 2) ι) (x : ι → ZMod 2) :
    ∑ y : ↥C, (-1 : ℝ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val
      = if x ∈ C.dual then (Nat.card ↥C : ℝ) else 0 := by
  by_cases hx : x ∈ C.dual
  · rw [ite_eq_left hx, sum_neg_one_pow_dotProduct_of_mem_dual C hx]
  · rw [ite_eq_right hx, sum_neg_one_pow_dotProduct_of_not_mem_dual C hx]

open Classical in
/-- **Complex character sum of a binary linear code** — the `ℂ`-valued companion of
`sum_neg_one_pow_dotProduct`: `∑_{y ∈ C} (-1)^{x·y} = |C|` if `x ∈ C⊥` and `= 0` otherwise, with
the signs taken in `ℂ`. Proved independently of the real version (rather than cast from it): the
explicit `[DecidablePred (· ∈ C)]` binder fixes the summation's `Fintype ↥C` instance to the
caller's, so callers can `rw` with it directly — a cast from the `open Classical` real
lemma would instead hit a `Fintype ↥C` instance mismatch. The `x ∉ C⊥` case is again character
orthogonality: `y ↦ (-1)^{x·y}` is a homomorphism `↥C → ℂ` with a value `-1`, so translating the
index by a witness `y₀` gives `(-1)·S = S`, whence `S = 0` (using `2 ≠ 0` in `ℂ`). -/
theorem sum_neg_one_pow_dotProduct_complex (C : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C)]
    (x : ι → ZMod 2) :
    ∑ y : ↥C, (-1 : ℂ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val
      = if x ∈ C.dual then (Nat.card ↥C : ℂ) else 0 := by
  by_cases hx : x ∈ C.dual
  · rw [ite_eq_left hx]
    have hone : ∀ y : ↥C, (-1 : ℂ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val = 1 := fun y => by
      have hz : x ⬝ᵥ (y : ι → ZMod 2) = 0 := by
        rw [dotProduct_comm]; exact mem_dual_iff.1 hx _ y.2
      rw [hz, ZMod.val_zero, pow_zero]
    rw [Finset.sum_congr rfl (fun y _ => hone y)]
    simp [Finset.card_univ, Nat.card_eq_fintype_card]
  · rw [ite_eq_right hx]
    rw [mem_dual_iff] at hx
    push Not at hx
    obtain ⟨z, hz, hznz⟩ := hx
    set y₀ : ↥C := ⟨z, hz⟩ with hy0
    set f : ↥C → ℂ := fun y => (-1 : ℂ) ^ (x ⬝ᵥ (y : ι → ZMod 2)).val with hf
    have hxy0 : x ⬝ᵥ (y₀ : ι → ZMod 2) = 1 := by
      rw [dotProduct_comm]; exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hznz
    have hf0 : f y₀ = -1 := by
      have hval : (x ⬝ᵥ (y₀ : ι → ZMod 2)).val = 1 := by rw [hxy0]; decide
      simp only [hf, hval, pow_one]
    have hom : ∀ a b : ↥C, f (a + b) = f a * f b := fun a b => by
      simp only [hf, Submodule.coe_add, dotProduct_add]
      exact neg_one_pow_zmod2_val_add _ _
    set S := ∑ y : ↥C, f y with hS
    have key : f y₀ * S = S := by
      rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft y₀) f]
      exact Finset.sum_congr rfl fun y _ => (hom y₀ y).symm
    rw [hf0] at key
    linear_combination (-1 / 2 : ℂ) * key

end LinearCode

end
