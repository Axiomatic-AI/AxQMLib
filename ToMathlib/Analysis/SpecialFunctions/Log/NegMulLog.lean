/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Additional lemmas about `Real.negMulLog`

The zero-set of `negMulLog` on `[0, ∞)`, the inverse and finite product/power expansions.
-/

@[expose] public section

namespace Real

/-- On `[0, ∞)` the function `negMulLog x = -x * log x` vanishes **exactly** at `x = 0` and `x = 1`
— the two roots of `-x log x`: at `x = 0` the factor `x` vanishes, at `x = 1` the factor `log x`
does, and elsewhere on `[0, ∞)` both factors are nonzero. (The hypothesis `0 ≤ x` rules out the
third root `x = -1` of `log`.) -/
theorem negMulLog_eq_zero {x : ℝ} (hx : 0 ≤ x) : negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  refine ⟨fun hz => ?_, fun h => h.elim (fun h => by rw [h, negMulLog_zero])
    (fun h => by rw [h, negMulLog_one])⟩
  simp only [negMulLog_eq_neg, neg_eq_zero, mul_eq_zero] at hz
  rcases hz with h | hlog
  · exact Or.inl h
  · rcases Real.log_eq_zero.mp hlog with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hx (by rw [h]; norm_num)

lemma negMulLog_inv (x : ℝ) : negMulLog x⁻¹ = x⁻¹ * Real.log x := by
  rw [negMulLog, Real.log_inv]
  ring

/-- Generalization of `negMulLog_mul` to a finite product: `negMulLog (∏ i ∈ s, f i)` expands as
a sum of `(∏ j ∈ s.erase i, f j) * negMulLog (f i)`. -/
lemma negMulLog_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    negMulLog (∏ i ∈ s, f i) =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * negMulLog (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, negMulLog_mul, ih, Finset.sum_insert ha,
      Finset.mul_sum, Finset.erase_insert ha]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi_ne_a : i ≠ a := fun h ↦ ha (h ▸ hi)
    have ha_notin_erase : a ∉ s.erase i := fun h ↦ ha (Finset.mem_of_mem_erase h)
    rw [Finset.erase_insert_of_ne hi_ne_a.symm, Finset.prod_insert ha_notin_erase, ← mul_assoc]

/-- Power-case companion to `negMulLog_prod`: `negMulLog (x^n)` expands as
`n * x^(n-1) * negMulLog x`. Derived directly via `pow_succ` induction (no
`DecidableEq` needed). Uses ℕ subtraction; at `n = 0` both sides are `0`. -/
lemma negMulLog_pow (x : ℝ) (n : ℕ) :
    negMulLog (x ^ n) = n * x ^ (n - 1) * negMulLog x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, negMulLog_mul, ih]
    cases n with
    | zero => simp
    | succ m => rw [Nat.succ_sub_one]; push_cast; ring

end Real
