/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Telescoping bound on the difference of two list products

Let `𝔸` be a normed ring with `‖1‖ = 1`. Given two lists of elements whose entries all have norm at
most one — think of them as two sequences of gates, a *target* sequence and the *approximating*
sequence actually applied — the difference of their products is controlled by the sum of the
per-entry differences:

`‖(∏ⱼ aⱼ) − (∏ⱼ bⱼ)‖ ≤ ∑ⱼ ‖aⱼ − bⱼ‖`.

This is the **chaining inequality** for approximate quantum circuits: *the error of a sequence of
imperfect gates is at most the sum of the individual gate errors* (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Box 4.1, eq. (4.63); with the operator norm as the error
measure `E(U, V) = ‖U − V‖`, and unitaries satisfying `‖U‖ = 1`). It is the list-indexed companion
of the single-generator telescoping bound `norm_pow_sub_pow_le`.

The elements need not commute, so the proof is the direct cons-induction on the identity
`a₀ · A − b₀ · B = a₀ · (A − B) + (a₀ − b₀) · B`, bounding `‖a₀‖ ≤ 1` and `‖B‖ ≤ 1`.

## Main results

* `norm_listProd_le_one`: the product of a list of elements each of norm `≤ 1` again has norm `≤ 1`.
* `norm_listProd_sub_listProd_le`: the chaining inequality
  `‖(l.map Prod.fst).prod − (l.map Prod.snd).prod‖ ≤ (l.map fun p => ‖p.1 − p.2‖).sum`
  for a list `l` of (target, approximant) pairs whose entries all have norm `≤ 1`.
-/

@[expose] public section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- The product of a list of ring elements each of norm at most one has norm at most one. -/
theorem norm_listProd_le_one {l : List 𝔸} (h : ∀ x ∈ l, ‖x‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    calc ‖a * t.prod‖ ≤ ‖a‖ * ‖t.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 :=
          mul_le_mul (h a (by simp)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
            (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- **Chaining inequality for products** (Nielsen & Chuang eq. (4.63)). For a list `l` of pairs
whose components all have norm at most one, the norm of the difference of the two componentwise
products is bounded by the sum of the componentwise differences:
`‖(∏ⱼ (l j).1) − (∏ⱼ (l j).2)‖ ≤ ∑ⱼ ‖(l j).1 − (l j).2‖`.

Reading `(l j).1` as the target gate `Uⱼ` and `(l j).2` as the approximating gate `Vⱼ`, this says
the total error of a sequence of imperfect gates is at most the sum of the individual gate errors.
The factors need not commute. -/
theorem norm_listProd_sub_listProd_le (l : List (𝔸 × 𝔸))
    (h₁ : ∀ p ∈ l, ‖p.1‖ ≤ 1) (h₂ : ∀ p ∈ l, ‖p.2‖ ≤ 1) :
    ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ ≤ (l.map fun p => ‖p.1 - p.2‖).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hBle : ‖(t.map Prod.snd).prod‖ ≤ 1 := by
      apply norm_listProd_le_one
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact h₂ p (List.mem_cons_of_mem _ hp)
    have ha1 : ‖a.1‖ ≤ 1 := h₁ a (by simp)
    have iht := ih (fun p hp => h₁ p (List.mem_cons_of_mem _ hp))
                   (fun p hp => h₂ p (List.mem_cons_of_mem _ hp))
    have hkey : a.1 * (t.map Prod.fst).prod - a.2 * (t.map Prod.snd).prod
        = a.1 * ((t.map Prod.fst).prod - (t.map Prod.snd).prod)
          + (a.1 - a.2) * (t.map Prod.snd).prod := by rw [mul_sub, sub_mul]; abel
    calc ‖a.1 * (t.map Prod.fst).prod - a.2 * (t.map Prod.snd).prod‖
        = ‖a.1 * ((t.map Prod.fst).prod - (t.map Prod.snd).prod)
            + (a.1 - a.2) * (t.map Prod.snd).prod‖ := by rw [hkey]
      _ ≤ ‖a.1 * ((t.map Prod.fst).prod - (t.map Prod.snd).prod)‖
            + ‖(a.1 - a.2) * (t.map Prod.snd).prod‖ := norm_add_le _ _
      _ ≤ ‖a.1‖ * ‖(t.map Prod.fst).prod - (t.map Prod.snd).prod‖
            + ‖a.1 - a.2‖ * ‖(t.map Prod.snd).prod‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * (t.map fun p => ‖p.1 - p.2‖).sum + ‖a.1 - a.2‖ * 1 :=
          add_le_add (mul_le_mul ha1 iht (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hBle (norm_nonneg _))
      _ = ‖a.1 - a.2‖ + (t.map fun p => ‖p.1 - p.2‖).sum := by ring
