/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Evolution
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# AxQM.Postulates.API — the gate-approximation error `E(U,V)` (N&C Box 4.1)

The form of Nielsen & Chuang's *error* measure for approximating one unitary
operation by another (Box 4.1, "Approximating quantum circuits", page 195; N&C eq. 4.61). If `U` is
the target evolution and `V` the one actually implemented, the error is

`E(U,V) ≡ max_{|ψ⟩} ‖(U - V)|ψ⟩‖`,   (4.61)

the largest deviation `V` produces from `U` over normalized states `|ψ⟩`. On a finite-dimensional
Hilbert space this maximum over the unit sphere is exactly the **operator norm** of `U - V` (it is
attained by compactness), so we formalize `E(U,V)` as `‖U.op - V.op‖` — a rigorous, reusable form of
4.61. `Evolution.gateError_apply_le` recovers the defining inequality `‖(U-V)ψ‖ ≤ E(U,V)` for every
normalized `ψ` (the `≥` half of "`E` is the max"); the operator norm being the *least* upper bound
is the `≤` half.

Box 4.1's key structural result — the one N&C's Exercise 4.50(b) instructs us to "use" — is that
approximation errors **add at most linearly** along a sequence of gates (N&C eqs. 4.63/4.69):

`E(Uₘ⋯U₁, Vₘ⋯V₁) ≤ Σⱼ E(Uⱼ, Vⱼ)`.   (4.63)

## What this file provides

* `Evolution.gateError` — `E(U,V) = ‖U.op - V.op‖`, N&C eq. 4.61.
* `Evolution.gateError_nonneg` / `_comm` / `_self` — basic properties (`E ≥ 0`, symm, `E(U,U)=0`).
* `Evolution.norm_op_le_one` — a unitary's operator has norm `≤ 1` (it is an isometry), in *every*
  system (including the trivial zero-dimensional one).
* `Evolution.gateError_apply_le` — the defining bound `‖U.op x - V.op x‖ ≤ E(U,V)·‖x‖` (N&C 4.61):
  `E(U,V)` dominates the per-state error, so it is the max over normalized states.
* `Evolution.gateError_comp_le` — **N&C eq. 4.69/4.73**, the two-gate case
  `E(U₂U₁, V₂V₁) ≤ E(U₂,V₂) + E(U₁,V₁)`.
* `Evolution.gateError_prod_le` — **N&C eq. 4.63**, the general chaining bound over a list of gate
  pairs, by induction from the two-gate case.
* `Evolution.gateError_prod_le_uniform` — the uniform-precision specialization `E(∏ Uⱼ, ∏ Vⱼ) ≤
  (length l)·Δ` when every gate is within `Δ`; the per-gate-precision → total-error-budget form used
  by Exercise 5.6.
* `Evolution.gateError_pow_le` — the `m`-fold repetition specialization `E(Uᵐ, Vᵐ) ≤ m·E(U,V)`, the
  form Exercise 4.50(b) applies to bound `E(U_Δtᵐ, e^{-2miHΔt})`.

## Design notes

* **The proof mirrors N&C's own.** Box 4.1 proves the chaining bound by handling the two-gate case
  (4.70–4.73) with the triangle inequality and unitary norm-preservation, then extends to `m` gates
  by induction. We do exactly that: `gateError_comp_le` is the two-gate base case (via
  `ContinuousLinearMap.opNorm_comp_le` and `Evolution.norm_op_le_one`), and `gateError_prod_le` /
  `gateError_pow_le` are the inductions. Because `‖U.op‖ ≤ 1` holds **unconditionally** (an isometry
  has operator norm `≤ 1`, and `0 ≤ 1` even on the trivial system), none of this needs a
  `NormOneClass` hypothesis or a trivial-space split — the development is uniform. (This is why
  we do not route through the Mathlib normed-ring bounds `norm_pow_sub_pow_le` /
  `norm_listProd_sub_listProd_le`, which require `NormOneClass` and would force a zero-dim split.)
* **A shared quantity.** `E(U,V)` is Box 4.1's error measure, referenced throughout the
  approximation theory of Chapter 4 and again in later chapters (e.g. Exercise 5.6's approximate-QFT
  error and Exercise A3.1's `D(U,V) = 2E(U,V)`).
* **Not covered.** Box 4.1's other bound, `|P_U - P_V| ≤ 2E(U,V)` on measurement-outcome
  probabilities (4.62/4.64–4.68), is a separate result about measurements; it is not needed for
  Exercise 4.50(b) (which uses only the chaining 4.63) and is not part of this file.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The gate-approximation error** `E(U,V)` (Nielsen & Chuang, Box 4.1, eq. 4.61). For a target
evolution `U` and an implemented evolution `V`, `E(U,V)` is the largest deviation `V` produces from
`U` over all normalized states, `max_{|ψ⟩} ‖(U-V)|ψ⟩‖`, which on a finite-dimensional Hilbert space
is exactly the operator norm `‖U.op - V.op‖`. -/
def Evolution.gateError (U V : Evolution S) : ℝ := ‖U.op - V.op‖

/-- The gate-approximation error is nonnegative (it is a norm). -/
theorem Evolution.gateError_nonneg (U V : Evolution S) : 0 ≤ U.gateError V :=
  norm_nonneg _

/-- The gate-approximation error is symmetric: `E(U,V) = E(V,U)`. -/
theorem Evolution.gateError_comm (U V : Evolution S) : U.gateError V = V.gateError U :=
  norm_sub_rev _ _

/-- A gate has zero error against itself: `E(U,U) = 0`. -/
@[simp]
theorem Evolution.gateError_self (U : Evolution S) : U.gateError U = 0 := by
  rw [Evolution.gateError, sub_self, norm_zero]

/-- A unitary evolution's operator is an isometry, hence has operator norm `≤ 1`. This holds in
every system, including a trivial (zero-dimensional) one where the norm is `0 ≤ 1`. -/
theorem Evolution.norm_op_le_one (U : Evolution S) : ‖U.op‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound U.op zero_le_one (fun x => ?_)
  rw [one_mul]
  exact le_of_eq (U.norm_op_apply x)

/-- **The defining bound of `E(U,V)`** (Nielsen & Chuang, eq. 4.61): the error dominates the
deviation `‖U.op x - V.op x‖` on every vector `x` (scaled by `‖x‖`). In particular
`‖U.op ψ - V.op ψ‖ ≤ E(U,V)` for every normalized `ψ` — so `E(U,V)` is an upper bound for, and (as
the operator norm, the least such) equals, the maximum over normalized states in 4.61. -/
theorem Evolution.gateError_apply_le (U V : Evolution S) (x : S) :
    ‖U.op x - V.op x‖ ≤ U.gateError V * ‖x‖ := by
  rw [Evolution.gateError, ← sub_apply]
  exact (U.op - V.op).le_opNorm x

/-- **Nielsen & Chuang, Box 4.1, eq. 4.69/4.73: the two-gate chaining bound.** The error of a
product of two gates is at most the sum of the errors of the factors:
`E(U₂U₁, V₂V₁) ≤ E(U₂,V₂) + E(U₁,V₁)`. This is N&C's base case (4.70–4.73): write
`U₂U₁ - V₂V₁ = (U₂ - V₂)U₁ + V₂(U₁ - V₁)`, apply the triangle inequality, and use that `U₁`, `V₂`
are norm-non-increasing (`Evolution.norm_op_le_one`). -/
theorem Evolution.gateError_comp_le (U₁ U₂ V₁ V₂ : Evolution S) :
    (U₂ * U₁).gateError (V₂ * V₁) ≤ U₂.gateError V₂ + U₁.gateError V₁ := by
  simp only [Evolution.gateError, Evolution.mul_def, Evolution.comp_op]
  have hsplit : U₂.op.comp U₁.op - V₂.op.comp V₁.op
      = (U₂.op - V₂.op).comp U₁.op + V₂.op.comp (U₁.op - V₁.op) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [hsplit]
  calc ‖(U₂.op - V₂.op).comp U₁.op + V₂.op.comp (U₁.op - V₁.op)‖
      ≤ ‖(U₂.op - V₂.op).comp U₁.op‖ + ‖V₂.op.comp (U₁.op - V₁.op)‖ := norm_add_le _ _
    _ ≤ ‖U₂.op - V₂.op‖ * ‖U₁.op‖ + ‖V₂.op‖ * ‖U₁.op - V₁.op‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖U₂.op - V₂.op‖ * 1 + 1 * ‖U₁.op - V₁.op‖ :=
        add_le_add (mul_le_mul_of_nonneg_left U₁.norm_op_le_one (norm_nonneg _))
          (mul_le_mul_of_nonneg_right V₂.norm_op_le_one (norm_nonneg _))
    _ = ‖U₂.op - V₂.op‖ + ‖U₁.op - V₁.op‖ := by rw [mul_one, one_mul]

/-- **Nielsen & Chuang, Box 4.1, eq. 4.63: the general chaining bound.** For a sequence of gate
pairs `(Uⱼ, Vⱼ)` (a list `l`), the error of approximating the ordered product `∏ Uⱼ` by `∏ Vⱼ` is at
most the sum of the individual errors: `E(∏ Uⱼ, ∏ Vⱼ) ≤ Σⱼ E(Uⱼ, Vⱼ)`. Proved by induction on `l`
from the two-gate case `Evolution.gateError_comp_le`. -/
theorem Evolution.gateError_prod_le (l : List (Evolution S × Evolution S)) :
    (l.map Prod.fst).prod.gateError (l.map Prod.snd).prod
      ≤ (l.map fun p => p.1.gateError p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    calc (p.1 * (l.map Prod.fst).prod).gateError (p.2 * (l.map Prod.snd).prod)
        ≤ p.1.gateError p.2 + (l.map Prod.fst).prod.gateError (l.map Prod.snd).prod :=
          Evolution.gateError_comp_le _ _ _ _
      _ ≤ p.1.gateError p.2 + (l.map fun p => p.1.gateError p.2).sum := by linarith [ih]

/-- **The uniform-precision chaining bound.** If every gate of a circuit `l` is implemented to a
common precision `Δ` — `E(Uⱼ, Vⱼ) ≤ Δ` for each pair — then the whole-circuit error is at most the
number of gates times that precision: `E(∏ Uⱼ, ∏ Vⱼ) ≤ (length l)·Δ`. This is the form in which
Nielsen & Chuang's chaining bound (eq. 4.63) is used to turn a per-gate precision into a total-error
budget (e.g. Exercise 5.6's approximate quantum Fourier transform). Obtained from
`Evolution.gateError_prod_le` by bounding the sum of the (nonnegatively many) gate errors by
`length l • Δ` (`List.sum_le_card_nsmul`). -/
theorem Evolution.gateError_prod_le_uniform (l : List (Evolution S × Evolution S)) (Δ : ℝ)
    (h : ∀ p ∈ l, p.1.gateError p.2 ≤ Δ) :
    (l.map Prod.fst).prod.gateError (l.map Prod.snd).prod ≤ (l.length : ℝ) * Δ := by
  calc (l.map Prod.fst).prod.gateError (l.map Prod.snd).prod
      ≤ (l.map fun p => p.1.gateError p.2).sum := Evolution.gateError_prod_le l
    _ ≤ l.length • Δ := by
        have hb := List.sum_le_length_nsmul (l.map fun p => p.1.gateError p.2) Δ (by
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact h p hp)
        rwa [List.length_map] at hb
    _ = (l.length : ℝ) * Δ := nsmul_eq_mul _ _

/-- **The `m`-fold repetition bound** `E(Uᵐ, Vᵐ) ≤ m·E(U,V)` (the constant-sequence case of Nielsen
& Chuang's chaining eq. 4.63). Repeating a gate `m` times amplifies the approximation error by at
most a factor of `m`. This is the form Exercise 4.50(b) uses to bound `E(U_Δtᵐ, e^{-2miHΔt})`.
Proved by induction on `m` from the two-gate case `Evolution.gateError_comp_le`. -/
theorem Evolution.gateError_pow_le (U V : Evolution S) (m : ℕ) :
    (U ^ m).gateError (V ^ m) ≤ m * U.gateError V := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    calc (U * U ^ n).gateError (V * V ^ n)
        ≤ U.gateError V + (U ^ n).gateError (V ^ n) := Evolution.gateError_comp_le _ _ _ _
      _ ≤ U.gateError V + n * U.gateError V := by linarith [ih]
      _ = (↑(n + 1) : ℝ) * U.gateError V := by push_cast; ring

end AxQM
