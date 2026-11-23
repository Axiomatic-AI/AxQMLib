/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import ToMathlib.Analysis.Normed.Algebra.LieTrotter

/-!
# AxQM.Postulates.API — the Trotter product formula for propagators (N&C Problem 4.3(4)(5))

The instantiation for propagators of parts (4) and (5) of Nielsen & Chuang,
Problem 4.3. Writing a Hamiltonian as a sum `H = Σᵢ Hᵢ` of Hamiltonians (each an `Observable`),
one approximates its propagator `exp(-i H Δ)` by the ordered product `∏ᵢ exp(-i Hᵢ Δ)` of the
component propagators:

* **(4)** the first-order (per-step) error is `O(Δ²)`:
  `‖(∏ᵢ exp(-i Hᵢ Δ)) - exp(-i H Δ)‖ ≤ C·Δ²`;
* **(5)** iterating `k` slices of size `Δ = 1/k` accumulates to an `O(1/k)` error:
  `‖(∏ᵢ exp(-i Hᵢ /k))ᵏ - exp(-i H)‖ ≤ C/k`, so `[∏ᵢ exp(-i Hᵢ Δ)]ᵏ → exp(-i H) = U`.

In this library the propagator is the `Evolution` `Observable.propagator H 1 0 t`
(`ℏ = 1`, from time `0` to `t`), whose operator is `exp(-i H.op t)` (N&C eq. 2.91,
`Observable.propagator_op`). Here `exp(-i H)` (`t = 1`) is the unitary `U` these formulas
approximate.

## What this file provides

* `Observable.propagator_op_one_zero` — the operator of the unit-`ℏ`, from-`0` propagator as a
  Lie–Trotter-shaped exponential: `(H.propagator 1 0 t).op = exp(t • (-i • H.op))`. The bridge
  from the physics propagator to the `exp(t • g)` form the Lie–Trotter lemmas are stated in.
* `Observable.exists_norm_prod_propagator_op_sub_propagator_op_le` — **Problem 4.3(4)**: for a
  Hamiltonian decomposition `H = Σᵢ Hᵢ` there is `C ≥ 0` with
  `‖(∏ᵢ (Hᵢ.propagator 1 0 Δ).op) - (H.propagator 1 0 Δ).op‖ ≤ C·Δ²` for every `Δ ∈ [0, 1]`.
* `Observable.exists_norm_prod_propagator_op_pow_sub_propagator_op_le` — **Problem 4.3(5)**: there
  is `C ≥ 0` with `‖(∏ᵢ (Hᵢ.propagator 1 0 (1/k)).op)ᵏ - (H.propagator 1 0 1).op‖ ≤ C/k` for every
  `k ≥ 1`; the right-hand propagator `(H.propagator 1 0 1).op = exp(-i H) = U`.

## Design notes

* **The operator algebra is itself the Banach algebra.** The continuous endomorphisms
  `S.space →L[ℂ] S.space` form a Banach algebra, so the Lie–Trotter error bounds
  (`NormedSpace.exists_norm_prod_exp_smul_sub_exp_smul_sum_le` and
  `NormedSpace.exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le`,
  `ToMathlib/Analysis/Normed/Algebra/LieTrotter.lean`) apply **directly** to the propagator
  operators — no matrix transport is needed. Taking the ordered generators `gᵢ = -i • Hᵢ.op`,
  the factor `exp(t • gᵢ)` is exactly `(Hᵢ.propagator 1 0 t).op` and `exp(t • Σ gᵢ)` is
  `(H.propagator 1 0 t).op` (using `H.op = Σᵢ Hᵢ.op`), so the abstract bound becomes the physics
  bound verbatim.
* **The trivial system.** A `QSystem` may have a zero-dimensional state space, in which case
  `‖1‖ = 0` and those lemmas' `NormOneClass` hypothesis fails. That case is handled separately:
  the operator ring `S.space →L[ℂ] S.space` is then a `Subsingleton`, every two operators are
  equal, and the bound holds trivially with `C = 0`.
* **A general Hamiltonian sum, specialising to Pauli strings.** N&C write `H = Σ_g h_g g` over the
  `4ⁿ` Pauli strings `g` and Trotterise that sum. The statements here take an *arbitrary* ordered
  decomposition `H = Σᵢ Hᵢ` of the Hamiltonian into Hamiltonians — the faithful, reusable physics
  content of (4)/(5) (Trotterising a Hamiltonian sum). N&C's literal form is the specialisation in
  which the `Hᵢ` are the Pauli-string Hamiltonians `h_g g` of the part-(2) expansion
  (`Observable.exists_real_pauliString_expansion`), so `H = i ln U` and the `4ⁿ` term count is
  absorbed into `C` (N&C's `O(4ⁿ Δ²)`/`O(4ⁿ Δ)`). Building each `h_g g` as an `Observable` on
  `qudit (2ⁿ)` from the matrix-level Pauli expansion (an operator↔matrix transport) is not
  formalised here; it does not change the physics captured here.

The statement of Problem 4.3 is in `AxQM/NC/Ch4/Problem4_3.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The operator of the unit-`ℏ`, from-time-`0` **propagator** written in Lie–Trotter form:
`(H.propagator 1 0 t).op = exp(t • (-i • H.op))`. Reading the physical exponent
`-i H.op (t - 0) / 1` (N&C eq. 2.91, `Observable.propagator_op`) as `t •` (a real scalar) times the
fixed generator `-i • H.op` puts the propagator into the `exp(t • g)` shape the Lie–Trotter
error bounds are stated in, which is what lets those bounds transfer to propagators verbatim. -/
theorem Observable.propagator_op_one_zero (H : Observable S) (t : ℝ) :
    (H.propagator 1 0 t).op = NormedSpace.exp (t • ((-Complex.I) • H.op)) := by
  rw [Observable.propagator_op, ← Complex.coe_smul, smul_smul]
  congr 2
  push_cast
  ring

/-- The **generators sum to the generator of the sum**: if a Hamiltonian is the ordered sum
`H = Σᵢ Hᵢ` (`H.op = (Hs.map Observable.op).sum`), then the Lie–Trotter generators `-i • Hᵢ.op`
sum to `-i • H.op`. This is the sum half of the bridge from a Hamiltonian decomposition to the
Lie–Trotter lemmas' `exp(t • Σᵢ gᵢ)`; both Trotter error bounds below use it to rewrite
`-i • H.op` as the sum of the generator list. -/
theorem Observable.sum_map_neg_I_smul_op {H : Observable S} {Hs : List (Observable S)}
    (hH : H.op = (Hs.map Observable.op).sum) :
    (Hs.map fun Hᵢ => (-Complex.I) • Hᵢ.op).sum = (-Complex.I) • H.op := by
  rw [hH, List.smul_sum, List.map_map]; rfl

/-- The **list of component propagator operators equals the list of Lie–Trotter factors**: for every
time `t`, `(Hᵢ.propagator 1 0 t).op = exp(t • (-i • Hᵢ.op))` factor by factor
(`Observable.propagator_op_one_zero`), so the two mapped lists agree. This is the product half of
the bridge from a Hamiltonian decomposition to the Lie–Trotter lemmas' `∏ᵢ exp(t • gᵢ)`; both
Trotter error bounds below use it to identify the product of component propagators with the
Lie–Trotter product. -/
theorem Observable.map_propagator_op_eq_map_exp_smul (Hs : List (Observable S)) (t : ℝ) :
    (Hs.map fun Hᵢ => (Hᵢ.propagator 1 0 t).op)
      = (Hs.map fun Hᵢ => (-Complex.I) • Hᵢ.op).map fun g => NormedSpace.exp (t • g) := by
  rw [List.map_map]
  exact List.map_congr_left fun Hᵢ _ => Hᵢ.propagator_op_one_zero t

/-- **Nielsen & Chuang, Problem 4.3(4): first-order Trotter error of a propagator.** If a
Hamiltonian `H` is a sum `H = Σᵢ Hᵢ` of Hamiltonians (`H.op = (Hs.map Observable.op).sum`, in the
list's order), then splitting its propagator `exp(-i H Δ)` into the ordered product
`∏ᵢ exp(-i Hᵢ Δ)` of the component propagators incurs only a second-order error: there is a
constant `C ≥ 0` (depending on the `Hᵢ`) with
`‖(∏ᵢ (Hᵢ.propagator 1 0 Δ).op) - (H.propagator 1 0 Δ).op‖ ≤ C·Δ²` for every `Δ ∈ [0, 1]`, even when
the `Hᵢ` do not commute.

This is the Banach-algebra bound
`NormedSpace.exists_norm_prod_exp_smul_sub_exp_smul_sum_le`, applied in the operator algebra
`S.space →L[ℂ] S.space` with generators `gᵢ = -i • Hᵢ.op`. Taking the `Hᵢ` to be the Pauli-string
Hamiltonians of N&C's part-(2) expansion recovers `exp(-iHΔ) = ∏_g exp(-i h_g g Δ) + O(4ⁿ Δ²)`. -/
theorem Observable.exists_norm_prod_propagator_op_sub_propagator_op_le
    (H : Observable S) (Hs : List (Observable S))
    (hH : H.op = (Hs.map Observable.op).sum) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ 1 →
      ‖(Hs.map fun Hᵢ => (Hᵢ.propagator 1 0 Δ).op).prod - (H.propagator 1 0 Δ).op‖
        ≤ C * Δ ^ 2 := by
  by_cases hnt : Nontrivial S.space
  · -- nontrivial space: `S.space →L[ℂ] S.space` is then a Banach algebra with `‖1‖ = 1`
    have := hnt
    obtain ⟨C, hC0, hC⟩ :=
      NormedSpace.exists_norm_prod_exp_smul_sub_exp_smul_sum_le
        (Hs.map fun Hᵢ => (-Complex.I) • Hᵢ.op)
    refine ⟨C, hC0, fun Δ hΔ0 hΔ1 => ?_⟩
    -- rewrite both sides into the Lie–Trotter shape via the shared bridge lemmas
    rw [Observable.map_propagator_op_eq_map_exp_smul, Observable.propagator_op_one_zero,
      ← Observable.sum_map_neg_I_smul_op hH]
    exact hC Δ hΔ0 hΔ1
  · -- trivial space: every operator equals every other, so the difference vanishes
    rw [not_nontrivial_iff_subsingleton] at hnt
    have := hnt
    refine ⟨0, le_rfl, fun Δ _ _ => ?_⟩
    rw [Subsingleton.elim (Hs.map fun Hᵢ => (Hᵢ.propagator 1 0 Δ).op).prod
      (H.propagator 1 0 Δ).op, sub_self, norm_zero]
    positivity

/-- **Nielsen & Chuang, Problem 4.3(5): accumulated Trotter error of the `k`-fold splitting.** If a
Hamiltonian `H` is a sum `H = Σᵢ Hᵢ` of Hamiltonians (`H.op = (Hs.map Observable.op).sum`), then
`k` iterations of the ordered product of the component propagators at step `Δ = 1/k` converge to the
full propagator `exp(-i H) = U` at first order: there is a constant `C ≥ 0` (depending on the `Hᵢ`)
with `‖(∏ᵢ (Hᵢ.propagator 1 0 (1/k)).op)ᵏ - (H.propagator 1 0 1).op‖ ≤ C/k` for every `k ≥ 1`.

This is the Banach-algebra bound
`NormedSpace.exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le`, applied in the operator algebra
`S.space →L[ℂ] S.space` with generators `gᵢ = -i • Hᵢ.op` (whose sum is `-i • H.op`, so
`exp(Σ gᵢ) = exp(-i H) = (H.propagator 1 0 1).op = U`). Taking the `Hᵢ` to be the Pauli-string
Hamiltonians of N&C's part-(2) expansion recovers `U = [∏_g exp(-i h_g g Δ)]ᵏ + O(4ⁿ Δ)`. -/
theorem Observable.exists_norm_prod_propagator_op_pow_sub_propagator_op_le
    (H : Observable S) (Hs : List (Observable S))
    (hH : H.op = (Hs.map Observable.op).sum) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖((Hs.map fun Hᵢ => (Hᵢ.propagator 1 0 (k : ℝ)⁻¹).op).prod) ^ k - (H.propagator 1 0 1).op‖
        ≤ C * (k : ℝ)⁻¹ := by
  by_cases hnt : Nontrivial S.space
  · have := hnt
    obtain ⟨C, hC0, hC⟩ :=
      NormedSpace.exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le
        (Hs.map fun Hᵢ => (-Complex.I) • Hᵢ.op)
    refine ⟨C, hC0, fun k hk => ?_⟩
    -- rewrite both sides into the Lie–Trotter shape via the shared bridge lemmas
    rw [Observable.map_propagator_op_eq_map_exp_smul, Observable.propagator_op_one_zero, one_smul,
      ← Observable.sum_map_neg_I_smul_op hH]
    exact hC k hk
  · rw [not_nontrivial_iff_subsingleton] at hnt
    have := hnt
    refine ⟨0, le_rfl, fun k _ => ?_⟩
    rw [Subsingleton.elim (((Hs.map fun Hᵢ => (Hᵢ.propagator 1 0 (k : ℝ)⁻¹).op).prod) ^ k)
      (H.propagator 1 0 1).op, sub_self, norm_zero]
    positivity

end AxQM
