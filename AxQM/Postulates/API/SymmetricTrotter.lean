/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TrotterProduct

/-!
# AxQM.Postulates.API — the symmetric (Strang) Trotter step (N&C Exercise 4.50(a))

Part (a) of Nielsen & Chuang, Exercise 4.50. Writing a
Hamiltonian as an ordered sum `H = Σₖ Hₖ` of Hamiltonians (each an `Observable`), the *symmetric*
(Strang) Trotter step is the **palindromic** product of the component propagators (N&C eq. 4.106),

`U_Δt = e^{-iH₁Δt} e^{-iH₂Δt} ⋯ e^{-iH_LΔt} · e^{-iH_LΔt} ⋯ e^{-iH₂Δt} e^{-iH₁Δt}`,

running the ordered propagators `Hₖ.propagator 1 0 Δt` immediately followed by the same factors in
reverse order. Symmetrising this way makes the second-order error cancel, so the step approximates
the full half-step-doubled propagator `e^{-2iHΔt}` to **third** order in `Δt` — one order better
than the unsymmetric splitting (`Postulates/API/TrotterProduct.lean`, `O(Δt²)`):

**(a)** `‖U_Δt.op - (H.propagator 1 0 (2Δt)).op‖ ≤ C·Δt³` for a constant `C ≥ 0`.

## What this file provides

* `Observable.symmTrotterStep` — the palindromic `Evolution` product `U_Δt` above.
* `Observable.symmTrotterStep_op` — its operator, the palindromic product of the component
  propagator operators.
* `Observable.exists_norm_symmTrotterStep_op_sub_propagator_op_le` — **N&C Exercise 4.50(a)**: the
  third-order bound `‖U_Δt.op - (H.propagator 1 0 (2Δt)).op‖ ≤ C·Δt³` for `Δt ∈ [0, 1]`.

## Design notes

* **The operator algebra is itself the Banach algebra.** As in `TrotterProduct.lean`, the
  continuous endomorphisms `S.space →L[ℂ] S.space` form a Banach algebra, so the symmetric
  Lie–Trotter bound `NormedSpace.exists_norm_symmProd_exp_smul_sub_exp_two_smul_sum_le`
  (`ToMathlib/Analysis/Normed/Algebra/LieTrotter.lean`) applies **directly** to the propagator
  operators with generators `gᵢ = -i • Hᵢ.op`. The palindromic operator product is exactly
  `(∏ exp(Δt•gᵢ)) · (∏ exp(Δt•gᵢ) reversed)` and `exp((2Δt) • Σ gᵢ) = exp((2Δt) • (-i • H.op))` is
  `(H.propagator 1 0 (2Δt)).op = e^{-2iHΔt}`, so the abstract bound becomes the physics bound.
  The lemmas (`Observable.propagator_op_one_zero`, `Observable.sum_map_neg_I_smul_op`,
  `Observable.map_propagator_op_eq_map_exp_smul`) are shared with `TrotterProduct.lean`.
* **The trivial system.** A `QSystem` may have a zero-dimensional state space, where `‖1‖ = 0` and
  the general lemma's `NormOneClass` hypothesis fails. That case is handled separately: the operator
  ring is then a `Subsingleton`, every two operators are equal, and the bound holds with `C = 0`.
* **A general Hamiltonian sum.** The statement takes an *arbitrary* ordered decomposition
  `H = Σₖ Hₖ` — the faithful, reusable content of 4.50(a). N&C's literal form (`H = Σ_g h_g g` over
  the `4ⁿ` Pauli strings) is the specialisation in which the `Hₖ` are the Pauli-string Hamiltonians;
  the term count is absorbed into `C`.

The statement of Exercise 4.50 is in `AxQM/NC/Ch4/Exercise4_50.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The symmetric (Strang) Trotter step** `U_Δt` (Nielsen & Chuang, Exercise 4.50, eq. 4.106).
Given a Hamiltonian decomposition into the list `Hs = [H₁, …, H_L]` (each an `Observable`) and a
step `Δt`, this is the **palindromic** `Evolution` product of the component propagators
`Hₖ.propagator 1 0 Δt = e^{-iHₖΔt}`: the ordered product `∏ₖ e^{-iHₖΔt}` immediately followed by the
same factors in reverse order, `∏ₖ e^{-iHₖΔt}` over `Hs.reverse`. As a product of unitaries it is
again a unitary `Evolution`. -/
def Observable.symmTrotterStep (Hs : List (Observable S)) (Δt : ℝ) : Evolution S :=
  (Hs.map fun Hₖ => Hₖ.propagator 1 0 Δt).prod
    * (Hs.reverse.map fun Hₖ => Hₖ.propagator 1 0 Δt).prod

/-- The operator of the symmetric Trotter step `U_Δt` is the palindromic product of the component
propagator operators: `U_Δt.op = (∏ₖ e^{-iHₖΔt}) · (∏ₖ e^{-iHₖΔt} reversed)`
(`Observable.symmTrotterStep`, `Evolution.op_prod`). -/
theorem Observable.symmTrotterStep_op (Hs : List (Observable S)) (Δt : ℝ) :
    (Observable.symmTrotterStep Hs Δt).op
      = (Hs.map fun Hₖ => (Hₖ.propagator 1 0 Δt).op).prod
        * (Hs.reverse.map fun Hₖ => (Hₖ.propagator 1 0 Δt).op).prod := by
  simp only [Observable.symmTrotterStep, Evolution.mul_def, Evolution.comp_op, Evolution.op_prod,
    List.map_map, Function.comp_def, ContinuousLinearMap.mul_def]

/-- **Nielsen & Chuang, Exercise 4.50(a): third-order error of the symmetric Trotter step.** If a
Hamiltonian `H` is an ordered sum `H = Σₖ Hₖ` of Hamiltonians (`H.op = (Hs.map Observable.op).sum`),
then the symmetric (Strang) Trotter step `U_Δt = Observable.symmTrotterStep Hs Δt` (the palindromic
product of the component propagators, N&C eq. 4.106) approximates the full half-step-doubled
propagator `e^{-2iHΔt} = (H.propagator 1 0 (2Δt)).op` to *third* order: there is a constant `C ≥ 0`
(depending on the `Hₖ`) with `‖U_Δt.op - (H.propagator 1 0 (2Δt)).op‖ ≤ C·Δt³` for every
`Δt ∈ [0, 1]`, even when the `Hₖ` do not commute.

This is the Banach-algebra bound
`NormedSpace.exists_norm_symmProd_exp_smul_sub_exp_two_smul_sum_le`, applied in the operator algebra
`S.space →L[ℂ] S.space` with generators `gᵢ = -i • Hᵢ.op`; the symmetrisation cancels the
second-order error, gaining an order over the unsymmetric splitting
(`Observable.exists_norm_prod_propagator_op_sub_propagator_op_le`, `O(Δt²)`). -/
theorem Observable.exists_norm_symmTrotterStep_op_sub_propagator_op_le
    (H : Observable S) (Hs : List (Observable S))
    (hH : H.op = (Hs.map Observable.op).sum) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δt : ℝ, 0 ≤ Δt → Δt ≤ 1 →
      ‖(Observable.symmTrotterStep Hs Δt).op - (H.propagator 1 0 (2 * Δt)).op‖ ≤ C * Δt ^ 3 := by
  by_cases hnt : Nontrivial S.space
  · -- nontrivial space: `S.space →L[ℂ] S.space` is then a Banach algebra with `‖1‖ = 1`
    have := hnt
    obtain ⟨C, hC0, hC⟩ :=
      NormedSpace.exists_norm_symmProd_exp_smul_sub_exp_two_smul_sum_le
        (Hs.map fun Hᵢ => (-Complex.I) • Hᵢ.op)
    refine ⟨C, hC0, fun Δt hΔ0 hΔ1 => ?_⟩
    have key := hC Δt hΔ0 hΔ1
    -- identify the physics products/exponential with the abstract ones via the shared bridge lemmas
    rw [Observable.symmTrotterStep_op, Observable.propagator_op_one_zero,
      ← Observable.sum_map_neg_I_smul_op hH,
      Observable.map_propagator_op_eq_map_exp_smul Hs Δt,
      Observable.map_propagator_op_eq_map_exp_smul Hs.reverse Δt, List.map_reverse]
    exact key
  · -- trivial space: every operator equals every other, so the difference vanishes
    rw [not_nontrivial_iff_subsingleton] at hnt
    have := hnt
    refine ⟨0, le_rfl, fun Δt _ _ => ?_⟩
    rw [Subsingleton.elim (Observable.symmTrotterStep Hs Δt).op (H.propagator 1 0 (2 * Δt)).op,
      sub_self, norm_zero]
    positivity

end AxQM
