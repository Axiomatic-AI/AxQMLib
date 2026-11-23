/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SymmetricTrotter
import AxQM.Postulates.API.ApproxError

/-!
# AxQM.Postulates.API — error of the symmetric (Strang) Trotter step (N&C Exercise 4.50)

Both parts of Nielsen & Chuang, Exercise 4.50, expressed in Box 4.1's *error* notation `E(U,V) =
‖U.op − V.op‖` (`Evolution.gateError`, N&C eq. 4.61). Writing a Hamiltonian as an ordered sum `H =
Σₖ Hₖ` of Hamiltonians (each an `Observable`), the symmetric (Strang) Trotter step is the
palindromic product of the component propagators (N&C eq. 4.106),

`U_Δt = e^{-iH₁Δt} ⋯ e^{-iH_LΔt} · e^{-iH_LΔt} ⋯ e^{-iH₁Δt}`  (`Observable.symmTrotterStep`).

* **(a)** `E(U_Δt, e^{-2iHΔt}) ≤ C·Δt³` — one symmetric step is a *third*-order approximation of the
  half-step-doubled evolution `e^{-2iHΔt} = H.propagator 1 0 (2Δt)`.
* **(b)** `E(U_Δtᵐ, e^{-2miHΔt}) ≤ m·α·Δt³` — repeating the step `m` times drifts from the exact
  long-time evolution `e^{-2miHΔt} = H.propagator 1 0 (2mΔt)` by at most `m` times the per-step
  error (N&C eq. 4.107).

## What this file provides

* `Observable.symmTrotterStep_gateError_le` — **Exercise 4.50(a)** in the `E(U,V)` notation: the
  third-order per-step bound `E(U_Δt, e^{-2iHΔt}) ≤ C·Δt³` for `Δt ∈ [0, 1]`.
* `Observable.symmTrotterStep_gateError_pow_le` — **Exercise 4.50(b)** (N&C eq. 4.107): the
  `m`-step bound `E(U_Δtᵐ, e^{-2miHΔt}) ≤ m·α·Δt³`, with `α` the per-step constant of part (a).

## Design notes

* **Part (a) is a restatement, not a re-proof.** The genuine `O(Δt³)` analysis is
  `Observable.exists_norm_symmTrotterStep_op_sub_propagator_op_le` (`SymmetricTrotter.lean`), whose
  conclusion `‖U_Δt.op − (H.propagator 1 0 (2Δt)).op‖ ≤ C·Δt³` *is* `E(U_Δt, e^{-2iHΔt}) ≤ C·Δt³` by
  the definition of `Evolution.gateError`. `symmTrotterStep_gateError_le` records this in Box 4.1's
  notation so part (b) reads uniformly in `E(·,·)`.
* **Part (b) is exactly N&C's Box 4.1 argument.** `Evolution.gateError_pow_le` (eqs. 4.63/4.69,
  `ApproxError.lean`) gives the linear error amplification `E(U_Δtᵐ, Vᵐ) ≤ m·E(U_Δt, V)` for the
  per-step target `V = e^{-2iHΔt}`; `Observable.propagator_pow` (`API/Evolution.lean`) identifies
  `Vᵐ = (e^{-2iHΔt})ᵐ` with the exact `e^{-2miHΔt}`; and part (a) bounds `E(U_Δt, V) ≤ C·Δt³`. Their
  composition is eq. 4.107 with `α = C`. No operator norm is manipulated here beyond the appeal to
  part (a).
* **Faithful, and general.** The statements take an *arbitrary* ordered decomposition `H = Σₖ Hₖ`
  (the `Hₖ` need not commute), the reusable content of Exercise 4.50; N&C's Pauli-string setting is
  the specialisation with `Hₖ` the Pauli-string Hamiltonians. No hypothesis is added and no
  dimension is fixed.
* **The decomposition hypothesis.** "`H = Σₖ Hₖ`" is expressed as
  `H.op = (Hs.map Observable.op).sum`, an equation of operators on `S.space`.

The statements of Exercise 4.50 are in `AxQM/NC/Ch4/Exercise4_50.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 4.50(a)**, stated in Box 4.1's error notation
`E(U,V) = ‖U.op − V.op‖` (`Evolution.gateError`). For a Hamiltonian decomposition `H = Σₖ Hₖ`
(`H.op = (Hs.map Observable.op).sum`), the symmetric (Strang) Trotter step
`U_Δt = Observable.symmTrotterStep Hs Δt` (the palindromic product of the component propagators, N&C
eq. 4.106) approximates the full half-step-doubled propagator `e^{-2iHΔt} = H.propagator 1 0 (2Δt)`
to *third* order: there is a constant `C ≥ 0` with `E(U_Δt, e^{-2iHΔt}) ≤ C·Δt³` for every
`Δt ∈ [0, 1]`.

This is the `E`-notation restatement of the propagator bound
`Observable.exists_norm_symmTrotterStep_op_sub_propagator_op_le` — the operator norm
`‖U_Δt.op − (H.propagator 1 0 (2Δt)).op‖` *is* `E(U_Δt, e^{-2iHΔt})` by definition of
`Evolution.gateError` — and it is the per-step bound that part (b) chains over `m` repetitions. -/
theorem Observable.symmTrotterStep_gateError_le
    (H : Observable S) (Hs : List (Observable S)) (hH : H.op = (Hs.map Observable.op).sum) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δt : ℝ, 0 ≤ Δt → Δt ≤ 1 →
      (Observable.symmTrotterStep Hs Δt).gateError (H.propagator 1 0 (2 * Δt)) ≤ C * Δt ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := Observable.exists_norm_symmTrotterStep_op_sub_propagator_op_le H Hs hH
  exact ⟨C, hC0, fun Δt hΔ0 hΔ1 => hC Δt hΔ0 hΔ1⟩

/-- **Nielsen & Chuang, Exercise 4.50(b)** (eq. 4.107). Running the symmetric Trotter step `m` times
approximates the exact long-time evolution `e^{-2miHΔt}` with an error that grows at most linearly
in `m`: for a Hamiltonian decomposition `H = Σₖ Hₖ` there is a constant `α ≥ 0` (the third-order
per-step constant of part (a)) with `E(U_Δtᵐ, e^{-2miHΔt}) ≤ m·α·Δt³` for every `m : ℕ` and
`Δt ∈ [0, 1]`, where `U_Δt = Observable.symmTrotterStep Hs Δt` and
`e^{-2miHΔt} = H.propagator 1 0 (2mΔt)`. (N&C's "positive integer `m`" is here stated for all
`m : ℕ`; the `m = 0` case is `0 ≤ 0` and the content is in `m ≥ 1`.)

This is N&C's Box 4.1 argument. `Evolution.gateError_pow_le` (Box 4.1 eqs. 4.63/4.69) gives the
linear error amplification `E(U_Δtᵐ, Vᵐ) ≤ m·E(U_Δt, V)` for the per-step target
`V = e^{-2iHΔt} = H.propagator 1 0 (2Δt)`; `Observable.propagator_pow` identifies `Vᵐ` with the
exact `e^{-2miHΔt} = H.propagator 1 0 (2mΔt)`; and part (a)
(`Observable.symmTrotterStep_gateError_le`) bounds the per-step error `E(U_Δt, V) ≤ C·Δt³`. Chaining
gives `≤ m·C·Δt³`, i.e. eq. 4.107 with `α = C`. -/
theorem Observable.symmTrotterStep_gateError_pow_le
    (H : Observable S) (Hs : List (Observable S)) (hH : H.op = (Hs.map Observable.op).sum) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (m : ℕ) (Δt : ℝ), 0 ≤ Δt → Δt ≤ 1 →
      (Observable.symmTrotterStep Hs Δt ^ m).gateError (H.propagator 1 0 (2 * (m : ℝ) * Δt))
        ≤ (m : ℝ) * α * Δt ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := Observable.symmTrotterStep_gateError_le H Hs hH
  refine ⟨C, hC0, fun m Δt hΔ0 hΔ1 => ?_⟩
  -- `e^{-2miHΔt}` is the `m`-th power of the per-step target `e^{-2iHΔt}` (propagator semigroup).
  have hpow : H.propagator 1 0 (2 * (m : ℝ) * Δt) = (H.propagator 1 0 (2 * Δt)) ^ m := by
    rw [show (2 : ℝ) * (m : ℝ) * Δt = (m : ℝ) * (2 * Δt) from by ring, ← Observable.propagator_pow]
  rw [hpow]
  calc (Observable.symmTrotterStep Hs Δt ^ m).gateError ((H.propagator 1 0 (2 * Δt)) ^ m)
      ≤ (m : ℝ) * (Observable.symmTrotterStep Hs Δt).gateError (H.propagator 1 0 (2 * Δt)) :=
        Evolution.gateError_pow_le _ _ m
    _ ≤ (m : ℝ) * (C * Δt ^ 3) := mul_le_mul_of_nonneg_left (hC Δt hΔ0 hΔ1) (Nat.cast_nonneg m)
    _ = (m : ℝ) * C * Δt ^ 3 := by ring

end AxQM
