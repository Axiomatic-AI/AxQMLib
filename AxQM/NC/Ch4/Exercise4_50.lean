/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SymmetricTrotterError

/-!
# Nielsen & Chuang, Exercise 4.50 — error of the symmetric (Strang) Trotter step

*(N&C p. 208.)*

For a Trotter step U_dt, prove U_dt=e^{-2iH dt}+O(dt^3) and bound error E(U^m,...).

`U_Δt` is the **palindromic** (Strang-symmetrised) product of the component propagators
`Hₖ.propagator 1 0 Δt = e^{-iHₖΔt}`, run in order and then in reverse. Symmetrising cancels the
second-order term, so one step approximates the full half-step-doubled evolution `e^{-2iHΔt}` to
*third* order (part a); Box 4.1's linear error-composition then bounds the drift of the `m`-step
circuit against the exact long-time evolution `e^{-2miHΔt}` (part b).

## The statements

Nielsen & Chuang measure how well a gate `V` approximates a gate `U` by the *error*
`E(U,V) = max_{|ψ⟩} ‖(U−V)|ψ⟩‖` (Box 4.1, eq. 4.61), which is the operator norm `‖U.op − V.op‖`. In
this notation "`U_Δt = e^{-2iHΔt} + O(Δt³)`" *is* `E(U_Δt, e^{-2iHΔt}) = O(Δt³)`, so both parts of
the exercise are `E(·,·)` bounds. Each is stated for an *arbitrary* Hamiltonian decomposition
`H = Σₖ Hₖ`, expressed by `H.op = (Hs.map Observable.op).sum` — and because there is no additive
structure on
`Observable`, that hypothesis is stated in terms of the operators `Observable.op`.
The statements are in `AxQM/Postulates/API/SymmetricTrotterError.lean`, listed below.

## The formalisation

Everything is at the `Evolution` level (a gate is a unitary `Evolution`; `E(U,V)` is
`Evolution.gateError`), as follows:

**Part (a)** — `AxQM/Postulates/API/SymmetricTrotterError.lean`:

* `Observable.symmTrotterStep_gateError_le` — the third-order per-step bound
  `E(U_Δt, e^{-2iHΔt}) ≤ C·Δt³` for `Δt ∈ [0, 1]`, the `E`-notation form of the propagator bound
  `Observable.exists_norm_symmTrotterStep_op_sub_propagator_op_le`
  (`AxQM/Postulates/API/SymmetricTrotter.lean`), whose `‖U_Δt.op − (H.propagator 1 0 (2Δt)).op‖`
  *is*
  `E(U_Δt, e^{-2iHΔt})` by definition of `Evolution.gateError`. Its genuine `O(Δt³)` analytic core
  is the Banach-algebra bound
  `NormedSpace.exists_norm_symmProd_exp_smul_sub_exp_two_smul_sum_le`
  (`ToMathlib/Analysis/Normed/Algebra/LieTrotter.lean`).

**Part (b)** — `AxQM/Postulates/API/SymmetricTrotterError.lean`:

* `Observable.symmTrotterStep_gateError_pow_le` — N&C eq. 4.107,
  `E(U_Δtᵐ, e^{-2miHΔt}) ≤ m·α·Δt³` for all `m : ℕ` and `Δt ∈ [0, 1]`, with `α = C` the per-step
  constant of part (a). This is exactly N&C's Box 4.1 argument, chaining:
  - `Evolution.gateError_pow_le` (`AxQM/Postulates/API/ApproxError.lean`) — Box 4.1 eqs. 4.63/4.69,
  the
    linear error amplification `E(U_Δtᵐ, Vᵐ) ≤ m·E(U_Δt, V)` for the per-step target
    `V = e^{-2iHΔt}`;
  - `Observable.propagator_pow` (`AxQM/Postulates/API/Evolution.lean`) — the propagator semigroup
  law
    `(e^{-2iHΔt})ᵐ = e^{-2miHΔt}`, identifying `Vᵐ` with the exact long-time evolution
    `H.propagator 1 0 (2mΔt)`;
  - part (a) for the per-step bound `E(U_Δt, V) ≤ C·Δt³`.

**Box 4.1 infrastructure** — `AxQM/Postulates/API/ApproxError.lean`: the error measure
`Evolution.gateError U V = ‖U.op − V.op‖` (eq. 4.61) and its chaining
(`Evolution.gateError_comp_le`, `gateError_prod_le`, `gateError_pow_le`, eqs. 4.63/4.69).

## Fidelity

No hypothesis is added and no dimension is fixed: the decomposition `H = Σₖ Hₖ` is arbitrary and the
`Hₖ` need not commute, exactly as in the exercise. N&C's literal setting (`H = Σ_g h_g g` over Pauli
strings, in the simulation algorithm of §4.7.2) is the specialisation with `Hₖ` the Pauli-string
Hamiltonians; the term count is absorbed into the constant `α`.
-/
