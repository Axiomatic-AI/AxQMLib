/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ProjectorHamiltonian
import AxQM.Postulates.API.Evolution

/-!
# Conjugation covariance of the projector-Hamiltonian propagator (N&C §6.2, Exercise 6.7)

The covariance law underlying **Figure 6.5** of Nielsen & Chuang, §6.2: the
propagator of a *transported* projector Hamiltonian is the conjugate of the original propagator.

For a state-preparation unitary `W` (an `Evolution S`) and a reference pure state `φ`, the
transported state is `W|φ⟩` (`W.evolvePure φ`), whose projector Hamiltonian generates the propagator
`exp(-i|Wφ⟩⟨Wφ|t)`. Because `|Wφ⟩⟨Wφ| = W|φ⟩⟨φ|W†` and conjugation by a unitary commutes with the
functional calculus, that propagator is exactly the `W`-conjugate of the reference propagator:

`exp(-i|Wφ⟩⟨Wφ|t) = W · exp(-i|φ⟩⟨φ|t) · W†`.

This is the identity that turns **Figure 6.4** (which implements `exp(-i|x⟩⟨x|Δt)` for a *marked*
reference state, via the marking oracle) into **Figure 6.5** (which implements `exp(-i|ψ⟩⟨ψ|Δt)` for
`ψ = W|0⟩` the uniform superposition of eq. 6.24, `W = H^{⊗n}` the Walsh–Hadamard state-preparation
transform): conjugate the reference circuit by the query-side state-preparation unitary. N&C's own
choice `ψ = H^{⊗n}|0⟩` (6.24) is the special case `W = H^{⊗n}`, `φ = |0⟩`.

## What is formalised

* `AxQM.PureState.projObservable_propagator_conj` — the covariance law
  `(W.evolvePure φ).projObservable.propagator 1 0 t`
  `= W.comp ((φ.projObservable.propagator 1 0 t).comp W.adjoint)`, an equality of `Evolution`s.

## Design

* **Proof.** The proof reduces to the propagator's closed form
  `PureState.projObservable_propagator_op_apply`
  (`exp(-i|φ⟩⟨φ|t) v = v + (e^{-it}-1)⟨φ,v⟩|φ⟩`), the unitary cancellation `W W† = 1`
  (`Evolution.comp_adjoint_self`), and the adjoint inner-product identity
  `⟨φ, W† v⟩ = ⟨W φ, v⟩` (`ContinuousLinearMap.adjoint_inner_right`) — no `exp`-conjugation lemma
  needed, since the closed form makes the conjugation a one-line vector computation.
* **Reuse.** This is general theory about `PureState.projObservable`, independent of the search
  oracle; it is applied to Figure 6.5 in Exercise 6.7 (`AxQM/NC/Ch6/Exercise6_7.lean`).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Conjugation covariance of the projector-Hamiltonian propagator** (Nielsen & Chuang, §6.2, the
identity behind Figure 6.5). For a state-preparation unitary `W` and a reference pure state `φ`, the
propagator of the transported projector Hamiltonian `|Wφ⟩⟨Wφ|` equals the `W`-conjugate of the
reference propagator:

`exp(-i|Wφ⟩⟨Wφ|t) = W · exp(-i|φ⟩⟨φ|t) · W†`.

The whole content is that `|Wφ⟩⟨Wφ| = W|φ⟩⟨φ|W†` and unitary conjugation commutes with the
functional calculus. The proof works vectorwise from the propagator's closed form
(`PureState.projObservable_propagator_op_apply`): applying `W · exp(-i|φ⟩⟨φ|t) · W†` to `v` gives
`v + (e^{-it}-1)⟨φ, W†v⟩ (Wφ)`, and `W W† = 1` together with `⟨φ, W†v⟩ = ⟨Wφ, v⟩` collapses this to
`v + (e^{-it}-1)⟨Wφ, v⟩ (Wφ) = exp(-i|Wφ⟩⟨Wφ|t) v`. This is the covariance step that turns the
Figure 6.4 circuit (for a marked reference state) into the Figure 6.5 circuit (for `ψ = W|0⟩`, the
uniform superposition of eq. 6.24, via `W = H^{⊗n}`). -/
theorem PureState.projObservable_propagator_conj (W : Evolution S) (φ : PureState S) (t : ℝ) :
    ((W.evolvePure φ).projObservable).propagator 1 0 t
      = W.comp (((φ.projObservable).propagator 1 0 t).comp W.adjoint) := by
  have hWW : ∀ v : S.space, W.op (ContinuousLinearMap.adjoint W.op v) = v := fun v => by
    rw [← ContinuousLinearMap.comp_apply, Evolution.comp_adjoint_self,
      one_apply_eq_self]
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.comp_op, Evolution.adjoint_op]
  ext v
  simp only [ContinuousLinearMap.comp_apply, PureState.projObservable_propagator_op_apply,
    map_add, map_smul, Evolution.evolvePure_vec, hWW, ContinuousLinearMap.adjoint_inner_right]

end AxQM
