/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution

/-!
# AxQM.Postulates.API — the projector Hamiltonian and its propagator

This file treats the **quantum-search-as-simulation** program of Nielsen & Chuang, §6.2 (and
Exercise 6.7): the rank-one *projector Hamiltonian* `H = |ψ⟩⟨ψ|`, and the closed form of the unitary
it generates.

For a pure state `ψ`, `|ψ⟩⟨ψ|` is a self-adjoint operator, hence an `Observable` — a legitimate
Hamiltonian (N&C eq. 6.18 takes `H = |x⟩⟨x| + |ψ⟩⟨ψ|`, a sum of two such projectors). Its
time-evolution operator `exp(-i|ψ⟩⟨ψ|t)` has the closed form

`exp(-i|ψ⟩⟨ψ|t) = I + (e^{-it} - 1)|ψ⟩⟨ψ|`,

which follows purely from the idempotence `|ψ⟩⟨ψ|² = |ψ⟩⟨ψ|` (lemma
`NormedSpace.exp_smul_of_mul_self_eq_self`): the propagator fixes every state orthogonal to `|ψ⟩`
and multiplies the `|ψ⟩` component by the phase `e^{-it}`.

## What is formalised

* `AxQM.PureState.projObservable ψ` — the projector Hamiltonian `|ψ⟩⟨ψ|` packaged as an
  `Observable`. An `Observable` bundles self-adjointness; producing this term discharges that
  obligation (`|ψ⟩⟨ψ|† = |ψ⟩⟨ψ|`).
* `AxQM.PureState.projObservable_op` — its operator form `|ψ⟩⟨ψ| = rankOne ℂ ψ.vec ψ.vec`.
* `AxQM.PureState.projObservable_propagator_op` — **the target operator of N&C Exercise
  6.7**: `exp(-i|ψ⟩⟨ψ|t) = I + (e^{-it} - 1)|ψ⟩⟨ψ|`, i.e.
  `(ψ.projObservable.propagator 1 0 t).op = 1 + (Complex.exp (-(I*t)) - 1) • rankOne ℂ ψ.vec ψ.vec`.
* `AxQM.PureState.projObservable_propagator_op_apply` — the same, applied to a vector `v`:
  `exp(-i|ψ⟩⟨ψ|t) v = v + (e^{-it} - 1)⟨ψ, v⟩ |ψ⟩` — the propagator leaves `v` unchanged apart from
  a phase on its `|ψ⟩` component, the "rotation of `|ψ⟩` towards `|x⟩`" of N&C §6.2 made exact.

## The proof

The whole content of the closed form is the Euler formula for an
  idempotent, `NormedSpace.exp (z • a) = 1 + (Complex.exp z - 1) • a` for `a * a = a`
  (`ToMathlib/Analysis/Normed/Algebra/ExponentialInvolution.lean`), specialised to the idempotent
  rank-one projector `a = |ψ⟩⟨ψ|` (idempotent since `⟨ψ, ψ⟩ = 1`) and `z = -it`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The projector Hamiltonian** `H = |ψ⟩⟨ψ|` of a pure state `ψ`, as an `Observable`. The rank-one
projector `|ψ⟩⟨ψ| = rankOne ℂ ψ.vec ψ.vec` is self-adjoint (`|ψ⟩⟨ψ|† = |ψ⟩⟨ψ|`, from
`adjoint_rankOne`), so it is a legitimate observable (Postulate 2). This is the elementary
Hamiltonian whose simulation drives quantum search: Nielsen & Chuang, §6.2, takes
`H = |x⟩⟨x| + |ψ⟩⟨ψ|` (eq. 6.18), a sum of two such projectors, and Exercise 6.7 simulates each
summand `exp(-i|x⟩⟨x|Δt)`, `exp(-i|ψ⟩⟨ψ|Δt)` by a quantum circuit. -/
def PureState.projObservable (ψ : PureState S) : Observable S where
  op := rankOne ℂ ψ.vec ψ.vec
  selfAdjoint := by rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- The underlying operator of the projector Hamiltonian `|ψ⟩⟨ψ|` is `rankOne ℂ ψ.vec ψ.vec`. -/
@[simp]
theorem PureState.projObservable_op (ψ : PureState S) :
    (ψ.projObservable).op = rankOne ℂ ψ.vec ψ.vec := rfl

/-- **The projector-Hamiltonian propagator** `exp(-i|ψ⟩⟨ψ|t) = I + (e^{-it} - 1)|ψ⟩⟨ψ|`
(Nielsen & Chuang, §6.2 — the operator that Exercise 6.7's circuits implement, for `H = |x⟩⟨x|` or
`H = |ψ⟩⟨ψ|`). With `ℏ = 1` and elapsed time `t`, the unit propagator of the projector Hamiltonian
`|ψ⟩⟨ψ|` (`ψ.projObservable`) equals `1 + (e^{-it} - 1)|ψ⟩⟨ψ|` at the operator level. The proof is
the idempotence of the rank-one projector (`|ψ⟩⟨ψ|² = |ψ⟩⟨ψ|`, since `⟨ψ, ψ⟩ = 1`) fed into the
Euler formula for an idempotent `NormedSpace.exp_smul_of_mul_self_eq_self` with `z = -it`. -/
theorem PureState.projObservable_propagator_op (ψ : PureState S) (t : ℝ) :
    ((ψ.projObservable).propagator 1 0 t).op
      = 1 + (Complex.exp (-(Complex.I * (t : ℂ))) - 1) • rankOne ℂ ψ.vec ψ.vec := by
  have hidem : rankOne ℂ ψ.vec ψ.vec * rankOne ℂ ψ.vec ψ.vec = rankOne ℂ ψ.vec ψ.vec :=
    InnerProductSpace.isIdempotentElem_rankOne_self ψ.normalized
  have h1 : ((ψ.projObservable).propagator 1 0 t).op
      = NormedSpace.exp ((-(Complex.I * (t : ℂ))) • rankOne ℂ ψ.vec ψ.vec) := by
    rw [Observable.propagator_op, PureState.projObservable_op]; norm_num
  rw [h1, NormedSpace.exp_smul_of_mul_self_eq_self hidem]

/-- **The projector-Hamiltonian propagator, applied to a vector.** `exp(-i|ψ⟩⟨ψ|t) v =
v + (e^{-it} - 1)⟨ψ, v⟩ |ψ⟩`: the propagator fixes `v` except that its `|ψ⟩` component is scaled by
the phase `e^{-it}`. This is N&C's "the `|ψ⟩` vector is rotated slightly, into the `|x⟩` direction"
(§6.2, following eq. 6.20) made exact, and the operator identity that the Exercise 6.7 circuits
must reproduce on the query register. -/
theorem PureState.projObservable_propagator_op_apply (ψ : PureState S) (t : ℝ) (v : S.space) :
    ((ψ.projObservable).propagator 1 0 t).op v
      = v + ((Complex.exp (-(Complex.I * (t : ℂ))) - 1) * inner ℂ ψ.vec v) • ψ.vec := by
  rw [PureState.projObservable_propagator_op, add_apply,
    one_apply_eq_self, smul_apply, rankOne_apply, smul_smul]

end AxQM
