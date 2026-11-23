/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Eigenstate
import AxQM.Postulates.API.Evolution

/-!
# AxQM.Postulates.API — stabilizer evolution under a unitary (N&C Eq. 10.87)

**Nielsen & Chuang Eq. (10.87)** (§10.5.2, p. 459), the foundational equation of the stabilizer
description of unitary dynamics and the engine of the Gottesman–Knill theorem (Theorem 10.7):

for `g ∈ S` stabilizing `|ψ⟩`, `U|ψ⟩ = UgU† U|ψ⟩`, so the evolved state is stabilized by `UgU†`.

Concretely: if a pure state `|ψ⟩` is a `μ`-eigenstate of an observable `A` (`A|ψ⟩ = μ|ψ⟩`, in
particular `μ = 1` is "`A` stabilizes `|ψ⟩`"), then the evolved state `U|ψ⟩`
(`Evolution.evolvePure`) is a `μ`-eigenstate of the **conjugated observable** `U A U†`
(`Observable.conjByEvolution`). Applied to `A = g` a stabilizer generator (`μ = 1`), this is exactly
"`U|ψ⟩` is stabilized by `U g U†`": a unitary transforms the stabilizer of a state by conjugating
its generators. The Gottesman–Knill theorem specializes this to the case where `U` is a Clifford
(normalizer) gate, for which `U g U†` is again a Pauli-group element computed *classically* — see
the check-matrix form
`AxQM.Concrete.CliffordCircuit.updatedGenerator_mulVec_toMatrix_mulVec`.

* `Observable.conjByEvolution` — the observable `U A U†` (self-adjoint by
  `IsSelfAdjoint.conjugate`), with the formula for its
  underlying operator `conjByEvolution_op`.
* `Observable.HasEigenstate.conjByEvolution_evolvePure` — Eq. (10.87) at a general eigenvalue.
* `Observable.HasEigenstate.conjByEvolution_evolvePure_one` — the stabilizer case (`μ = 1`),
  "`U|ψ⟩` is stabilized by `U g U†`".

The statement of Theorem 10.7 (classical simulability) is in
`AxQM/NC/Ch10/Theorem10_7_GottesmanKnill.lean`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Observable

/-- **Conjugation of an observable by a unitary evolution** (N&C §10.5.2): the observable `U A U†`,
where `U` is a unitary `Evolution` and `A` an `Observable`. Self-adjoint because conjugation of a
self-adjoint element by any element preserves self-adjointness (`IsSelfAdjoint.conjugate`, using
`A† = A`). The observable whose eigenstates track those of `A` under the evolution `U`. -/
def conjByEvolution (A : Observable S) (U : Evolution S) : Observable S where
  op := U.op * A.op * star U.op
  selfAdjoint := A.selfAdjoint.conjugate U.op

/-- The underlying operator of `A.conjByEvolution U` is `U A U†` (`= U.op * A.op * star U.op`). -/
@[simp]
theorem conjByEvolution_op (A : Observable S) (U : Evolution S) :
    (A.conjByEvolution U).op = U.op * A.op * star U.op := rfl

/-- **Nielsen & Chuang Eq. (10.87): unitary evolution transforms the stabilizer by conjugation.**
If `ψ` is a `μ`-eigenstate of the observable `A` (`A|ψ⟩ = μ|ψ⟩`), then the evolved state `U|ψ⟩`
(`U.evolvePure ψ`) is a `μ`-eigenstate of the conjugated observable `U A U†`
(`A.conjByEvolution U`): `(U A U†)(U|ψ⟩) = μ (U|ψ⟩)`. Proof:
`(U A U†)(Uψ) = U A (U†U ψ) = U A ψ = U (μ ψ) = μ (Uψ)`, using unitarity `U†U = 1`. -/
theorem HasEigenstate.conjByEvolution_evolvePure {A : Observable S} {μ : ℝ} {ψ : PureState S}
    (h : A.HasEigenstate μ ψ) (U : Evolution S) :
    (A.conjByEvolution U).HasEigenstate μ (U.evolvePure ψ) := by
  have hUadjU : star U.op * U.op = 1 := (Unitary.mem_iff.mp U.unitary).1
  have hAψ : A.op ψ.vec = (μ : ℂ) • ψ.vec := h
  rw [Observable.HasEigenstate, conjByEvolution_op, Evolution.evolvePure_vec,
    mul_apply_eq_comp, mul_apply_eq_comp,
    ← mul_apply_eq_comp (star U.op) U.op, hUadjU,
    one_apply_eq_self, hAψ, map_smul]

/-- **N&C Eq. (10.87), the stabilizer case:** if the observable `A` (e.g. a stabilizer generator
`g`) stabilizes `ψ` (`A|ψ⟩ = |ψ⟩`), then `U A U†` stabilizes the evolved state `U|ψ⟩` — "the state
`U|ψ⟩` is stabilized by `U g U†`". The `μ = 1` case of
`HasEigenstate.conjByEvolution_evolvePure`. -/
theorem HasEigenstate.conjByEvolution_evolvePure_one {A : Observable S} {ψ : PureState S}
    (h : A.HasEigenstate 1 ψ) (U : Evolution S) :
    (A.conjByEvolution U).HasEigenstate 1 (U.evolvePure ψ) :=
  h.conjByEvolution_evolvePure U

end Observable

end AxQM
