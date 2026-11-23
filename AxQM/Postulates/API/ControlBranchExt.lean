/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.Evolution

/-!
# AxQM.Postulates.API — control-branch extensionality and gate-algebra helpers

Machinery for **multiply-controlled** operations (Nielsen & Chuang §4.3), used to
reason about controlled gates on `qubit ⊗ R` for an *arbitrary* target system `R`. It generalises
the three-qubit tools of `ControlledControlledUnitary` from a fixed two-control system to an
arbitrary tail, so an `n`-control gate (`C(C(…C(U)…))`) can be handled one control at a time.

## What is formalised

* `controlBranch_evolution_ext` — **control-branch extensionality:** two evolutions of `qubit ⊗ R`
  are equal as soon as they agree on every product input `|i⟩ ⊗ ψ` with `i ∈ {0, 1}` a
  computational-basis control and `ψ` an arbitrary pure state of the tail `R`. This is the tool that
  lets an induction on the number of controls peel one control at a time (the target `R` being the
  remaining controls plus the target qubit), the direct generalisation of
  `threeQubit_evolution_ext` to a variable tail.
* `Evolution.adjoint_comp_self'` — the gate-level unitarity cancellation `U† U = 1` (the
  `Evolution`-valued form of the op-level `Evolution.adjoint_comp_self`).
* `controlledUnitary_id` — `C(1) = 1`: controlling the identity gate is the identity.

The generic right-factor gate-algebra `Evolution.onRight_comp` (`(1 ⊗ V)(1 ⊗ W) = 1 ⊗ (V W)`) and
`Evolution.id_onRight` (`1 ⊗ 1 = 1`) are reused from `Postulates/API/ToffoliHadamard`.

## Design notes

* **The extensionality proof.** As in `threeQubit_evolution_ext`, reduce `Evolution` equality to
  operator equality (`Evolution.ext`, `ContinuousLinearMap.coe_injective`) and apply
  `Module.Basis.ext` to the tensor basis `basisFun (Fin 2) ⊗ stdOrthonormalBasis R.space` (via
  `OrthonormalBasis.tensorProduct`). Each tail basis vector is a unit vector, hence the `vec` of a
  `PureState`, so the product hypothesis supplies the required agreement after unfolding
  `evolvePure_vec` / `PureState.tmul_vec`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### Control-branch extensionality -/

/-- **Control-branch extensionality for `qubit ⊗ R` gates.** Two evolutions `A`, `B` of `qubit ⊗ R`
(control qubit on the left, arbitrary tail `R` on the right) are equal as soon as they agree on
every product input `|i⟩ ⊗ ψ` with `i ∈ {0, 1}` a computational-basis control and `ψ` an arbitrary
pure state of `R`. This is the tool for peeling one control at a time in an induction over the
number of controls; it generalises `threeQubit_evolution_ext` from the fixed two-control tail
`qubit ⊗ qubit` to a variable tail `R`.

Proved as in `threeQubit_evolution_ext`: reduce to operator equality (`Evolution.ext`,
`ContinuousLinearMap.coe_injective`) and apply `Module.Basis.ext` to the tensor basis
`EuclideanSpace.basisFun (Fin 2) ⊗ stdOrthonormalBasis R.space`; each tail basis vector `eR j` is a
unit vector, hence `(⟨eR j, _⟩ : PureState R).vec`, so the hypothesis supplies agreement on the
basis after unfolding `evolvePure_vec` / `PureState.tmul_vec`. -/
theorem controlBranch_evolution_ext {R : QSystem} {A B : Evolution (qubit ⊗ R)}
    (h : ∀ (i : Fin 2) (ψ : PureState R),
      A.evolvePure ((qubitBasis i) ⊗ ψ) = B.evolvePure ((qubitBasis i) ⊗ ψ)) :
    A = B := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  let bq : OrthonormalBasis (Fin 2) ℂ qubit.space := EuclideanSpace.basisFun (Fin 2) ℂ
  let eR : OrthonormalBasis (Fin (Module.finrank ℂ R.space)) ℂ R.space :=
    stdOrthonormalBasis ℂ R.space
  have hbq : ∀ i : Fin 2, bq i = (qubitBasis i).vec := fun i => by
    rw [qubitBasis_vec]; exact EuclideanSpace.basisFun_apply (Fin 2) ℂ i
  refine Module.Basis.ext (bq.tensorProduct eR).toBasis ?_
  rintro ⟨i, j⟩
  have hb : (bq.tensorProduct eR).toBasis (i, j) = (qubitBasis i).vec ⊗ₜ[ℂ] (eR j) := by
    rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply, hbq]
  rw [hb]
  let ψ : PureState R := ⟨eR j, eR.orthonormal.1 j⟩
  have hh := congrArg PureState.vec (h i ψ)
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec] at hh
  exact hh

/-! ### Gate-level unitarity cancellation -/

/-- **Uncompute cancellation** `U† U = 1` as an equality of `Evolution`s: the `Evolution`-valued
form of the op-level `Evolution.adjoint_comp_self` (named `_self'` to follow it, *not* the bare
`adjoint_comp`, which is Mathlib's adjoint-of-a-composition `(A ∘ B)† = B† ∘ A†`). -/
theorem Evolution.adjoint_comp_self' (U : Evolution S) : U.adjoint.comp U = Evolution.id := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.adjoint_op, Evolution.id_op, U.adjoint_comp_self]

/-! ### Controlling the identity -/

/-- **Controlling the identity gate is the identity:** `C(1) = 1`. With control `|0⟩` the target is
untouched and with control `|1⟩` the identity is applied, so nothing happens either way. -/
theorem controlledUnitary_id : controlledUnitary (Evolution.id : Evolution S) = Evolution.id := by
  apply controlBranch_evolution_ext
  intro i _
  fin_cases i <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, Evolution.id_evolvePure]

end AxQM
