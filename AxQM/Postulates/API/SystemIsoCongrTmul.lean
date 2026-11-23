/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.Associator
import ToMathlib.Analysis.InnerProductSpace.TensorProductCongrConj

/-!
# AxQM.Postulates.API — transport of a product state distributes over the tensor

Two elementary reshaping laws for transport along system isomorphisms, alongside
`QSystem.Iso.comm` / `QSystem.Iso.tmul` and `PureState.congr_tmul`:

* `QSystem.Iso.comm_symm` — the inverse of the factor swap is the reversed swap,
  `(comm S T)⁻¹ = comm T S`.
* `State.congr_tmul` — the **density-state** companion of `PureState.congr_tmul`: transporting a
  product state `ρ ⊗ σ` along a product isomorphism `e ⊗ f` transports each factor separately,
  `(e ⊗ f)(ρ ⊗ σ)(e ⊗ f)⁻¹ = (e ρ e⁻¹) ⊗ (f σ f⁻¹)`.

The proof of `State.congr_tmul` works with the operators (`.op`, `TensorProduct.mapL`) and uses the
lemma `TensorProduct.congrIsometry_conjStarAlgEquiv_mapL`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The inverse of the factor swap is the reversed swap:** `(comm S T)⁻¹ = comm T S`. The
`QSystem.Iso` reading of `TensorProduct.commIsometry_symm`; the swap is its own inverse up to
reversing the factors. -/
theorem QSystem.Iso.comm_symm (S T : QSystem) :
    (QSystem.Iso.comm S T).symm = QSystem.Iso.comm T S :=
  congrArg QSystem.Iso.mk (TensorProduct.commIsometry_symm (𝕜 := ℂ) (E := S.space) (F := T.space))

variable {S S' T T' : QSystem}

/-- **Transport of a product state distributes over the tensor:** for system isomorphisms
`e : S ≃ₛ S'`, `f : T ≃ₛ T'` and states `ρ` on `S`, `σ` on `T`,

`(e ⊗ f)(ρ ⊗ σ)(e ⊗ f)⁻¹ = (e ρ e⁻¹) ⊗ (f σ f⁻¹)`,

i.e. `State.congr (e.tmul f) (ρ.tmul σ) = (ρ.congr e).tmul (σ.congr f)`. The density-state companion
of `PureState.congr_tmul`: the product isomorphism `e ⊗ f` transports each factor of a product state
separately. Proved at the level of operators, where the transport `conjStarAlgEquiv (e ⊗ f)`
distributes over the tensor operator `mapL ρ.op σ.op` by
`TensorProduct.congrIsometry_conjStarAlgEquiv_mapL`. -/
theorem State.congr_tmul (e : S ≃ₛ S') (f : T ≃ₛ T') (ρ : State S) (σ : State T) :
    State.congr (e.tmul f) (ρ.tmul σ) = (State.congr e ρ).tmul (State.congr f σ) := by
  have := FiniteDimensional.completeSpace ℂ S.space
  have := FiniteDimensional.completeSpace ℂ S'.space
  have := FiniteDimensional.completeSpace ℂ T.space
  have := FiniteDimensional.completeSpace ℂ T'.space
  ext1
  rw [State.congr_op, State.tmul_op, State.tmul_op, State.congr_op, State.congr_op]
  exact TensorProduct.congrIsometry_conjStarAlgEquiv_mapL e.toIsometry f.toIsometry ρ.op σ.op

/-- **Transport of a product gate distributes over the tensor:** for system isomorphisms
`e : S ≃ₛ S'`, `f : T ≃ₛ T'` and gates `U` on `S`, `V` on `T`,
`congr (e ⊗ f) (U ⊗ V) = (congr e U) ⊗ (congr f V)`. The `Evolution` companion of `State.congr_tmul`
(and of `PureState.congr_tmul`): the product isomorphism `e ⊗ f` transports each factor of a product
gate separately. Proved at the level of operators, where the transport `conjStarAlgEquiv (e ⊗ f)`
distributes over the tensor operator `mapL U.op V.op` by
`TensorProduct.congrIsometry_conjStarAlgEquiv_mapL`. -/
theorem Evolution.congr_tmul (e : S ≃ₛ S') (f : T ≃ₛ T') (U : Evolution S) (V : Evolution T) :
    Evolution.congr (e.tmul f) (U.tmul V) = (Evolution.congr e U).tmul (Evolution.congr f V) := by
  apply Evolution.ext
  rw [Evolution.congr_op, Evolution.tmul_op, Evolution.tmul_op, Evolution.congr_op,
    Evolution.congr_op]
  exact TensorProduct.congrIsometry_conjStarAlgEquiv_mapL e.toIsometry f.toIsometry U.op V.op

/-- **Naturality of the idle-front wrap under register transport.** Transporting a gate `E` along
`e : T ≃ₛ T'` and then wrapping it with an idle left factor `S` equals wrapping first and then
transporting along the lifted isomorphism `(Iso.refl S) ⊗ e`:
`(congr e E).onRight S = congr ((Iso.refl S).tmul e) (E.onRight S)`. Since `E.onRight S = 1 ⊗ E`,
this is `Evolution.congr_tmul` on `1 ⊗ E` together with `congr (refl S) 1 = 1`
(`Evolution.congr_id`). Lives here beside `Evolution.congr_tmul` — the corollary it is built from —
rather than with the general `congr` API, as its proof needs the tensor-transport lemma
this file imports. -/
theorem Evolution.congr_onRight (e : T ≃ₛ T') (E : Evolution T) (S : QSystem) :
    (Evolution.congr e E).onRight S
      = Evolution.congr ((QSystem.Iso.refl S).tmul e) (E.onRight S) := by
  change Evolution.id.tmul (Evolution.congr e E)
      = Evolution.congr ((QSystem.Iso.refl S).tmul e) (Evolution.id.tmul E)
  rw [Evolution.congr_tmul, Evolution.congr_id]

end AxQM
