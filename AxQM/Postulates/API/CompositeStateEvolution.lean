/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import AxQM.Postulates.SystemIso

/-!
# AxQM.Postulates.API — composite-state evolution algebra

The **density-operator** analogues of the pure-state composite-evolution laws
`Evolution.tmul_evolvePure` (`Postulates/API/ControlledControlledUnitary`) and
`Evolution.congr_evolvePure_congr` (`Postulates/API/LeftPairGate`): how a product unitary and a
system-isomorphism transport interact with the Schrödinger evolution `U ρ U†` of a mixed `State`.

* `Evolution.tmul_evolve` — a **product unitary evolves a product state factorwise**:
  `(U ⊗ V)(ρ ⊗ σ)(U ⊗ V)† = (U ρ U†) ⊗ (V σ V†)`. The mixed-state companion of
  `Evolution.tmul_evolvePure`.
* `Evolution.congr_evolve_congr` — **state transport commutes with evolution**:
  transporting the gate `U` and the state `ρ` along a system isomorphism `e` and then evolving is
  the same as evolving and then transporting, `(e U e⁻¹)(e ρ e⁻¹)(e U e⁻¹)† = e (U ρ U†) e⁻¹`. The
  mixed-state companion of `Evolution.congr_evolvePure_congr`.

## Design notes

Both proofs drop to the operators (`.op`) and reduce to the
`TensorProduct.mapL` algebra (`mapL_comp`, `mapL_adjoint`) and the `StarAlgEquiv` naturality of
`conjStarAlgEquiv`. The final `mapL`-adjoint step in `Evolution.tmul_evolve` is discharged by
`congr 2` down to `adjoint (mapL U V) = mapL (adjoint U) (adjoint V)` and then `exact`, rather than
`rw [TensorProduct.adjoint_mapL]`: the tensor-adjoint term produced by `Evolution.evolve_op` and the
one produced by `mapL_adjoint` are *defeq* but not syntactically equal (the composite system's
inner-product instance is a defeq-but-distinct copy of `TensorProduct`'s canonical one, the diamond
documented in `Postulates/API/Interchange`), so `rw`/`simp only [mapL_adjoint]` cannot match it
while a definitionally checked `exact` can.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A product unitary evolves a product state factorwise:** `(U ⊗ V)(ρ ⊗ σ)(U ⊗ V)† =
(U ρ U†) ⊗ (V σ V†)`. The mixed-state companion of `Evolution.tmul_evolvePure`: the tensor operator
`U ⊗ V = mapL U.op V.op` conjugates the tensor density operator `ρ ⊗ σ = mapL ρ.op σ.op` slotwise,
by multiplicativity of `mapL` (`TensorProduct.mapL_comp`) and its compatibility with the adjoint
(`TensorProduct.adjoint_mapL`). -/
theorem Evolution.tmul_evolve (U : Evolution S) (V : Evolution T) (ρ : State S) (σ : State T) :
    (U ⊗ V).evolve (ρ ⊗ σ) = (U.evolve ρ) ⊗ (V.evolve σ) := by
  ext1
  have := FiniteDimensional.completeSpace ℂ S.space
  have := FiniteDimensional.completeSpace ℂ T.space
  simp only [Evolution.evolve_op, State.tmul_op, Evolution.tmul_op]
  have hkey : TensorProduct.mapL U.op V.op ∘L TensorProduct.mapL ρ.op σ.op ∘L
        ContinuousLinearMap.adjoint (TensorProduct.mapL U.op V.op)
      = TensorProduct.mapL (U.op ∘L ρ.op ∘L ContinuousLinearMap.adjoint U.op)
          (V.op ∘L σ.op ∘L ContinuousLinearMap.adjoint V.op) := by
    rw [TensorProduct.adjoint_mapL, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp]
  exact hkey

/-- **State transport commutes with evolution:** transporting the gate `U` and the state `ρ` along a
system isomorphism `e : S ≃ₛ T` and then evolving equals evolving and then transporting,
`(e U e⁻¹)(e ρ e⁻¹)(e U e⁻¹)† = e (U ρ U†) e⁻¹`. The mixed-state companion of
`Evolution.congr_evolvePure_congr`: the conjugation `conjStarAlgEquiv e` is a `StarAlgEquiv`, so it
distributes over the operator product and the adjoint that make up `U.evolve ρ = U ρ U†`. -/
theorem Evolution.congr_evolve_congr (e : S.Iso T) (U : Evolution S) (ρ : State S) :
    (U.congr e).evolve (State.congr e ρ) = State.congr e (U.evolve ρ) := by
  ext1
  simp only [State.congr_op, Evolution.evolve_op, Evolution.congr_op,
    ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, map_mul, map_star]

end AxQM
