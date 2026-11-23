/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import AxQM.Postulates.PartialTrace
import ToMathlib.Analysis.InnerProductSpace.PurificationFreedom

/-!
# Nielsen & Chuang, Exercise 2.81 (freedom in purifications)

Freedom in purifications: two purifications related by (I_A⊗U_R).

A **purification** of a mixed state `ρᴬ` on system `A` is a pure state `|AR⟩` on an enlarged
system `A ⊗ R` whose reduced density operator on `A` is `ρᴬ`, i.e. `Tr_R(|AR⟩⟨AR|) = ρᴬ`
(`State.reducedLeft`). Two purifications of the *same* `ρᴬ` to the *same* reference system `R`
therefore have equal left marginals; the exercise asserts they are related by a unitary acting
only on the reference `R`.

Here `ψ, φ : PureState (A ⊗ R)` are the two purifications (`|AR₂⟩` and `|AR₁⟩`), and the shared
reduced state hypothesis is `ψ.toState.reducedLeft = φ.toState.reducedLeft`. The unitary on `R`
is packaged as an `Evolution R` (Postulate 5), and `I_A ⊗ U_R` is the composite evolution
`(Evolution.id) ⊗ U_R` (`Evolution.tmul`, equivalently `Evolution.onRight`); it acts on the pure
state via `Evolution.evolvePure`.

The statement uses `State.reducedLeft` (partial trace, §2.4.3), `Evolution` (Postulate 5),
`Evolution.tmul`, and `Evolution.evolvePure`.

The mathematical content is the theorem
`TensorProduct.exists_mem_unitary_mapL_id_eq`
(`ToMathlib/Analysis/InnerProductSpace/PurificationFreedom.lean`): two vectors of `E ⊗ F` with
equal right-partial-trace of their rank-one projectors are related by `I_E ⊗ U` for a unitary
`U` on `F`. Its proof reduces, via the matricization `M = matricize b Ψ`, to
`M_ψ M_ψ† = M_φ M_φ†`, feeds this to the operator crux of the unitary-freedom-in-the-ensemble
theorem (`ContinuousLinearMap.exists_unitary_comp_of_comp_adjoint_eq`, N&C Thm 2.6) to get a
unitary `W` with `M_φ = M_ψ ∘ W`, and transports `W` back through the tensor factor using the
basis transpose (`I_E ⊗ U` acts on the matricization by right-composition with `transpose b U`).
This file states it for pure states and evolutions.
-/

open AxQM

namespace AxQM

/-- **Freedom in purifications** (N&C Exercise 2.81). Two purifications `ψ, φ` of the same state
`ρᴬ` to the same composite system `A ⊗ R` — i.e. two pure states of `A ⊗ R` with the same reduced
state on `A`, `ψ.toState.reducedLeft = φ.toState.reducedLeft` — are related by a unitary `U`
acting only on the reference system `R`: `φ = (I_A ⊗ U) ψ`, where `I_A ⊗ U` is the composite
evolution `Evolution.id ⊗ U` acting via `Evolution.evolvePure`. -/
theorem PureState.exists_evolution_tmul_id_evolvePure_eq {S R : QSystem}
    (ψ φ : PureState (S.compose R)) (h : ψ.toState.reducedLeft = φ.toState.reducedLeft) :
    ∃ U : Evolution R, φ = ((Evolution.id (S := S)).tmul U).evolvePure ψ := by
  obtain ⟨Uop, hUop, hUeq⟩ :=
    TensorProduct.exists_mem_unitary_mapL_id_eq (stdOrthonormalBasis ℂ R.space) ψ.vec φ.vec (by
      have hop := congrArg State.op h
      rw [State.reducedLeft_op, State.reducedLeft_op, PureState.toState_op,
        PureState.toState_op] at hop
      exact LinearMap.toContinuousLinearMap.injective hop)
  refine ⟨⟨Uop, hUop⟩, ?_⟩
  ext
  rw [Evolution.evolvePure_vec, Evolution.tmul_op, Evolution.id_op]
  exact hUeq.symm

end AxQM
