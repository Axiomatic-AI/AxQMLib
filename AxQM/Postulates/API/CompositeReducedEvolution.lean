/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MutualInformationEvolution
import AxQM.Postulates.API.EvolutionTensorHom
import AxQM.Postulates.API.ReducedStateComm
import AxQM.Postulates.API.CompositeStateEvolution

/-!
# AxQM.Postulates.API — marginals of a product-unitary evolution

The marginal (reduced-state) laws for a **product unitary** `U ⊗ V` acting on a bipartite state
`ρ` on `S ⊗ T`. They generalise the existing "one factor is the identity" laws
`State.reducedLeft_evolve_id_tmul` / `State.reducedRight_evolve_id_tmul` to the case where *both*
factors carry a nontrivial unitary — the situation that arises when Alice and Bob apply their own
local unitaries simultaneously on disjoint factors (Nielsen & Chuang Exercise 12.22, the
no-communication entanglement-conversion model).

The physical content: a product unitary `U ⊗ V` conjugates each party's marginal by that party's own
unitary and leaves the other marginal's *support* alone (the other unitary, being trace preserving,
disappears when its factor is traced out). Concretely

* `State.reducedLeft_evolve_tmul` — `Tr_T((U ⊗ V) ρ (U ⊗ V)†) = U (Tr_T ρ) U† = U.evolve ρ_S`;
* `State.reducedRight_evolve_tmul` — `Tr_S((U ⊗ V) ρ (U ⊗ V)†) = V (Tr_S ρ) V† = V.evolve ρ_T`.

## Design

Each law is obtained by factoring the product unitary `U ⊗ V = (U ⊗ I).comp (I ⊗ V)`
(`Evolution.tmul_comp` with the identity on the other factor) so that the two single-factor laws
apply in sequence (`Evolution.evolve_comp`):

* for `reducedLeft`, the `I ⊗ V` step is invisible to Alice's marginal
  (`State.reducedLeft_evolve_id_tmul`) and the `U ⊗ I` step conjugates it
  (`State.reducedLeft_evolve_tmul_id`, the mirror of `State.reducedRight_evolve_id_tmul`);
* for `reducedRight`, symmetrically, via the swap `QSystem.Iso.comm`
  (`State.reducedRight_congr_comm` reads a right marginal off as a left marginal) after which
  `State.reducedLeft_evolve_tmul` applies — the swap turning `U ⊗ V` into `V ⊗ U` is
  `Evolution.tmul_congr_comm`.

The building block `State.reducedLeft_evolve_tmul_id` (Alice's unitary on the *kept* left factor,
identity on the traced right factor) mirrors `State.reducedRight_evolve_id_tmul` at the level of
operators: the partial trace over the traced factor commutes with the kept factor's unitary
(`LinearMap.partialTraceRight_tensorMap_id_comp` / `…_comp_tensorMap_id`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A local unitary on the kept factor transforms that marginal covariantly.** For a state `ρ` on
`S ⊗ T` and a unitary `U` on the left factor `S`, the reduced state on the *left* factor of
`(U ⊗ I_T) ρ (U ⊗ I_T)†` is `U ρ_S U†` (`U.evolve ρ.reducedLeft`). The identity on the traced-out
`T` factor passes straight through the partial trace over `T`
(`LinearMap.partialTraceRight_tensorMap_id_comp` / `…_comp_tensorMap_id`), leaving the conjugation
by `U` acting on the surviving `S`-marginal. The mirror of `State.reducedRight_evolve_id_tmul`. -/
theorem State.reducedLeft_evolve_tmul_id (U : Evolution S) (ρ : State (S ⊗ T)) :
    ((U.tmul (Evolution.id (S := T))).evolve ρ).reducedLeft = U.evolve ρ.reducedLeft := by
  -- Express the evolved operator as `(U ⊗ I) ρ (U ⊗ I)†` at the linear-map level. The adjoint of
  -- `U ⊗ I` is `U† ⊗ I`; push it through `TensorProduct.map` via `adjoint_map` under a `congr` (the
  -- `QSystem.compose` instance blocks a direct rewrite; `exact` unifies up to defeq).
  have hbridge : ((U.tmul (Evolution.id (S := T))).evolve ρ).op.toLinearMap
      = TensorProduct.map U.op.toLinearMap LinearMap.id ∘ₗ ρ.op.toLinearMap
          ∘ₗ TensorProduct.map (LinearMap.adjoint U.op.toLinearMap) LinearMap.id := by
    let ρopCLM : S.space ⊗[ℂ] T.space →L[ℂ] S.space ⊗[ℂ] T.space := ρ.op
    have hgen : ((U.tmul (Evolution.id (S := T))).evolve ρ).op.toLinearMap
        = (TensorProduct.mapL U.op (1 : T.space →L[ℂ] T.space) ∘L ρopCLM ∘L
            TensorProduct.mapL (ContinuousLinearMap.adjoint U.op)
              (1 : T.space →L[ℂ] T.space)).toLinearMap := by
      rw [show ((U.tmul (Evolution.id (S := T))).evolve ρ).op
          = TensorProduct.mapL U.op (1 : T.space →L[ℂ] T.space) ∘L ρopCLM ∘L
            ContinuousLinearMap.adjoint (TensorProduct.mapL U.op (1 : T.space →L[ℂ] T.space))
          from rfl,
        TensorProduct.adjoint_mapL, ContinuousLinearMap.adjoint_one]
    rw [hgen, ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      TensorProduct.toLinearMap_mapL, TensorProduct.toLinearMap_mapL,
      ContinuousLinearMap.toLinearMap_one]
    rfl
  ext1
  rw [State.reducedLeft_op, hbridge, LinearMap.partialTraceRight_tensorMap_id_comp]
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap, Evolution.evolve_op,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap,
    ContinuousLinearMap.adjoint_toLinearMap]
  congr 1
  exact LinearMap.partialTraceRight_comp_tensorMap_id (stdOrthonormalBasis ℂ T.space)
    (LinearMap.adjoint U.op.toLinearMap) ρ.op.toLinearMap

/-- **The left marginal after a product-unitary evolution undergoes only the left unitary.** For a
state `ρ` on `S ⊗ T` and a product unitary `U ⊗ V`, tracing out the right factor `T` from
`(U ⊗ V) ρ (U ⊗ V)†` gives `U ρ_S U† = U.evolve ρ.reducedLeft`: the right unitary `V`, being trace
preserving, disappears with its factor, and the left unitary `U` conjugates the surviving
`S`-marginal. Proved by factoring `U ⊗ V = (U ⊗ I).comp (I ⊗ V)` (`Evolution.tmul_comp`,
`Evolution.evolve_comp`) so `State.reducedLeft_evolve_id_tmul` clears the `I ⊗ V` step and
`State.reducedLeft_evolve_tmul_id` conjugates by `U`. -/
theorem State.reducedLeft_evolve_tmul (U : Evolution S) (V : Evolution T) (ρ : State (S ⊗ T)) :
    ((U.tmul V).evolve ρ).reducedLeft = U.evolve ρ.reducedLeft := by
  have hUV : (U.tmul (Evolution.id (S := T))).comp ((Evolution.id (S := S)).tmul V) = U.tmul V := by
    rw [Evolution.tmul_comp, Evolution.comp_id, Evolution.id_comp]
  rw [← hUV, Evolution.evolve_comp, State.reducedLeft_evolve_tmul_id,
    State.reducedLeft_evolve_id_tmul]

/-- **Conjugating a product unitary by the factor swap exchanges its factors.** For unitaries `U` on
`S` and `V` on `T`, transporting `U ⊗ V` along the swap `S ⊗ T ≃ₛ T ⊗ S` gives `V ⊗ U`:
`(U ⊗ V).congr (comm S T) = V ⊗ U`. Proved pointwise on a pure tensor `y ⊗ x`, where both sides act
as `V y ⊗ U x` (the swap turns `y ⊗ x` into `x ⊗ y`, `U ⊗ V` sends it to `U x ⊗ V y`, and the swap
sends that back to `V y ⊗ U x`). The `Evolution` analogue of `State.reducedRight_congr_comm`'s
underlying swap, used to read a right marginal off as a left marginal in
`State.reducedRight_evolve_tmul`. -/
theorem Evolution.tmul_congr_comm (U : Evolution S) (V : Evolution T) :
    (U.tmul V).congr (QSystem.Iso.comm S T) = V.tmul U := by
  ext1
  rw [Evolution.congr_op, Evolution.tmul_op, Evolution.tmul_op, QSystem.Iso.comm_toIsometry]
  exact TensorProduct.commIsometry_conjStarAlgEquiv_mapL U.op V.op

/-- **The right marginal after a product-unitary evolution undergoes only the right unitary.** For a
state `ρ` on `S ⊗ T` and a product unitary `U ⊗ V`, tracing out the left factor `S` from
`(U ⊗ V) ρ (U ⊗ V)†` gives `V ρ_T V† = V.evolve ρ.reducedRight`: the left unitary `U`, being trace
preserving, disappears with its factor, and the right unitary `V` conjugates the surviving
`T`-marginal. Proved by reading the right marginal off as a left marginal after the swap
`QSystem.Iso.comm` (`State.reducedRight_congr_comm`), which turns `U ⊗ V` into `V ⊗ U`
(`Evolution.tmul_congr_comm`, transported through evolution by `Evolution.congr_evolve_congr`), and
then applying `State.reducedLeft_evolve_tmul`. The mirror of `State.reducedLeft_evolve_tmul`. -/
theorem State.reducedRight_evolve_tmul (U : Evolution S) (V : Evolution T) (ρ : State (S ⊗ T)) :
    ((U.tmul V).evolve ρ).reducedRight = V.evolve ρ.reducedRight := by
  rw [State.reducedRight_congr_comm, ← Evolution.congr_evolve_congr, Evolution.tmul_congr_comm,
    State.reducedLeft_evolve_tmul, ← State.reducedRight_congr_comm]

end AxQM
