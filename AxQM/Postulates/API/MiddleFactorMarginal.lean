/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MutualInformationAncilla
import AxQM.Postulates.API.ReducedStateComm

/-!
# AxQM.Postulates.API — tracing out the *middle* factor of a product

For a bipartite state `ρ` on `S ⊗ T` and an uncorrelated spectator `σ` on `U`, this file computes
the `S ⊗ U`-marginal of `ρ ⊗ σ` — the marginal obtained by tracing out the **middle** factor `T`,
keeping the outer left factor `S` and the spectator `U`:

`Tr_T (ρ ⊗ σ) = (Tr_T ρ) ⊗ σ = ρ.reducedLeft ⊗ σ`.

The two siblings in `MutualInformationAncilla` trace out an *outer* factor of a first-cut
product: `State.reducedLeft_congr_symm_assoc_tmul` traces out `B ⊗ C` (keeping only `A`) and
`State.reducedRight_congr_symm_assoc_tmul` traces out the *outer left* factor `A` (keeping `B ⊗ C`).
Neither traces out the *middle* factor of `(S ⊗ T) ⊗ U`, which is what a two-stage single-system
dilation needs: after the first channel discards its environment `T`, adjoining the second
environment `U` and re-exposing the surviving system `S` traces `T` from between `S` and `U`.

Because `State.reducedRight` traces the *left* factor, the middle factor `T` is first brought to the
front by the swap `S ⊗ T ≃ₛ T ⊗ S` (`QSystem.Iso.comm`) — so `(ρ ⊗ σ)` is presented as
`(comm ρ) ⊗ σ` on `(T ⊗ S) ⊗ U`, then re-associated to `T ⊗ (S ⊗ U)` where tracing the front factor
`T` (`State.reducedRight_congr_symm_assoc_tmul`) leaves `(comm ρ).reducedRight ⊗ σ`, and
`(comm ρ).reducedRight = ρ.reducedLeft` (`State.reducedLeft_congr_comm`).

-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S T U : QSystem}

/-- **Tracing out the middle factor of a first-cut product state.** For a bipartite state `ρ` on
`S ⊗ T` and an uncorrelated spectator `σ` on `U`, bringing the middle factor `T` to the front (swap
`S ⊗ T ≃ₛ T ⊗ S`), re-associating `(T ⊗ S) ⊗ U ≃ₛ T ⊗ (S ⊗ U)`, and tracing out that front factor
`T` leaves the `S`-marginal of `ρ` tensored with the spectator:

`Tr_T ((comm ρ) ⊗ σ, re-associated) = ρ.reducedLeft ⊗ σ`.

The middle-factor companion of `State.reducedLeft_congr_symm_assoc_tmul` /
`State.reducedRight_congr_symm_assoc_tmul` (which trace an *outer* factor). It lets the second stage
of a two-stage single-system dilation re-expose its system after the first stage discarded its
environment: read off from `State.reducedRight_congr_symm_assoc_tmul` (tracing the front factor) and
`State.reducedLeft_congr_comm` (the swapped right marginal is the left marginal). -/
theorem State.reducedRight_congr_symm_assoc_comm_tmul (ρ : State (S ⊗ T)) (σ : State U) :
    (State.congr (QSystem.assoc T S U).symm
        ((State.congr (QSystem.Iso.comm S T) ρ).tmul σ)).reducedRight = ρ.reducedLeft.tmul σ := by
  rw [State.reducedRight_congr_symm_assoc_tmul, ← State.reducedLeft_congr_comm]

end AxQM
