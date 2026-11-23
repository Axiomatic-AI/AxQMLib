/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SubadditivityReformulations
import AxQM.Postulates.API.ReducedStateReshape
import AxQM.Postulates.API.SystemIsoComm

/-!
# AxQM.Postulates.API — the left-commutation marginal law

For a tripartite state `W` on `X ⊗ (Y ⊗ Z)`, bringing the middle factor `Y` to the front by the
left-commutation reshape `QSystem.Iso.leftComm X Y Z : X ⊗ (Y ⊗ Z) ≃ₛ Y ⊗ (X ⊗ Z)` and then tracing
out everything except `Y` (`State.reducedLeft`, which discards the right factor `X ⊗ Z`) gives the
same state on `Y` as tracing out the outer factor `X` and then the inner factor `Z` of the original
`W` (`W.reducedRight.reducedLeft`):

`Tr_{X ⊗ Z} (leftComm · W) = Tr_Z (Tr_X W) = W.reducedRight.reducedLeft`.

This is the "keep the middle factor" companion of the reshape-marginal calculus
(`State.reducedLeft_congr_comm`, `State.reducedRight_congr_symm_assoc_comm_tmul`, …): `leftComm`
brings `Y` to the head of the composite so a single `State.reducedLeft` reads off the `Y`-marginal,
and because tracing out `X` and `Z` from `W` is order-independent, the result is the iterated
marginal `W.reducedRight.reducedLeft`.

Compare the related reshape-marginal laws in `MiddleFactorMarginal`, `ReducedStateComm` and
`SubadditivityReformulations`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {X Y Z : QSystem}

/-- **The left-commutation marginal law.** For a state `W` on `X ⊗ (Y ⊗ Z)`, transporting along the
left-commutation reshape `QSystem.Iso.leftComm X Y Z : X ⊗ (Y ⊗ Z) ≃ₛ Y ⊗ (X ⊗ Z)` (which brings the
middle factor `Y` to the front) and tracing out the right factor `X ⊗ Z` (`State.reducedLeft`) is
the same as tracing out the outer left factor `X` and then the inner factor `Z` of `W`:

`(State.congr (QSystem.Iso.leftComm X Y Z) W).reducedLeft = W.reducedRight.reducedLeft`.

Unfolding `leftComm` to its associator/swap composite and peeling with `State.congr_trans`, the
outer de-association (`State.reducedLeft_congr_assoc_symm`) turns the marginal into a double trace,
the front swap is carried through the kept factor (`State.reducedLeft_congr_tmul_left`) and read as
a right marginal (`State.reducedRight_congr_comm`), and the residual associator trace reorders to
`W.reducedRight.reducedLeft` (`State.reducedRight_reducedLeft_congr_assoc`). The "keep the middle
factor" companion of the reduced-state reshape calculus, used to collapse a two-stage single-system
dilation into one joint dilation (`State.dilatedChannelComp_eq_dilatedChannel`). -/
theorem State.reducedLeft_congr_leftComm (W : State (X ⊗ (Y ⊗ Z))) :
    (State.congr (QSystem.Iso.leftComm X Y Z) W).reducedLeft = W.reducedRight.reducedLeft := by
  rw [QSystem.Iso.leftComm, State.congr_trans, State.congr_trans,
    State.reducedLeft_congr_assoc_symm, State.reducedLeft_congr_tmul_left,
    ← State.reducedRight_congr_comm, State.reducedRight_reducedLeft_congr_assoc]

end AxQM
