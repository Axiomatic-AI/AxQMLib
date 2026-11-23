/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ReducedStateTransport
import ToMathlib.Analysis.InnerProductSpace.PartialTraceLeftBlock

/-!
# AxQM — tracing out a composite *left* factor of a state (N&C Exercise 11.24)

`State.reducedLeft` traces out the *right* factor of a bipartite state and `State.reducedRight` the
*left* factor. The transport lemma `State.reducedLeft_congr_assoc_symm`
(`AxQM/Postulates/API/ReducedStateTransport.lean`) records how tracing out a composite *right* block
`Y ⊗ Z` decomposes after re-association: for `ω` on `(X ⊗ Y) ⊗ Z`,
`Tr_{Y⊗Z} (assoc⁻¹ ω) = Tr_Z (Tr_Y ω)` (an iterated `reducedLeft`). This file adds the mirror for
the composite *left* block, the `reducedRight` analogue:

* `State.reducedRight_reducedRight_congr_assoc_symm` — for a state `b` on `(X ⊗ Y) ⊗ W`, tracing out
  the left block `X ⊗ Y` in one step equals re-associating to `X ⊗ (Y ⊗ W)`, tracing out `X`
  (`reducedRight`), then tracing out `Y` (`reducedRight`):

  `Tr_X (Tr_Y (assoc⁻¹ b)) = Tr_{X⊗Y} b`.

* `State.reducedRight_congr_assoc` — the forward face of the same identity (for `b` on
  `X ⊗ (Y ⊗ W)`), completing the `reducedRight` family alongside its `symm` face.

## Use

The purification proof of **weak monotonicity** `S(A) + S(B) ≤ S(A,C) + S(B,C)` (N&C Exercise 11.24)
reads the `S(A,C)` term off the purification as the marginal on the *composite* two-subsystem block
`A ⊗ C`, tracing out `R ⊗ B`. Turning that composite-block marginal into iterated single-factor
marginals — so it can be matched against strong subadditivity's `S(R,B)` term — is exactly this
decomposition. The `reducedLeft` half is in `AxQM/Postulates/API/ReducedStateTransport.lean`; the
`reducedRight` half is here.

The proof reduces to the left-block partial-trace tower lemma
`LinearMap.partialTraceLeft_partialTraceLeft_assocIsometry_conjStarAlgEquiv`
(`ToMathlib/Analysis/InnerProductSpace/PartialTraceLeftBlock`, the left mirror of
`partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Tracing out a composite left factor decomposes as iterated single-factor traces** (the
`reducedRight` mirror of `State.reducedLeft_congr_assoc_symm`). For a state `b` on `(X ⊗ Y) ⊗ W`,
re-associating to `X ⊗ (Y ⊗ W)`, tracing out `X` (`reducedRight`), then tracing out `Y`
(`reducedRight`) gives the same `W`-marginal as tracing out the whole left block `X ⊗ Y` at once:

`Tr_X (Tr_Y (assoc⁻¹ b)) = Tr_{X⊗Y} b`.

Reduces to the left-block tower lemma
`LinearMap.partialTraceLeft_partialTraceLeft_assocIsometry_conjStarAlgEquiv` (up to
basis-independence of the partial trace, `LinearMap.partialTraceLeft_eq_of_basis`). This is the
identity that lets the weak-monotonicity purification argument (N&C Exercise 11.24)
express the `A ⊗ C`-block marginal of a purification as an iterated marginal. -/
theorem State.reducedRight_reducedRight_congr_assoc_symm {X Y W : QSystem}
    (b : State ((X ⊗ Y) ⊗ W)) :
    ((State.congr (QSystem.assoc X Y W).symm b).reducedRight).reducedRight = b.reducedRight := by
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  change LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ Y.space)
      (LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ X.space)
        (((QSystem.assoc X Y W).symm.toIsometry.conjStarAlgEquiv b.op).toLinearMap)) =
      LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ (X ⊗ Y : QSystem).space) b.op.toLinearMap
  rw [QSystem.assoc_symm_toIsometry]
  -- `((X ⊗ Y) ⊗ W).space` is only `rfl`-defeq (via `QSystem.compose`, twice-nested) to the
  -- generic `(X.space ⊗[ℂ] Y.space) ⊗[ℂ] W.space` the tower/basis-independence lemmas
  -- need to match syntactically; restate `b.op` there via a `let` and bridge back with `exact`.
  let bopCLM : (X.space ⊗[ℂ] Y.space) ⊗[ℂ] W.space →L[ℂ]
      (X.space ⊗[ℂ] Y.space) ⊗[ℂ] W.space := b.op
  have htower := LinearMap.partialTraceLeft_partialTraceLeft_assocIsometry_conjStarAlgEquiv
    (stdOrthonormalBasis ℂ X.space) (stdOrthonormalBasis ℂ Y.space) bopCLM
  have hbasis := LinearMap.partialTraceLeft_eq_of_basis
    ((stdOrthonormalBasis ℂ X.space).tensorProduct (stdOrthonormalBasis ℂ Y.space))
    (stdOrthonormalBasis ℂ (X.space ⊗[ℂ] Y.space)) bopCLM.toLinearMap
  exact htower.trans hbasis

/-- **Tracing out a composite left factor is stable under association** — the forward face of
`State.reducedRight_reducedRight_congr_assoc_symm`, completing the `reducedRight` family. For a
state `b` on `X ⊗ (Y ⊗ W)`, re-associating to `(X ⊗ Y) ⊗ W` and tracing out the whole `X ⊗ Y` block
gives the same `W`-marginal as tracing out `X` then `Y`: `Tr_{X⊗Y}(assoc b) = Tr_Y(Tr_X b)`. Derived
from the `symm` face by cancelling the associator against its inverse, exactly as
`State.reducedLeft_reducedLeft_congr_assoc` (`AxQM/Postulates/API/SubadditivityReformulations.lean`)
mirrors
`State.reducedLeft_congr_assoc_symm`. -/
theorem State.reducedRight_congr_assoc {X Y W : QSystem} (b : State (X ⊗ (Y ⊗ W))) :
    (b.congr (QSystem.assoc X Y W)).reducedRight = b.reducedRight.reducedRight := by
  have h := State.reducedRight_reducedRight_congr_assoc_symm (b.congr (QSystem.assoc X Y W))
  rw [← State.congr_trans, QSystem.Iso.trans_symm_self, State.congr_refl] at h
  exact h.symm

end AxQM
