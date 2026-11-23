/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ReducedStateTransport
import ToMathlib.Analysis.InnerProductSpace.PartialTraceComm

/-!
# AxQM — the two reduced states are related by the factor swap

The two reduced states are the two faces of one partial trace: `State.reducedLeft` traces
out the *right* factor, `State.reducedRight` traces out the *left* factor. This file records the
relation between them, mediated by the transport swap `QSystem.Iso.comm`:

`ρ.reducedRight = (ρ.congr (QSystem.Iso.comm S T)).reducedLeft`  — the right marginal of `ρ` on
`S ⊗ T` (trace out `S`) is the *left* marginal of the swapped state on `T ⊗ S`.

## Why this is useful

`State.reducedLeft` has a full transport-naturality API (`State.reducedLeft_congr_tmul_refl`,
`State.reducedLeft_congr_assoc_symm`, `State.reducedLeft_reducedLeft_congr_assoc`, …, in
`AxQM/Postulates/API/ReducedStateTransport.lean` and
`AxQM/Postulates/API/SubadditivityReformulations.lean`), because it is defined through
`LinearMap.partialTraceRight`, for which `ToMathlib` has the naturality lemmas (invariance under a
unitary on the traced factor, associator commutation). Its mirror `State.reducedRight`, defined
through `LinearMap.partialTraceLeft`, has *no* such API. Rather than re-prove every naturality fact
on the left, this relation lets a `reducedRight` goal be rewritten to a `reducedLeft` goal on the
swapped state, where the existing API applies. The purification proof of weak monotonicity (N&C
Exercise 11.24) uses it to trace out the *first* factor of a nested composite (a `reducedRight`)
and read the result off through the `reducedLeft` lemmas.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The right marginal is the left marginal of the swapped state.** For a bipartite state `ρ` on
`S ⊗ T`, tracing out the left factor `S` (`State.reducedRight`) is the same as swapping the factors
(`ρ.congr (QSystem.Iso.comm S T)`, a state on `T ⊗ S`) and tracing out the (now right) factor `S`
(`State.reducedLeft`):

`ρ.reducedRight = (ρ.congr (QSystem.Iso.comm S T)).reducedLeft`.

At the level of operators this is the partial-trace identity
`LinearMap.partialTraceLeft_eq_partialTraceRight_comm`: `reducedRight` is a `partialTraceLeft`,
`reducedLeft` of the swapped state is a `partialTraceRight` of the `comm`-conjugated operator, and
the two agree. It transfers the `reducedLeft` transport-naturality API to
`reducedRight` (see the module docstring). -/
theorem State.reducedRight_congr_comm (ρ : State (S ⊗ T)) :
    ρ.reducedRight = (ρ.congr (QSystem.Iso.comm S T)).reducedLeft := by
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  simp only [State.reducedRight_op, State.reducedLeft_op, State.congr_op,
    LinearMap.coe_toContinuousLinearMap]
  exact LinearMap.partialTraceLeft_eq_partialTraceRight_comm (stdOrthonormalBasis ℂ S.space)
    (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)

/-- **The left marginal is the right marginal of the swapped state** (mirror of
`State.reducedRight_congr_comm`). For a bipartite state `ρ` on `S ⊗ T`, tracing out the right
factor `T` (`State.reducedLeft`) is the same as swapping the factors and tracing out the (now left)
factor `T` (`State.reducedRight`):

`ρ.reducedLeft = (ρ.congr (QSystem.Iso.comm S T)).reducedRight`.

Partial-trace identity `LinearMap.partialTraceRight_eq_partialTraceLeft_comm`. Transfers the
`reducedRight` API to `reducedLeft` (e.g. symmetry of the mutual information). -/
theorem State.reducedLeft_congr_comm (ρ : State (S ⊗ T)) :
    ρ.reducedLeft = (ρ.congr (QSystem.Iso.comm S T)).reducedRight := by
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  simp only [State.reducedRight_op, State.reducedLeft_op, State.congr_op,
    LinearMap.coe_toContinuousLinearMap]
  exact LinearMap.partialTraceRight_eq_partialTraceLeft_comm (stdOrthonormalBasis ℂ T.space)
    (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)

end AxQM
