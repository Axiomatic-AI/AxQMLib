/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.QSystem
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.ReducedState

/-!
# AxQM — reduced states (partial trace)

The **reduced state** (marginal) of a bipartite state of a composite system `S ⊗ T`,
obtained by tracing out one factor (Nielsen–Chuang §2.4.3):

* `State.reducedLeft ρ : State S` — the marginal on the left system `S`,
  `ρ_A = Tr_T(ρ_{AB})`.
* `State.reducedRight ρ : State T` — the marginal on the right system `T`.

The partial trace (`LinearMap.partialTraceLeft`/`partialTraceRight`) is
parametrized by an orthonormal basis on the traced-out factor, but is
basis-independent (`partialTraceLeft_eq_of_basis`). We canonicalize on
`stdOrthonormalBasis`, giving the definitions a basis-free signature; the
density-operator property transfers via `IsDensityOp.of_partialTrace{Left,Right}_eq`.

The op is ascribed to the explicit underlying tensor `S.space ⊗[ℂ] T.space` so the
partial-trace API unifies through the composite coercion `↑(S ⊗ T)`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **reduced state on the left system**: `ρ_A = Tr_T(ρ_{AB})`, tracing out
the right factor. -/
def State.reducedLeft (ρ : State (S ⊗ T)) : State S where
  op := (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ T.space)
    (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)).toContinuousLinearMap
  isDensity :=
    ρ.isDensity.of_partialTraceRight_eq (stdOrthonormalBasis ℂ T.space)
      (by rw [LinearMap.coe_toContinuousLinearMap])

/-- The **reduced state on the right system**: `ρ_B = Tr_S(ρ_{AB})`, tracing out
the left factor. -/
def State.reducedRight (ρ : State (S ⊗ T)) : State T where
  op := (LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ S.space)
    (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)).toContinuousLinearMap
  isDensity :=
    ρ.isDensity.of_partialTraceLeft_eq (stdOrthonormalBasis ℂ S.space)
      (by rw [LinearMap.coe_toContinuousLinearMap])

@[simp]
theorem State.reducedLeft_op (ρ : State (S ⊗ T)) :
    ρ.reducedLeft.op = (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ T.space)
      (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)).toContinuousLinearMap :=
  rfl

@[simp]
theorem State.reducedRight_op (ρ : State (S ⊗ T)) :
    ρ.reducedRight.op = (LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ S.space)
      (ρ.op.toLinearMap : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)).toContinuousLinearMap :=
  rfl

end AxQM
