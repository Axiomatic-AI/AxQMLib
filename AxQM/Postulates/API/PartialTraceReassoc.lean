/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Associator
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.PartialTraceTensor

/-!
# AxQM — the middle marginal of a first-cut product state

For a product state `ρ ⊗ σ` on `A ⊗ (V ⊗ W)` (uncorrelated across the `A | VW` cut), the
marginal on `A ⊗ V` — obtained by re-associating to `(A ⊗ V) ⊗ W` and tracing out the outer
factor `W` — is again a product, `ρ ⊗ (Tr_W σ)`:

`Tr_W (ρ ⊗ σ) = ρ ⊗ σ.reducedLeft`.

This is the reduced-state analogue of associativity: the spectator factor `A` passes through the
partial trace untouched, and the trace lands on `σ`'s right factor. It is the tool for reading off
the `A ⊗ V` marginal of a tripartite product state `A ⊗ (V ⊗ W)` — the marginal that is otherwise
not a top-level `reducedLeft`/`reducedRight` because `W` sits in the middle after re-association.

The proof passes through the density operators to `LinearMap.partialTraceRight` and the tensor
associator; the statement uses `State.congr`, `QSystem.assoc`, `State.tmul`, `State.reducedLeft`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A V W : QSystem}

/-- **Right-regrouping a triple product state.** For factor states `ρ : State A`, `σ : State V`,
`τ : State W`, transporting the left-bracketed product `(ρ ⊗ σ) ⊗ τ` along the inverse associator
`(A ⊗ V) ⊗ W ≃ₛ A ⊗ (V ⊗ W)` yields the right-bracketed product `ρ ⊗ (σ ⊗ τ)`:

`State.congr (QSystem.assoc A V W).symm ((ρ ⊗ σ) ⊗ τ) = ρ ⊗ (σ ⊗ τ)`.

The `State`-level companion of `pureState_congr_assocSymm` (the `PureState` version). Proved at the
operator level: the associator's `conjStarAlgEquiv` re-brackets the triple tensor
`mapL (mapL ρ σ) τ` into `mapL ρ (mapL σ τ)` (`LinearMap.assocIsometry_conjStarAlgEquiv_mapL_mapL`),
the transport being `(A.assoc V W).symm.toIsometry = assocIsometry`
(`QSystem.assoc_symm_toIsometry`). -/
theorem State.congr_assoc_symm_tmul_tmul (ρ : State A) (σ : State V) (τ : State W) :
    State.congr (QSystem.assoc A V W).symm ((ρ.tmul σ).tmul τ) = ρ.tmul (σ.tmul τ) := by
  apply State.ext
  rw [State.congr_op, State.tmul_op, State.tmul_op, State.tmul_op, State.tmul_op,
    QSystem.assoc_symm_toIsometry]
  exact LinearMap.assocIsometry_conjStarAlgEquiv_mapL_mapL ρ.op σ.op τ.op

/-- **Left-regrouping a triple product state.** The forward companion of
`State.congr_assoc_symm_tmul_tmul`: transporting the right-bracketed product `ρ ⊗ (σ ⊗ τ)` along the
associator `A ⊗ (V ⊗ W) ≃ₛ (A ⊗ V) ⊗ W` yields the left-bracketed product `(ρ ⊗ σ) ⊗ τ`:

`State.congr (QSystem.assoc A V W) (ρ ⊗ (σ ⊗ τ)) = (ρ ⊗ σ) ⊗ τ`.

Immediate from `State.congr_assoc_symm_tmul_tmul` by cancelling the associator round-trip
(`State.congr_congr_symm`). -/
theorem State.congr_assoc_tmul_tmul (ρ : State A) (σ : State V) (τ : State W) :
    State.congr (QSystem.assoc A V W) (ρ.tmul (σ.tmul τ)) = (ρ.tmul σ).tmul τ := by
  rw [← State.congr_assoc_symm_tmul_tmul ρ σ τ, State.congr_congr_symm]

/-- **Middle marginal of a first-cut product state.** For `ρ : State A` and `σ : State (V ⊗ W)`,
re-associating the product `ρ ⊗ σ` on `A ⊗ (V ⊗ W)` to `(A ⊗ V) ⊗ W` and tracing out the outer
factor `W` leaves `ρ ⊗ (Tr_W σ)`:

`(State.congr (QSystem.assoc A V W) (ρ ⊗ σ)).reducedLeft = ρ ⊗ σ.reducedLeft`.

The spectator `A` factors through the partial trace; the reduction acts on `σ`. Proved at the
operator level via `LinearMap.partialTraceRight_assoc_conj_map` (the partial trace of an
associator-conjugated tensor map). -/
theorem State.reducedLeft_congr_assoc_tmul (ρ : State A) (σ : State (V ⊗ W)) :
    (State.congr (QSystem.assoc A V W) (ρ.tmul σ)).reducedLeft = ρ.tmul σ.reducedLeft := by
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  simp only [State.reducedLeft_op, State.congr_op, QSystem.assoc_toIsometry, State.tmul_op,
    LinearMap.coe_toContinuousLinearMap, TensorProduct.toLinearMap_mapL]
  have h1 := LinearMap.assocIsometry_symm_conjStarAlgEquiv_toLinearMap
    (𝕜 := ℂ) (E := A.space) (F := V.space) (G := W.space)
    (TensorProduct.mapL ρ.op σ.op)
  have h2 := LinearMap.partialTraceRight_assoc_conj_map (stdOrthonormalBasis ℂ W.space)
    ρ.op.toLinearMap σ.op.toLinearMap
  have h3 := TensorProduct.toLinearMap_mapL ρ.op σ.op
  have h1' := h1.trans (congrArg (TensorProduct.assoc ℂ A.space V.space W.space).symm.conj h3)
  exact (congrArg (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ W.space)) h1').trans h2

end AxQM
