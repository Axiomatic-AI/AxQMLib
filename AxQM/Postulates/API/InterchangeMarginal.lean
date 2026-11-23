/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Interchange
import AxQM.Postulates.API.ReducedStateReshape
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.PartialTraceTensor
import ToMathlib.Analysis.InnerProductSpace.TensorProductInterchangePartialTrace

/-!
# AxQM.Postulates.API — the interchange marginal of a product state

For a product state `ρ ⊗ σ` on a fourfold composite `(E ⊗ F) ⊗ (G ⊗ H)` (`ρ` on `E ⊗ F`, `σ` on
`G ⊗ H`), transporting along the interchange braid
`QSystem.Iso.interchange E F G H : (E ⊗ F) ⊗ (G ⊗ H) ≃ₛ (E ⊗ G) ⊗ (F ⊗ H)` (which brings `E` beside
`G` and `F` beside `H`) and reading off the left marginal factorises across the two blocks:

`Tr_{F ⊗ H} (interchange (ρ ⊗ σ)) = ρ.reducedLeft ⊗ σ.reducedLeft`.

Even though `ρ`, `σ` are correlated within their own blocks, the `E ⊗ G`-marginal sees only the
`F`-trace of `ρ` and the `H`-trace of `σ`: the two parties' factors decouple exactly as the
interchange regroups them.

## Role in Exercise 12.22

This is the "trace out both parties' ancillae" step of Nielsen & Chuang Exercise 12.22.  The
joint pure state of the no-communication protocol lives on `(A ⊗ B) ⊗ (CA ⊗ CB)` (system beside
system, ancilla beside ancilla) but its *Alice-side* marginal is read across the
`(A ⊗ CA) | (B ⊗ CB)` cut.  When the joint state factorises as `|φ⟩⟨φ| ⊗ |χ⟩⟨χ|` (its `A ⊗ B`
marginal is the pure target `φ`), applying `interchange A B CA CB` and tracing `B ⊗ CB` reads off
the Alice marginal `ρ_φ ⊗ ρ_χ`, whose spectrum is `λ_φ ⊗ x` — one half of the spectral equivalence
`λ_ψ ≅ λ_φ ⊗ x`.

## Design notes

The `reducedLeft`/`reducedRight` reshape toolkit (`State.reducedLeft_congr_assoc_symm`,
`State.reducedLeft_congr_leftComm`, …) cannot reach this law: peeling the interchange through its
`assoc/comm` decomposition first de-associates `(E ⊗ F) ⊗ (G ⊗ H)`, splitting the correlated `E | F`
block, so no `State`-level marginal law applies.  The proof therefore cracks the density operator:
`reducedLeft.op` is `partialTraceRight`, `congr.op` is `conjStarAlgEquiv` by the interchange
isometry, and `tmul.op` is `mapL`, and the lemma
`TensorProduct.partialTraceRight_tensorTensorTensorCommIsometry_conjStarAlgEquiv_mapL` computes the
partial trace of the interchange-conjugated product operator as `(Tr_F ρ) ⊗ (Tr_H σ)` — proved there
by reducing to fully product operators via `homTensorHomEquiv` (its trace basis is left general, so
the composite factor `(F ⊗ H).space`'s standard basis slots in directly).

Compare `MiddleFactorMarginal`, `LeftCommMarginal` and `ReducedStateReshape`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {E F G H : QSystem}

/-- **The interchange marginal of a product state (left block).** For a product state `ρ ⊗ σ` on
`(E ⊗ F) ⊗ (G ⊗ H)`, transporting along the interchange braid `QSystem.Iso.interchange E F G H`
(which brings `E` beside `G`) and tracing out the new right factor `F ⊗ H` gives the product of the
two block left-marginals:

`(congr (interchange E F G H) (ρ ⊗ σ)).reducedLeft = ρ.reducedLeft ⊗ σ.reducedLeft`.

Proved at the level of operators: `reducedLeft.op = partialTraceRight`,
`congr.op = conjStarAlgEquiv` by the interchange isometry, `tmul.op = mapL`, and the
interchange-marginal computation
`TensorProduct.partialTraceRight_tensorTensorTensorCommIsometry_conjStarAlgEquiv_mapL`. -/
theorem State.reducedLeft_congr_interchange_tmul (ρ : State (E ⊗ F)) (σ : State (G ⊗ H)) :
    (State.congr (QSystem.Iso.interchange E F G H) (ρ.tmul σ)).reducedLeft
      = ρ.reducedLeft.tmul σ.reducedLeft := by
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  simp only [State.reducedLeft_op, State.congr_op, State.tmul_op,
    QSystem.Iso.interchange_toIsometry, LinearMap.coe_toContinuousLinearMap,
    TensorProduct.toLinearMap_mapL]
  exact TensorProduct.partialTraceRight_tensorTensorTensorCommIsometry_conjStarAlgEquiv_mapL
    (stdOrthonormalBasis ℂ (F ⊗ H).space) (stdOrthonormalBasis ℂ F.space)
    (stdOrthonormalBasis ℂ H.space) ρ.op σ.op

/-- **The inverse-interchange left marginal of a state with a product right block.** For a state
`ρ ⊗ (σ ⊗ μ)` on `(E ⊗ G) ⊗ (F ⊗ H)` — the "parties∣ancillas" frame — transporting along the
**inverse** interchange braid `(QSystem.Iso.interchange E F G H).symm : (E ⊗ G) ⊗ (F ⊗ H) ≃ₛ
(E ⊗ F) ⊗ (G ⊗ H)` (the "Alice∣Bob" frame) and tracing out the new right factor `G ⊗ H` gives
`ρ.reducedLeft ⊗ σ`:

`(congr (interchange E F G H).symm (ρ ⊗ (σ ⊗ μ))).reducedLeft = ρ.reducedLeft ⊗ σ`.

The inverse braid is the forward braid `interchange E G F H` (`QSystem.Iso.interchange_symm`), so
the product-marginal law `State.reducedLeft_congr_interchange_tmul` applies; the surviving ancilla
block `σ ⊗ μ` then contributes only its own left marginal `σ` (`State.reducedLeft_tmul`, the second
block `μ` being trace-preserving). This is the marginal Nielsen & Chuang Exercise 12.22 reads off in
both directions of its iff: with `ρ = ψ` and `σ ⊗ μ = ωA ⊗ ωB` the two pure ancillas, the Alice-side
marginal of the regrouped joint state `|ψ⟩ ⊗ |ωA⟩ ⊗ |ωB⟩` is `ρ_ψ ⊗ |ωA⟩⟨ωA|`. -/
theorem State.reducedLeft_congr_interchange_symm_tmul_tmul (ρ : State (E ⊗ G)) (σ : State F)
    (μ : State H) :
    (State.congr (QSystem.Iso.interchange E F G H).symm (ρ.tmul (σ.tmul μ))).reducedLeft
      = ρ.reducedLeft.tmul σ := by
  rw [QSystem.Iso.interchange_symm, State.reducedLeft_congr_interchange_tmul,
    State.reducedLeft_tmul]

/-- **`PureState` companion of `State.reducedLeft_congr_interchange_symm_tmul_tmul`.** For pure
states `ρ` on `E ⊗ G`, `σ` on `F`, `μ` on `H`, the left marginal of the density state of the
inverse-interchange-transported `|ρ⟩ ⊗ (|σ⟩ ⊗ |μ⟩)` is `ρ_ρ ⊗ |σ⟩⟨σ|`:

`(congr (interchange E F G H).symm (ρ ⊗ (σ ⊗ μ))).toState.reducedLeft`
`  = ρ.toState.reducedLeft ⊗ σ.toState`.

Unfolds `PureState.congr`/`PureState.tmul` to their density-state form (`PureState.congr_toState`,
`PureState.toState_tmul`) and applies the `State`-level lemma. The exact bridge both directions of
Nielsen & Chuang Exercise 12.22 use to read the Alice-side marginal `ρ_ψ ⊗ |ωA⟩⟨ωA|` of the
regrouped joint pure state `|ψ⟩ ⊗ |ωA⟩ ⊗ |ωB⟩`. -/
theorem PureState.reducedLeft_congr_interchange_symm_tmul_tmul (ρ : PureState (E ⊗ G))
    (σ : PureState F) (μ : PureState H) :
    (PureState.congr (QSystem.Iso.interchange E F G H).symm
        (ρ.tmul (σ.tmul μ))).toState.reducedLeft
      = ρ.toState.reducedLeft.tmul σ.toState := by
  rw [PureState.congr_toState, PureState.toState_tmul, PureState.toState_tmul,
    State.reducedLeft_congr_interchange_symm_tmul_tmul]

end AxQM
