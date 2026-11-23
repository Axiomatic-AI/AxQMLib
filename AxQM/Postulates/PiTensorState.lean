/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.PiTensor
import AxQM.Postulates.StateSpace
import AxQM.Postulates.SystemIso
import ToMathlib.Analysis.InnerProductSpace.PiTensorProductDensity

/-!
# AxQM.Postulates — indexed product states (`⨂ₚ i, ψ i`)

The state-level companion of the indexed composite system `⨂ₛ i, S i`
(`QSystem.piTensor`, `PiTensor.lean`). Given a finite family of *pure* states
`ψ : ∀ i, PureState (S i)`, their **indexed product state** `⨂ₚ i, ψ i` is the pure
state of `⨂ₛ i, S i` whose underlying vector is the n-ary elementary tensor
`⨂ₜ[ℂ] i, (ψ i).vec` — the n-ary form of the binary product pure state `ψ ⊗ φ`
(`PureState.tmul`, `Composite.lean`).

Alongside it, `QSystem.piTensorReindex` re-indexes an indexed composite along an
index equivalence `e : ι ≃ κ` (a system isomorphism `⨂ₛ i, S i ≃ₛ ⨂ₛ j, S (e.symm j)`,
built on `PiTensorProduct.reindexₗᵢ`), and `PureState.piTensor_congr_piTensorReindex`
records its naturality: transporting a product state along the reindex is the product
state of the reindexed family.

Normalization is proved on the explicit underlying space via the multiplicativity of the tensor
inner product (`PiTensorProduct.inner_tprod_tprod`) and closed into the bundled goal by defeq.

## Main definitions

* `PureState.piTensor` (`⨂ₚ i, ψ i`) — the indexed product pure state of a finite family
  `ψ : ∀ i, PureState (S i)`, on `⨂ₛ i, S i`.
* `State.piTensor` (`⨂ₚ i, ρ i`) — the indexed product (mixed) state of a finite family
  `ρ : ∀ i, State (S i)`, on `⨂ₛ i, S i`.
* `QSystem.piTensorReindex` — the reindexing system isomorphism
  `⨂ₛ i, S i ≃ₛ ⨂ₛ j, S (e.symm j)` along `e : ι ≃ κ`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {S : ι → QSystem}

/-- **Indexed product pure state** `⨂ₚ i, ψ i`: the product of a finite family of pure
states `ψ : ∀ i, PureState (S i)`, on the indexed composite `⨂ₛ i, S i`. The n-ary form of
the binary product pure state `ψ ⊗ φ` (`PureState.tmul`). The underlying vector is the n-ary
elementary tensor `⨂ₜ[ℂ] i, (ψ i).vec`; it is a unit vector because the tensor inner product
is multiplicative (`PiTensorProduct.inner_tprod_tprod`). -/
def PureState.piTensor (ψ : ∀ i, PureState (S i)) : PureState (⨂ₛ i, S i) where
  vec := ⨂ₜ[ℂ] i, (ψ i).vec
  normalized := by
    have h : (inner ℂ (⨂ₜ[ℂ] i, (ψ i).vec) (⨂ₜ[ℂ] i, (ψ i).vec) : ℂ) = 1 := by
      rw [PiTensorProduct.inner_tprod_tprod]
      exact Finset.prod_eq_one fun i _ ↦ by
        rw [inner_self_eq_norm_sq_to_K, (ψ i).normalized]; norm_num
    have h2 : ‖(⨂ₜ[ℂ] i, (ψ i).vec)‖ ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]; simp
    calc ‖(⨂ₜ[ℂ] i, (ψ i).vec)‖
        = Real.sqrt (‖(⨂ₜ[ℂ] i, (ψ i).vec)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 1 := by rw [h2, Real.sqrt_one]

@[inherit_doc PureState.piTensor]
scoped notation3:100 "⨂ₚ "(...)", "r:67:(scoped f => PureState.piTensor f) => r

@[simp]
theorem PureState.piTensor_vec (ψ : ∀ i, PureState (S i)) :
    (⨂ₚ i, ψ i).vec = ⨂ₜ[ℂ] i, (ψ i).vec := rfl

/-- **Indexed product (mixed) state** `⨂ₚ i, ρ i`: the product of a finite family of states
`ρ : ∀ i, State (S i)`, on the indexed composite `⨂ₛ i, S i`. The n-ary form of the binary
product state `ρ ⊗ σ` (`State.tmul`); a genuine `State` because the n-ary tensor of density
operators is a density operator (`PiTensorProduct.mapCLM_isDensityOp`). -/
def State.piTensor (ρ : ∀ i, State (S i)) : State (⨂ₛ i, S i) where
  op := PiTensorProduct.mapCLM fun i ↦ (ρ i).op
  isDensity := PiTensorProduct.mapCLM_isDensityOp fun i ↦ (ρ i).isDensity

@[inherit_doc State.piTensor]
scoped notation3:100 "⨂ₚ "(...)", "r:67:(scoped f => State.piTensor f) => r

@[simp]
theorem State.piTensor_op (ρ : ∀ i, State (S i)) :
    (⨂ₚ i, ρ i).op = PiTensorProduct.mapCLM fun i ↦ (ρ i).op := rfl

/-! ## Reindexing an indexed composite -/

/-- **Reindexing an indexed composite** along an index equivalence `e : ι ≃ κ`: the system
isomorphism `⨂ₛ i, S i ≃ₛ ⨂ₛ j, S (e.symm j)`, built on the reindex isometry
`PiTensorProduct.reindexₗᵢ`. -/
def QSystem.piTensorReindex (e : ι ≃ κ) (S : ι → QSystem) :
    (⨂ₛ i, S i) ≃ₛ ⨂ₛ j, S (e.symm j) :=
  ⟨PiTensorProduct.reindexₗᵢ ℂ (fun i ↦ (S i).space) e⟩

@[simp]
theorem QSystem.piTensorReindex_toIsometry (e : ι ≃ κ) (S : ι → QSystem) :
    (QSystem.piTensorReindex e S).toIsometry
      = PiTensorProduct.reindexₗᵢ ℂ (fun i ↦ (S i).space) e := rfl

/-- **Naturality of the product state under reindexing**: transporting `⨂ₚ i, ψ i` along
`QSystem.piTensorReindex e` is the product state of the reindexed family `fun j ↦ ψ (e.symm j)`. -/
@[simp]
theorem PureState.piTensor_congr_piTensorReindex (e : ι ≃ κ) (ψ : ∀ i, PureState (S i)) :
    (⨂ₚ i, ψ i).congr (QSystem.piTensorReindex e S) = ⨂ₚ j, ψ (e.symm j) := by
  apply PureState.ext
  rw [PureState.congr_vec, PureState.piTensor_vec, PureState.piTensor_vec]
  exact PiTensorProduct.reindexₗᵢ_tprod e (fun i ↦ (ψ i).vec)

/-- **Naturality of the product (mixed) state under reindexing**: transporting `⨂ₚ i, ρ i`
along `QSystem.piTensorReindex e` is the product state of the reindexed family
`fun j ↦ ρ (e.symm j)`. The `State` companion of `PureState.piTensor_congr_piTensorReindex`,
riding `PiTensorProduct.reindexₗᵢ_mapCLM`. -/
@[simp]
theorem State.piTensor_congr_piTensorReindex (e : ι ≃ κ) (ρ : ∀ i, State (S i)) :
    (⨂ₚ i, ρ i).congr (QSystem.piTensorReindex e S) = ⨂ₚ j, ρ (e.symm j) := by
  apply State.ext
  rw [State.congr_op, State.piTensor_op, State.piTensor_op, QSystem.piTensorReindex_toIsometry]
  ext y
  -- `(⨂ₛ i, S i).space` vs the plain `⨂[ℂ] i, (S i).space` diverge under `rw`'s syntactic
  -- matching even though defeq; `erw` bridges it.
  erw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  -- term-mode `.trans`: a syntactic `rw`/`simp [reindexₗᵢ_mapCLM]` won't fire — the reindex
  -- family `(S i).space` and `mapCLM`'s codomain `↥(S i)` (from `(ρ i).op`) are defeq but not
  -- syntactically equal, so only the defeq-checking `exact`/`congrArg` route matches.
  exact (PiTensorProduct.reindexₗᵢ_mapCLM e (fun i ↦ (ρ i).op) _).trans
    (congrArg _ (LinearIsometryEquiv.apply_symm_apply _ y))

end AxQM
