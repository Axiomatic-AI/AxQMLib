/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditGate
import AxQM.Postulates.API.QuditTensorFactor
import AxQM.Postulates.API.Associator
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.DeutschGate
import AxQM.Postulates.API.LeftPairGate
import AxQM.Concrete.DeutschDoublyControlledReachable
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# Register identification for the three-qubit ↔ eight-level register (N&C Ex 4.44)

This file supplies the **register identification** for expressing the physical Deutsch gate
`deutschGate α = ccontrolledUnitary (iRxGate (πα))` (a gate on the composite three-qubit system
`qubit ⊗ qubit ⊗ qubit`) as an explicit matrix on the eight-level register `qudit 8` — the
representation in which the matrix reachability argument of Exercise 4.44
(`Concrete.deutschWirePlacedReachable`, `…deutschDataReachableCircuits`, etc.) is carried out.

The point of this file is the *register model*: the physical gates (`controlledUnitary`,
`ccontrolledUnitary`) are defined on composite tensor systems `qubit ⊗ S`, whereas the matrix-level
statements work on `qudit d = EuclideanSpace ℂ (Fin d)`. The two are
identified here by the system isomorphism `threeQuditIso`, whose basis-transport law
`threeQuditIso_congr_quditBasis` reads its action on `qudit 8` off the three-qubit product basis via
the pure-math packing bijection `Concrete.threeQubitIndex : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` (and its
matrix companion `Concrete.ccontrolledMatFin8`, both in
`Concrete/DeutschDoublyControlledReachable`).

## What is formalised

* `threeQuditIso` — the system isomorphism `qudit 2 ⊗ (qudit 2 ⊗ qudit 2) ≃ₛ qudit 8`, built from
  the tensor-factoring isomorphism `quditProdIso` (splitting `qudit 8 ≃ qudit 2 ⊗ qudit 4` and then
  `qudit 4 ≃ qudit 2 ⊗ qudit 2`). As `qubit = qudit 2` definitionally, any evolution on
  `qubit ⊗ (qubit ⊗ qubit)` — in particular `deutschGate α` — transports along it.
* `threeQuditIso_congr_quditBasis` — **the basis-transport law**: the three-qubit product basis
  state `|c₁⟩ ⊗ |c₂⟩ ⊗ |t⟩` maps, under `threeQuditIso`, to the computational basis vector of
  `qudit 8` at the packed index `Concrete.threeQubitIndex (c₁, c₂, t)`. This is the bridge that lets
  the action of a transported gate on `qudit 8` be read off from its action on the product basis
  (the computation carried out below to identify `ccontrolledUnitary U`,
  transported, with `Matrix.toEuclideanCLM (Concrete.ccontrolledMatFin8 M2)`).

The data these statements consume — the `Fin`-index packing `Concrete.threeQubitIndex` and the
reindexed doubly-controlled matrix `Concrete.ccontrolledMatFin8` — are in
`AxQM/Concrete/DeutschDoublyControlledReachable.lean`.
-/

namespace AxQM

open scoped TensorProduct

noncomputable section

/-- The system isomorphism `qudit 2 ⊗ (qudit 2 ⊗ qudit 2) ≃ₛ qudit 8` (identifying the three-qubit
register with the eight-level register). As `qubit = qudit 2` definitionally, an evolution on
`qubit ⊗ (qubit ⊗ qubit)` — such as `deutschGate α` — transports along it. It is built from the
tensor-factoring isomorphism `quditProdIso`, splitting `qudit 8 ≃ qudit 2 ⊗ qudit 4` and the right
`qudit 4 ≃ qudit 2 ⊗ qudit 2`. -/
def threeQuditIso : ((qudit 2) ⊗ ((qudit 2) ⊗ (qudit 2))) ≃ₛ qudit 8 :=
  (QSystem.Iso.tmul (QSystem.Iso.refl (qudit 2)) (quditProdIso 2 2).symm).trans
    (quditProdIso 2 4).symm

/-- **The basis-transport law for `threeQuditIso`.** The three-qubit product basis state
`|c₁⟩ ⊗ |c₂⟩ ⊗ |t⟩` maps, under `threeQuditIso`, to the computational basis vector of `qudit 8` at
the packed index `Concrete.threeQubitIndex (c₁, c₂, t)`. Proved by unfolding `threeQuditIso` into
its two `quditProdIso` factors and applying the symm-direction basis law
`quditProdIso_symm_congr_quditBasis` at each step. This is the bridge that lets the action of a
transported gate on `qudit 8` be read off from its action on the three-qubit product basis. -/
theorem threeQuditIso_congr_quditBasis (c₁ c₂ t : Fin 2) :
    PureState.congr threeQuditIso
        ((quditBasis c₁).tmul ((quditBasis c₂).tmul (quditBasis t)))
      = quditBasis (Concrete.threeQubitIndex (c₁, c₂, t)) := by
  rw [threeQuditIso, PureState.congr_trans, PureState.congr_tmul, PureState.congr_refl,
    quditProdIso_symm_congr_quditBasis 2 2 c₂ t,
    quditProdIso_symm_congr_quditBasis 2 4 c₁ (finProdFinEquiv (c₂, t))]
  rfl

/-! ### The operator–matrix bridge `C²(U)` transported ≟ `toEuclideanCLM (ccontrolledMatFin8 M2)`

The physical doubly-controlled gate `ccontrolledUnitary U` on `qubit ⊗ (qubit ⊗ qubit)`, transported
along `threeQuditIso` to `qudit 8`, is the explicit `Fin 8` matrix `Concrete.ccontrolledMatFin8 M2`
whenever `U.op = toEuclideanCLM M2`. This is proved by evaluating both continuous linear maps on the
computational basis `|threeQubitIndex (c₁, c₂, t)⟩` of `qudit 8`: the physical side transports the
product-basis input through `threeQuditIso` and applies `C²(U)`'s truth table (the target undergoes
`U` exactly on the `|1⟩|1⟩` control block, otherwise nothing), while the matrix side reads off the
`threeQubitIndex`-th column of `ccontrolledMatFin8 M2` — the two agree by the entrywise formula
`Concrete.ccontrolledMat_apply`.
-/

/-- **The doubly-controlled gate transports the two `|1⟩` controls with the target undergoing `U`.**
Rewriting the transported `C²(U)` action on the packed basis state `|threeQubitIndex (1,1,t)⟩` as
the `threeQuditIso`-image of `|1⟩ ⊗ |1⟩ ⊗ (U|t⟩)`. The `qubit = qudit 2` identification lets the
`qubitBasis`-stated action lemmas `ccontrolledUnitary_evolvePure_ketOne_left` /
`controlledUnitary_evolvePure_ketOne` discharge the `quditBasis`-phrased goal after `congr`. -/
private theorem congr_ccontrolledUnitary_evolvePure_eleven (U : Evolution qubit) (t : Fin 2) :
    (Evolution.congr threeQuditIso (ccontrolledUnitary U)).evolvePure
        (quditBasis (Concrete.threeQubitIndex (1, 1, t)))
      = PureState.congr threeQuditIso
          ((quditBasis 1).tmul ((quditBasis 1).tmul (U.evolvePure (quditBasis t)))) := by
  erw [← threeQuditIso_congr_quditBasis, Evolution.congr_evolvePure_congr]
  congr 1
  change (ccontrolledUnitary U).evolvePure
        ((qubitBasis 1).tmul ((qubitBasis 1).tmul (qubitBasis t)))
      = (qubitBasis 1).tmul ((qubitBasis 1).tmul (U.evolvePure (qubitBasis t)))
  rw [ccontrolledUnitary_evolvePure_ketOne_left, controlledUnitary_evolvePure_ketOne]

/-- **The doubly-controlled gate fixes every packed basis state whose controls are not both `|1⟩`.**
When `¬ (c₁ = 1 ∧ c₂ = 1)`, `C²(U)` leaves `|c₁⟩ ⊗ |c₂⟩ ⊗ |t⟩` untouched, so the transported gate
fixes `|threeQubitIndex (c₁, c₂, t)⟩`. The three inactive control patterns are discharged by the
`qubitBasis` action lemmas after `congr`; the `(1,1)` pattern contradicts the hypothesis. -/
private theorem congr_ccontrolledUnitary_evolvePure_fixed (U : Evolution qubit) (c₁ c₂ t : Fin 2)
    (h : ¬ (c₁ = 1 ∧ c₂ = 1)) :
    (Evolution.congr threeQuditIso (ccontrolledUnitary U)).evolvePure
        (quditBasis (Concrete.threeQubitIndex (c₁, c₂, t)))
      = quditBasis (Concrete.threeQubitIndex (c₁, c₂, t)) := by
  erw [← threeQuditIso_congr_quditBasis, Evolution.congr_evolvePure_congr]
  congr 1
  fin_cases c₁ <;> fin_cases c₂
  · change (ccontrolledUnitary U).evolvePure
          ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t)))
        = (qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t))
    rw [ccontrolledUnitary_evolvePure_ketZero_left]
  · change (ccontrolledUnitary U).evolvePure
          ((qubitBasis 0).tmul ((qubitBasis 1).tmul (qubitBasis t)))
        = (qubitBasis 0).tmul ((qubitBasis 1).tmul (qubitBasis t))
    rw [ccontrolledUnitary_evolvePure_ketZero_left]
  · change (ccontrolledUnitary U).evolvePure
          ((qubitBasis 1).tmul ((qubitBasis 0).tmul (qubitBasis t)))
        = (qubitBasis 1).tmul ((qubitBasis 0).tmul (qubitBasis t))
    rw [ccontrolledUnitary_evolvePure_ketOne_left, controlledUnitary_evolvePure_ketZero]
  · exact absurd ⟨rfl, rfl⟩ h

/-- **The `threeQubitIndex`-th column of `ccontrolledMatFin8 M2` as a basis expansion.** Applying
the matrix operator `toEuclideanCLM (ccontrolledMatFin8 M2)` to `|threeQubitIndex p⟩` yields the
`p`-th column of `ccontrolledMat M2`, expanded over the packed basis `{|threeQubitIndex q⟩}`.
Obtained from `Matrix.toEuclideanCLM_apply_single` by reindexing the column sum along
`threeQubitIndex`. -/
private theorem ccontrolledMatFin8_toEuclideanCLM_apply (M2 : Matrix (Fin 2) (Fin 2) ℂ)
    (p : Fin 2 × Fin 2 × Fin 2) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (Concrete.ccontrolledMatFin8 M2)
        (EuclideanSpace.single (Concrete.threeQubitIndex p) 1)
      = ∑ q : Fin 2 × Fin 2 × Fin 2,
          Concrete.ccontrolledMat M2 q p •
            EuclideanSpace.single (Concrete.threeQubitIndex q) (1 : ℂ) := by
  rw [Matrix.toEuclideanCLM_apply_single, ← Equiv.sum_comp Concrete.threeQubitIndex
      (fun k => Concrete.ccontrolledMatFin8 M2 k (Concrete.threeQubitIndex p) •
        EuclideanSpace.single k (1 : ℂ))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  simp only [Concrete.ccontrolledMatFin8, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]

/-- **The active column of `ccontrolledMat M2`** (both controls `|1⟩`): the `(1,1,t)` column
expands to `∑ₛ (M2)ₛₜ |threeQubitIndex (1,1,s)⟩` — the target runs `M2`, controls fixed. -/
private theorem ccontrolledMat_col_sum_active (M2 : Matrix (Fin 2) (Fin 2) ℂ) (t : Fin 2) :
    ∑ q : Fin 2 × Fin 2 × Fin 2,
        Concrete.ccontrolledMat M2 q (1, 1, t) •
          EuclideanSpace.single (Concrete.threeQubitIndex q) (1 : ℂ)
      = ∑ s : Fin 2, M2 s t •
          EuclideanSpace.single (Concrete.threeQubitIndex (1, 1, s)) (1 : ℂ) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Concrete.ccontrolledMat_apply]
  simp

/-- **An inactive column of `ccontrolledMat M2`** (controls not both `|1⟩`): the `(c,d,t)` column is
the single basis vector `|threeQubitIndex (c,d,t)⟩` — the gate acts as the identity there. -/
private theorem ccontrolledMat_col_sum_inactive (M2 : Matrix (Fin 2) (Fin 2) ℂ) (c d t : Fin 2)
    (h : ¬ (c = 1 ∧ d = 1)) :
    ∑ q : Fin 2 × Fin 2 × Fin 2,
        Concrete.ccontrolledMat M2 q (c, d, t) •
          EuclideanSpace.single (Concrete.threeQubitIndex q) (1 : ℂ)
      = EuclideanSpace.single (Concrete.threeQubitIndex (c, d, t)) (1 : ℂ) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Concrete.ccontrolledMat_apply]
  fin_cases c <;> fin_cases d <;> fin_cases t <;> simp_all

/-- **The transported `C²(U)` on an inactive basis column**: `|threeQubitIndex (c₁,c₂,t)⟩` is fixed
by the transported gate when the controls are not both `|1⟩` — the `Evolution.op` form of
`congr_ccontrolledUnitary_evolvePure_fixed`. -/
private theorem congr_ccontrolledUnitary_op_single_fixed (U : Evolution qubit) (c₁ c₂ t : Fin 2)
    (h : ¬ (c₁ = 1 ∧ c₂ = 1)) :
    (Evolution.congr threeQuditIso (ccontrolledUnitary U)).op
        (EuclideanSpace.single (Concrete.threeQubitIndex (c₁, c₂, t)) 1)
      = EuclideanSpace.single (Concrete.threeQubitIndex (c₁, c₂, t)) (1 : ℂ) := by
  rw [← quditBasis_vec, ← Evolution.evolvePure_vec,
    congr_ccontrolledUnitary_evolvePure_fixed U c₁ c₂ t h]

/-- **The transported `C²(U)` on the active basis column** (both controls `|1⟩`):
`|threeQubitIndex (1,1,t)⟩` maps to `∑ₛ (M2)ₛₜ |threeQubitIndex (1,1,s)⟩`, the `M2`-column on the
`|1⟩|1⟩` block.
The superposition `U|t⟩ = ∑ₛ (M2)ₛₜ|s⟩` is transported factorwise through `threeQuditIso` using its
linearity (`map_sum` / `map_smul`) — the `Evolution.op` form of
`congr_ccontrolledUnitary_evolvePure_eleven`. -/
private theorem congr_ccontrolledUnitary_op_single_active (U : Evolution qubit)
    (M2 : Matrix (Fin 2) (Fin 2) ℂ) (hU : U.op = Matrix.toEuclideanCLM (𝕜 := ℂ) M2) (t : Fin 2) :
    (Evolution.congr threeQuditIso (ccontrolledUnitary U)).op
        (EuclideanSpace.single (Concrete.threeQubitIndex (1, 1, t)) 1)
      = ∑ s : Fin 2, M2 s t •
          EuclideanSpace.single (Concrete.threeQubitIndex (1, 1, s)) (1 : ℂ) := by
  have hUt : U.op (quditBasis t).vec = ∑ s : Fin 2, M2 s t • EuclideanSpace.single s (1 : ℂ) := by
    rw [hU, quditBasis_vec]; exact Matrix.toEuclideanCLM_apply_single M2 t
  -- The transported gate maps `|threeQubitIndex (1,1,s)⟩` to the packed `|1⟩|1⟩|s⟩` basis state.
  have hrec : ∀ s : Fin 2, threeQuditIso.toIsometry
        (EuclideanSpace.single (1 : Fin 2) (1 : ℂ) ⊗ₜ[ℂ]
          (EuclideanSpace.single (1 : Fin 2) (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single s (1 : ℂ)))
      = EuclideanSpace.single (Concrete.threeQubitIndex (1, 1, s)) (1 : ℂ) := fun s => by
    rw [show (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = (quditBasis 1).vec from
        (quditBasis_vec 1).symm,
      show (EuclideanSpace.single s (1 : ℂ)) = (quditBasis s).vec from (quditBasis_vec s).symm,
      ← PureState.tmul_vec, ← PureState.tmul_vec, ← PureState.congr_vec,
      threeQuditIso_congr_quditBasis, quditBasis_vec]
  erw [← quditBasis_vec, ← Evolution.evolvePure_vec,
    congr_ccontrolledUnitary_evolvePure_eleven U t, PureState.congr_vec,
    PureState.tmul_vec, PureState.tmul_vec, quditBasis_vec,
    Evolution.evolvePure_vec, hUt]
  -- Transport the superposition `U|t⟩ = ∑ₛ (M2)ₛₜ|s⟩` factorwise: the composite
  -- `X ↦ threeQuditIso (|1⟩ ⊗ |1⟩ ⊗ X)` is a linear map, so it commutes with the finite sum.
  refine (map_sum (threeQuditIso.toIsometry.toLinearMap ∘ₗ
      (TensorProduct.mk ℂ (qudit 2).space (qudit 2 ⊗ qudit 2).space
        (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))) ∘ₗ
      (TensorProduct.mk ℂ (qudit 2).space (qudit 2).space
        (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))))
    (fun s => M2 s t • EuclideanSpace.single s (1 : ℂ)) Finset.univ).trans ?_
  refine Finset.sum_congr rfl (fun s _ => ?_)
  erw [map_smul]
  congr 1
  exact hrec s

set_option maxRecDepth 10000 in
/-- **The operator–matrix bridge for the doubly-controlled gate** (Nielsen & Chuang, Exercise 4.44).
If a single-qubit evolution `U` has matrix `M2` (`U.op = toEuclideanCLM M2`), then the
doubly-controlled gate `ccontrolledUnitary U = C²(U)` — a gate on the composite three-qubit system
`qubit ⊗ (qubit ⊗ qubit)` — transported along the register identification `threeQuditIso` to the
eight-level register `qudit 8` is exactly the explicit `Fin 8` matrix `Concrete.ccontrolledMatFin8
M2 = C²(M2)` (`toEuclideanCLM` of it).

Since `deutschGate α = ccontrolledUnitary (iRxGate (πα))` (definitionally), instantiating this at `U
= iRxGate (πα)`, `M2 = Concrete.iRxMat (πα)` (via `iRxGate_op`) reads the physical Deutsch gate as
the concrete doubly-controlled matrix on which the matrix-level reachability argument of Exercise
4.44 operates.

The proof evaluates both continuous linear maps on the computational basis `|threeQubitIndex p⟩` of
`qudit 8` (`Module.Basis.ext`). On each of the four control patterns, the transported `C²(U)` action
(`congr_ccontrolledUnitary_evolvePure_eleven` / `_fixed`) is matched against the corresponding
column of `ccontrolledMatFin8 M2` (`ccontrolledMat_col_sum_active` / `_inactive`); the active
`|1⟩|1⟩` block uses that `U` is linear, transporting `U|t⟩` factorwise through `threeQuditIso`.

(`maxRecDepth` is raised because matching each transported-gate column against the matrix column
unfolds the `Matrix.toEuclideanCLM` `⋆`-algebra coercion, whose definitional chain is deep.) -/
theorem ccontrolledUnitary_congr_threeQuditIso_op {U : Evolution qubit}
    {M2 : Matrix (Fin 2) (Fin 2) ℂ} (hU : U.op = Matrix.toEuclideanCLM (𝕜 := ℂ) M2) :
    (Evolution.congr threeQuditIso (ccontrolledUnitary U)).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (Concrete.ccontrolledMatFin8 M2) := by
  apply ContinuousLinearMap.coe_injective
  refine Module.Basis.ext (EuclideanSpace.basisFun (Fin 8) ℂ).toBasis (fun j => ?_)
  obtain ⟨⟨c₁, c₂, t⟩, rfl⟩ := Concrete.threeQubitIndex.surjective j
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  -- Both continuous linear maps are compared on `|threeQubitIndex (c₁,c₂,t)⟩`; the transported
  -- gate's action (`_op_single_fixed`/`_active`) matches the corresponding column of the matrix
  -- (`ccontrolledMatFin8_toEuclideanCLM_apply` + `_col_sum_inactive`/`_active`). `exact` bridges
  -- the `↑` (continuous-linear-map to linear-map) coercion introduced by `Module.Basis.ext`.
  fin_cases c₁ <;> fin_cases c₂
  · exact (congr_ccontrolledUnitary_op_single_fixed U 0 0 t (by decide)).trans
      ((ccontrolledMatFin8_toEuclideanCLM_apply M2 (0, 0, t)).trans
        (ccontrolledMat_col_sum_inactive M2 0 0 t (by decide))).symm
  · exact (congr_ccontrolledUnitary_op_single_fixed U 0 1 t (by decide)).trans
      ((ccontrolledMatFin8_toEuclideanCLM_apply M2 (0, 1, t)).trans
        (ccontrolledMat_col_sum_inactive M2 0 1 t (by decide))).symm
  · exact (congr_ccontrolledUnitary_op_single_fixed U 1 0 t (by decide)).trans
      ((ccontrolledMatFin8_toEuclideanCLM_apply M2 (1, 0, t)).trans
        (ccontrolledMat_col_sum_inactive M2 1 0 t (by decide))).symm
  · exact (congr_ccontrolledUnitary_op_single_active U M2 hU t).trans
      ((ccontrolledMatFin8_toEuclideanCLM_apply M2 (1, 1, t)).trans
        (ccontrolledMat_col_sum_active M2 t)).symm

/-- **The physical Deutsch gate `G = C²(iR_x(πα))` as its explicit `Fin 8` matrix** (Nielsen &
Chuang, Exercise 4.44). Transported along the register identification `threeQuditIso` to the
eight-level register `qudit 8`, the Deutsch gate `deutschGate α = ccontrolledUnitary (iRxGate (πα))`
is `toEuclideanCLM (Concrete.ccontrolledMatFin8 (Concrete.iRxMat (πα)))` — the doubly-controlled
matrix `C²(iR_x(πα))` its entire matrix-level reachability/compression development
(`Concrete.deutschDoublyControlledReachableMats`, `…deutschDataReachableCircuits`, …) is built from.

Stated over the unfolded form `ccontrolledUnitary (iRxGate (πα))` (definitionally `deutschGate α`,
which lives above this file in `NC/`); the instance of the general bridge
`ccontrolledUnitary_congr_threeQuditIso_op` at the Deutsch target `iRxGate (πα)`, whose matrix is
`Concrete.iRxMat (πα)` by `iRxGate_op`. -/
theorem deutschGate_congr_threeQuditIso_op (α : ℝ) :
    (Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (Real.pi * α)))).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ)
          (Concrete.ccontrolledMatFin8 (Concrete.iRxMat (Real.pi * α))) :=
  ccontrolledUnitary_congr_threeQuditIso_op (iRxGate_op (Real.pi * α))

end

end AxQM
