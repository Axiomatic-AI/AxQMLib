/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.PureMarginalEntropy
import AxQM.Postulates.Composite

/-!
# AxQM — reduced-state transport and purification-entropy complementarity

Structural facts about how the reduced states `State.reducedLeft` / `State.reducedRight` interact
with the transport of a state along a system isomorphism (`State.congr`), together with the entropy
identity relating a state to the ancilla marginal of its purification. They are used in the
purification proof of **weak monotonicity** (N&C eq. (11.72) / Exercise 11.24, the "form-1"
strong-subadditivity inequality `S(A) + S(B) ≤ S(A,C) + S(B,C)`) and hence the **second-entry
subadditivity of the conditional entropy** (N&C Theorem 11.16, eq. (11.118)): that argument purifies
a state, applies strong subadditivity to a marginal of the purification, and reads the resulting
entropies back onto the original state's marginals through exactly these transport lemmas. Compare
`AxQM/Postulates/API/SubadditivityReformulations.lean` and
`AxQM/Postulates/API/PartialTraceReassoc.lean`, whose companions these are.

## Main results

* `AxQM.State.congr_trans` — transports compose:
  `ρ.congr (e.trans f) = (ρ.congr e).congr f`.
* `AxQM.State.congr_refl` / `AxQM.QSystem.Iso.trans_symm_self` /
  `AxQM.QSystem.Iso.symm_trans_self` — the unit, right-inverse and left-inverse laws of the
  transport backbone.
* `AxQM.State.reducedLeft_congr_tmul_refl` — reshaping the traced-out right factor of a
  bipartite state leaves the left marginal unchanged.
* `AxQM.State.reducedLeft_congr_assoc_symm` — the left marginal after de-associating
  `(X ⊗ Y) ⊗ Z → X ⊗ (Y ⊗ Z)` is the iterated left marginal (trace `Z`, then `Y`). This is the
  single canonical associator–left-marginal lemma that applies the commutation fact
  `partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv`; the reverse face
  `State.reducedLeft_reducedLeft_congr_assoc` (`Postulates/API/SubadditivityReformulations`)
  reuses it (via the transport unit/inverse laws) rather than re-proving the commutation fact.
* `AxQM.State.vonNeumannEntropy_purify_reducedRight` — a state and the ancilla marginal of
  its canonical purification are isentropic, `S(ρ) = S(Tr_S ρ.purify)`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Transports compose.** Carrying a state along `e : S ≃ₛ T` and then along `f : T ≃ₛ U` is the
same as carrying it along the composite `e.trans f`. The `State` functoriality of the transport
backbone (`QSystem.Iso.trans`), the density-operator companion of `PureState.congr_trans` (stated in
the same orientation, `congr (e.trans f) = congr f ∘ congr e`). -/
theorem State.congr_trans {S T U : QSystem} (e : S ≃ₛ T) (f : T ≃ₛ U) (ρ : State S) :
    ρ.congr (e.trans f) = (ρ.congr e).congr f := by
  apply State.ext
  simp only [State.congr_op]
  rfl

/-- **Transport along the identity is the identity**: `ρ.congr (refl S) = ρ`. The unit law of the
transport backbone, paired with `State.congr_trans`; conjugating by the identity isometry
(`LinearIsometryEquiv.conjStarAlgEquiv_refl`) fixes the density operator. -/
theorem State.congr_refl (ρ : State S) : ρ.congr (QSystem.Iso.refl S) = ρ := by
  apply State.ext
  simp only [State.congr_op, QSystem.Iso.refl_toIsometry,
    LinearIsometryEquiv.conjStarAlgEquiv_refl, StarAlgEquiv.coe_refl, id_eq]

/-- **A system isomorphism composed with its inverse is the identity**: `e.trans e.symm = refl S`.
The right-inverse law of the transport backbone (`QSystem.Iso.trans`/`symm`/`refl`), a
consequence of `LinearIsometryEquiv.self_trans_symm`. -/
theorem QSystem.Iso.trans_symm_self {S T : QSystem} (e : S ≃ₛ T) :
    e.trans e.symm = QSystem.Iso.refl S :=
  congrArg QSystem.Iso.mk (LinearIsometryEquiv.self_trans_symm e.toIsometry)

/-- **A system isomorphism composed after its inverse is the identity**: `e.symm.trans e = refl T`.
The left-inverse law of the transport backbone (`QSystem.Iso.trans`/`symm`/`refl`), the companion of
the right-inverse law `QSystem.Iso.trans_symm_self`, a consequence of
`LinearIsometryEquiv.symm_trans_self`. -/
theorem QSystem.Iso.symm_trans_self {S T : QSystem} (e : S ≃ₛ T) :
    e.symm.trans e = QSystem.Iso.refl T :=
  congrArg QSystem.Iso.mk (LinearIsometryEquiv.symm_trans_self e.toIsometry)

/-- **Reshaping the traced-out factor leaves the left marginal unchanged.** For a bipartite state
`ρ` on `S ⊗ T` and a system isomorphism `g : T ≃ₛ T'` reshaping only the right factor, transporting
along `id ⊗ g` and then tracing out the (reshaped) right factor gives the same left marginal as
tracing out the original right factor: `Tr_{T'} ((id ⊗ g) ρ (id ⊗ g)⁻¹) = Tr_T ρ`. The left marginal
does not see a unitary applied to the discarded factor (lemma
`LinearMap.partialTraceRight_conjStarAlgEquiv_congrIsometry`, up to basis-independence of the
partial trace). -/
theorem State.reducedLeft_congr_tmul_refl {S T T' : QSystem} (g : T ≃ₛ T') (ρ : State (S ⊗ T)) :
    (ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl S) g)).reducedLeft = ρ.reducedLeft := by
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  change (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ T'.space)
      (((QSystem.Iso.tmul (QSystem.Iso.refl S) g).toIsometry.conjStarAlgEquiv ρ.op).toLinearMap)) =
      (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ T.space) ρ.op.toLinearMap)
  have hbasis := LinearMap.partialTraceRight_eq_of_basis (stdOrthonormalBasis ℂ T'.space)
    ((stdOrthonormalBasis ℂ T.space).map g.toIsometry)
    (((QSystem.Iso.tmul (QSystem.Iso.refl S) g).toIsometry.conjStarAlgEquiv ρ.op).toLinearMap)
  exact hbasis.trans (LinearMap.partialTraceRight_conjStarAlgEquiv_congrIsometry
    (stdOrthonormalBasis ℂ T.space) g.toIsometry ρ.op)

/-- **The left marginal is stable under de-association.** For a state `ω` on `(X ⊗ Y) ⊗ Z`,
re-associating to `X ⊗ (Y ⊗ Z)` and tracing out the whole right block `Y ⊗ Z` gives the same
`X`-marginal as tracing out `Z` (`reducedLeft`) and then `Y` (`reducedLeft`):
`Tr_{Y⊗Z} (assoc⁻¹ ω) = Tr_Y (Tr_Z ω)`. Reduces to the commutation lemma
`LinearMap.partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv` (with the
associator roundtrip absorbed), up to basis-independence of the partial trace. -/
theorem State.reducedLeft_congr_assoc_symm {X Y Z : QSystem} (ω : State ((X ⊗ Y) ⊗ Z)) :
    (ω.congr (QSystem.assoc X Y Z).symm).reducedLeft = ω.reducedLeft.reducedLeft := by
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  set e := TensorProduct.assocIsometry ℂ X.space Y.space Z.space with he
  set ceq := e.conjStarAlgEquiv with hceq
  have key := LinearMap.partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv
    (stdOrthonormalBasis ℂ Y.space) (stdOrthonormalBasis ℂ Z.space) (ceq ω.op)
  have hcancel := StarAlgEquiv.symm_apply_apply ceq ω.op
  have keyed : LinearMap.partialTraceRight (stdOrthonormalBasis ℂ Y.space)
        (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ Z.space)
          ((ceq.symm (ceq ω.op)).toLinearMap)) =
      LinearMap.partialTraceRight
        ((stdOrthonormalBasis ℂ Y.space).tensorProduct (stdOrthonormalBasis ℂ Z.space))
        (ceq ω.op).toLinearMap :=
    key
  rw [hcancel] at keyed
  clear key hcancel
  change LinearMap.partialTraceRight (stdOrthonormalBasis ℂ (Y ⊗ Z : QSystem).space)
      (((QSystem.assoc X Y Z).symm.toIsometry.conjStarAlgEquiv ω.op).toLinearMap) =
      LinearMap.partialTraceRight (stdOrthonormalBasis ℂ Y.space)
        (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ Z.space) ω.op.toLinearMap)
  rw [QSystem.assoc_symm_toIsometry]
  have hbasis2 := LinearMap.partialTraceRight_eq_of_basis
    (stdOrthonormalBasis ℂ (Y ⊗ Z : QSystem).space)
    ((stdOrthonormalBasis ℂ Y.space).tensorProduct (stdOrthonormalBasis ℂ Z.space))
    ((e.conjStarAlgEquiv ω.op).toLinearMap)
  exact hbasis2.trans keyed.symm

/-- **A state is isentropic with the ancilla marginal of its purification.** For any state `ρ` on
`S`, the canonical purification `ρ.purify` is a pure state on `S ⊗ R` (`R` a copy of `S`) whose left
marginal is `ρ` (`State.purify_reducedLeft_eq`); since the two reduced states of a pure bipartite
state have equal von Neumann entropy (`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`,
N&C Theorem 11.8(3)), `ρ` and the ancilla marginal `Tr_S ρ.purify` are isentropic:

`S(ρ) = S(Tr_S ρ.purify)`.

This is the entropy half of the purification-complementarity fact (`S(X) = S(X^c)` for a pure
composite) that turns strong subadditivity into weak monotonicity (N&C eq. (11.72) / Exercise 11.24)
and the Araki–Lieb triangle inequality. -/
theorem State.vonNeumannEntropy_purify_reducedRight (ρ : State S) :
    ρ.vonNeumannEntropy = ρ.purify.toState.reducedRight.vonNeumannEntropy := by
  rw [← PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight ρ.purify, ρ.purify_reducedLeft_eq]

end AxQM
