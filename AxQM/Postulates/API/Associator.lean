/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.SystemIso
import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM — the associator system isomorphism `A ⊗ (B ⊗ C) ≃ₛ (A ⊗ B) ⊗ C`

Composite systems built by the binary tensor `⊗` (`QSystem.compose`) are literally
right-nested or left-nested tensor products of the underlying spaces; the physicist regards
`A ⊗ (B ⊗ C)` and `(A ⊗ B) ⊗ C` as the same tripartite system. The **associator**
`QSystem.assoc` is the `QSystem.Iso` witnessing this, so a state / observable / … on one
nesting can be transported to the other via the `*.congr` transport of
`AxQM.Postulates.SystemIso`.

The underlying isometry is `(TensorProduct.assocIsometry ℂ A.space B.space C.space).symm`
(the inner-product-space associator `(A ⊗ B) ⊗ C ≃ₗᵢ A ⊗ (B ⊗ C)`, reversed).

It is the structural conversion the strong-subadditivity route needs: the tripartite state
lives on the right-nested `A ⊗ (B ⊗ C)`, but the `A ⊗ B`-marginal is read off after
re-associating to `(A ⊗ B) ⊗ C` and tracing out `C`
(see `AxQM/Postulates/API/StrongSubadditivity.lean`).

## Main definitions

* `AxQM.QSystem.assoc` — the associator system isomorphism
  `A ⊗ (B ⊗ C) ≃ₛ (A ⊗ B) ⊗ C`.
* `AxQM.QSystem.Iso.tmul` — the tensor product of two system isomorphisms,
  `(S ⊗ T) ≃ₛ (S' ⊗ T')`, the `⊗` of the transport backbone (a sibling of
  `QSystem.Iso.refl/symm/trans` and `QSystem.assoc`); it lets a structural conversion on one
  factor act inside a composite while the other factor is untouched.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable (A B C : QSystem)

/-- The **associator** system isomorphism `A ⊗ (B ⊗ C) ≃ₛ (A ⊗ B) ⊗ C`: the two nestings
of the tripartite composite are the same quantum system, re-bracketed. The underlying isometry
is the reversed inner-product associator
`(TensorProduct.assocIsometry ℂ A.space B.space C.space).symm`. -/
def QSystem.assoc : (A ⊗ (B ⊗ C)) ≃ₛ ((A ⊗ B) ⊗ C) :=
  ⟨(TensorProduct.assocIsometry ℂ A.space B.space C.space).symm⟩

@[simp]
theorem QSystem.assoc_toIsometry :
    (QSystem.assoc A B C).toIsometry =
      (TensorProduct.assocIsometry ℂ A.space B.space C.space).symm :=
  rfl

/-- The associator's **inverse** isometry is the *forward* `assocIsometry` (the two `.symm`s
cancel): `(QSystem.assoc A B C).symm.toIsometry = TensorProduct.assocIsometry ℂ …`. The `.symm`
companion of `QSystem.assoc_toIsometry`; extracted because the purification / marginal proofs that
re-associate a left-nested composite `(A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)` repeatedly need it to expose the
transported operator as a forward-associator conjugation. -/
@[simp]
theorem QSystem.assoc_symm_toIsometry :
    (QSystem.assoc A B C).symm.toIsometry =
      TensorProduct.assocIsometry ℂ A.space B.space C.space :=
  LinearIsometryEquiv.symm_symm _

/-- The **associator on a pure double tensor**: `(assoc A B C)(a ⊗ (b ⊗ c)) = (a ⊗ b) ⊗ c`.
Re-brackets a right-nested pure tensor to the left-nested form (the content of
`QSystem.assoc`, via `TensorProduct.assoc_symm_tmul`). -/
theorem assoc_toIsometry_tmul_tmul {A B C : QSystem} (a : A.space) (b : B.space) (c : C.space) :
    (QSystem.assoc A B C).toIsometry (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c)) = (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c := by
  rw [QSystem.assoc_toIsometry]; exact TensorProduct.assoc_symm_tmul a b c

/-- The **tensor product of two system isomorphisms** `e : S ≃ₛ S'` and `f : T ≃ₛ T'`, a system
isomorphism `(S ⊗ T) ≃ₛ (S' ⊗ T')` whose underlying isometry is
`TensorProduct.congrIsometry e.toIsometry f.toIsometry`.  The `⊗` of the transport backbone: it
lets a structural conversion on one factor (e.g. an associator) act inside a composite while the
other factor is left untouched — the direct sibling of `QSystem.Iso.refl/symm/trans`. -/
def QSystem.Iso.tmul {S S' T T' : QSystem} (e : S ≃ₛ S') (f : T ≃ₛ T') :
    (S ⊗ T) ≃ₛ (S' ⊗ T') :=
  ⟨TensorProduct.congrIsometry e.toIsometry f.toIsometry⟩

/-- The action of `QSystem.Iso.tmul e f` on a pure tensor: `(e ⊗ f)(x ⊗ y) = e x ⊗ f y`. -/
@[simp]
theorem QSystem.Iso.tmul_toIsometry_tmul {S S' T T' : QSystem} (e : S ≃ₛ S') (f : T ≃ₛ T')
    (x : S.space) (y : T.space) :
    (QSystem.Iso.tmul e f).toIsometry (x ⊗ₜ[ℂ] y)
      = e.toIsometry x ⊗ₜ[ℂ] f.toIsometry y :=
  TensorProduct.congrIsometry_tmul e.toIsometry f.toIsometry x y

/-- The tensor of two identity isomorphisms is the identity: `(refl S ⊗ refl T) = refl (S ⊗ T)`
(mirroring `TensorProduct.congrIsometry_refl_refl`). -/
@[simp]
theorem QSystem.Iso.tmul_refl_refl (S T : QSystem) :
    QSystem.Iso.tmul (QSystem.Iso.refl S) (QSystem.Iso.refl T) = QSystem.Iso.refl (S ⊗ T) :=
  congrArg QSystem.Iso.mk TensorProduct.congrIsometry_refl_refl

/-- The inverse of a tensor of isomorphisms is the tensor of the inverses:
`(e ⊗ f)⁻¹ = e⁻¹ ⊗ f⁻¹` (mirroring `TensorProduct.congrIsometry_symm`). -/
theorem QSystem.Iso.tmul_symm {S S' T T' : QSystem} (e : S ≃ₛ S') (f : T ≃ₛ T') :
    (QSystem.Iso.tmul e f).symm = QSystem.Iso.tmul e.symm f.symm :=
  congrArg QSystem.Iso.mk (TensorProduct.congrIsometry_symm e.toIsometry f.toIsometry)

end AxQM
