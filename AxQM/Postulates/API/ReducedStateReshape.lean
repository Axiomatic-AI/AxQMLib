/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ReducedStateComm

/-!
# AxQM — the reduced states under a per-factor tensor reshape

For a bipartite state `ρ` on `S ⊗ T`, `State.reducedLeft` traces out the *right* factor `T` and
`State.reducedRight` traces out the *left* factor `S`. This file records how these two marginals
behave when the state is transported (`State.congr`) along a reshape that acts on a **single**
tensor factor — `QSystem.Iso.tmul e (QSystem.Iso.refl _)` or `QSystem.Iso.tmul (QSystem.Iso.refl _)
e`. There are two faces:

* **Reshape the traced-out factor ⟹ the marginal is unchanged.** Applying a unitary to the factor
  that is about to be discarded cannot change the marginal.
  - `State.reducedLeft_congr_tmul_refl` (right factor reshaped; in `ReducedStateTransport`);
  - `State.reducedRight_congr_tmul_refl` (left factor reshaped) — its mirror, added here.
* **Reshape the kept factor ⟹ the marginal is conjugated.** A unitary on the surviving factor is
  carried through the partial trace and reappears conjugating the marginal.
  - `State.reducedLeft_congr_tmul_left` (left factor reshaped ⟹ `Tr_T · ↦ (Tr_T ·).congr`);
  - `State.reducedRight_congr_tmul_right` (right factor reshaped ⟹ `Tr_S · ↦ (Tr_S ·).congr`).

Together with `State.reducedLeft_congr_tmul_refl` this is the complete quartet of
"marginal of a state transported along a one-factor reshape" identities.

## Use

These `reducedRight` identities are used in the purification proof of **weak monotonicity**
(N&C eq. (11.72) / Exercise 11.24) — hence the second-entry subadditivity of the conditional
entropy (N&C Theorem 11.16, eq. (11.118)). That argument purifies a state,
applies strong subadditivity to a marginal of the purification, and reads the resulting entropies
back onto the original state's marginals; the reference is brought beside the traced block by the
reshape `QSystem.pullRefReshape = (assoc _ _ _).symm.trans (id ⊗ comm)`, whose `id ⊗ comm` step is a
kept-factor reshape whose `reducedRight` is exactly `State.reducedRight_congr_tmul_right`.

The `reducedLeft` reshaping lemmas (`AxQM/Postulates/API/ReducedStateTransport.lean`) rest on the
`partialTraceRight` naturality; the mirror `reducedRight` lemmas would need the `partialTraceLeft`
counterparts, which are not available. Rather than add them, the `reducedRight` identities here are
derived from their `reducedLeft` siblings through the factor-swap bridge
`State.reducedRight_congr_comm` (`AxQM/Postulates/API/ReducedStateComm.lean`): a `reducedRight`
goal is rewritten to a `reducedLeft` goal on the `QSystem.Iso.comm`-swapped state, where the
existing API applies. The swap-commutes-past-a-one-factor-reshape identity that makes this
routing go through is the naturality square `QSystem.Iso.tmul_trans_comm`
(`AxQM/Postulates/API/SystemIsoComm.lean`), instantiated with `h := refl` (left-factor reshape) or
`g := refl` (right-factor reshape). The one
lemma proved directly from the partial trace is `State.reducedLeft_congr_tmul_left` (kept-left
conjugation), which reuses the kept-factor equivariance
`LinearMap.restrictRight_comp_tensorMap_id` (generalized here to a space-changing map); its
`reducedRight` mirror follows from it via the bridge.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S S' T T' : QSystem}

/-- **Reshaping the traced-out left factor leaves the right marginal unchanged.** For a bipartite
state `ρ` on `S ⊗ T` and a reshape `g : S ≃ₛ S'` acting only on the left factor, transporting along
`g ⊗ id_T` and then tracing out the (reshaped) left factor gives the same right marginal as tracing
out the original left factor:

`(ρ.congr (g ⊗ id_T)).reducedRight = ρ.reducedRight`.

The `reducedRight` mirror of `State.reducedLeft_congr_tmul_refl`: the right marginal does not see a
unitary applied to the discarded left factor. Derived from that `reducedLeft` lemma by rewriting
both `reducedRight`s through the factor-swap bridge `State.reducedRight_congr_comm` and commuting
the swap past the reshape (`QSystem.Iso.tmul_trans_comm`, `h := refl`). -/
theorem State.reducedRight_congr_tmul_refl (g : S ≃ₛ S') (ρ : State (S ⊗ T)) :
    (ρ.congr (QSystem.Iso.tmul g (QSystem.Iso.refl T))).reducedRight = ρ.reducedRight := by
  rw [State.reducedRight_congr_comm (ρ.congr (QSystem.Iso.tmul g (QSystem.Iso.refl T))),
    State.reducedRight_congr_comm ρ, ← State.congr_trans, QSystem.Iso.tmul_trans_comm,
    State.congr_trans, State.reducedLeft_congr_tmul_refl]

/-- **Reshaping the kept left factor conjugates the left marginal.** For a bipartite state `ρ` on
`S ⊗ T` and a reshape `h : S ≃ₛ S'` acting only on the left factor, transporting along `h ⊗ id_T`
and then tracing out the right factor equals tracing out the right factor and then transporting the
`S`-marginal along `h`:

`(ρ.congr (h ⊗ id_T)).reducedLeft = ρ.reducedLeft.congr h`.

A unitary on the surviving (left) factor is carried through the partial trace and reappears
conjugating the marginal. Proved at the level of operators: the transported operator is the
conjugation `(h ⊗ 1) · (h ⊗ 1)⁻¹` of `ρ.op`, whose `partialTraceRight` is `h · h⁻¹` of
`partialTraceRight ρ.op` by the kept-factor equivariance
`LinearMap.restrictRight_comp_tensorMap_id` (applied inside the partial-trace sum). Its
`reducedRight` mirror `State.reducedRight_congr_tmul_right` follows from it through the factor-swap
bridge. -/
theorem State.reducedLeft_congr_tmul_left (h : S ≃ₛ S') (ρ : State (S ⊗ T)) :
    (ρ.congr (QSystem.Iso.tmul h (QSystem.Iso.refl T))).reducedLeft = ρ.reducedLeft.congr h := by
  set b := stdOrthonormalBasis ℂ T.space with hb
  -- Kept-factor equivariance of `restrictRight`: reshaping the (kept) left factor by `f` pulls `f`
  -- out of the restriction (`restrictRight_comp_tensorMap_id`, whose space-changing case
  -- this is; `restrictRight` only reads the right factor, which `f ⊗ id` fixes).
  have hr : ∀ (f : S.space →ₗ[ℂ] S'.space) (k) (w : S.space ⊗[ℂ] T.space),
      LinearMap.restrictRight b k (TensorProduct.map f LinearMap.id w)
        = f (LinearMap.restrictRight b k w) :=
    fun f k w => LinearMap.congr_fun (LinearMap.restrictRight_comp_tensorMap_id b f k) w
  apply State.ext
  apply ContinuousLinearMap.coe_injective
  simp only [State.reducedLeft_op, State.congr_op, QSystem.Iso.tmul_toIsometry,
    QSystem.Iso.refl_toIsometry, LinearMap.coe_toContinuousLinearMap]
  change LinearMap.partialTraceRight b
      (((TensorProduct.congrIsometry h.toIsometry
        (LinearIsometryEquiv.refl ℂ T.space)).conjStarAlgEquiv ρ.op).toLinearMap) =
      (h.toIsometry.conjStarAlgEquiv (LinearMap.toContinuousLinearMap
        (LinearMap.partialTraceRight b ρ.op.toLinearMap))).toLinearMap
  -- Unfold the two conjugations to plain `TensorProduct.map`/`LinearMap` compositions.
  have hcoe : ((TensorProduct.congrIsometry h.toIsometry
        (LinearIsometryEquiv.refl ℂ T.space)).conjStarAlgEquiv ρ.op).toLinearMap =
      TensorProduct.map h.toIsometry.toLinearMap LinearMap.id ∘ₗ ρ.op.toLinearMap ∘ₗ
        TensorProduct.map h.toIsometry.symm.toLinearMap LinearMap.id := by
    let ρopCLM : S.space ⊗[ℂ] T.space →L[ℂ] S.space ⊗[ℂ] T.space := ρ.op
    have hgen : ((TensorProduct.congrIsometry h.toIsometry
          (LinearIsometryEquiv.refl ℂ T.space)).conjStarAlgEquiv ρopCLM).toLinearMap =
        TensorProduct.map h.toIsometry.toLinearMap LinearMap.id ∘ₗ ρopCLM.toLinearMap ∘ₗ
          TensorProduct.map h.toIsometry.symm.toLinearMap LinearMap.id := by
      rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap, LinearEquiv.conj_apply,
        TensorProduct.toLinearEquiv_congrIsometry]
      simp only [TensorProduct.congr_symm, TensorProduct.toLinearMap_congr]
      rfl
    exact hgen
  have hrhs : (h.toIsometry.conjStarAlgEquiv (LinearMap.toContinuousLinearMap
        (LinearMap.partialTraceRight b ρ.op.toLinearMap))).toLinearMap =
      h.toIsometry.toLinearMap ∘ₗ LinearMap.partialTraceRight b ρ.op.toLinearMap ∘ₗ
        h.toIsometry.symm.toLinearMap := by
    rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap, LinearEquiv.conj_apply]
    simp only [LinearMap.coe_toContinuousLinearMap]
    rfl
  rw [hcoe, hrhs]
  -- Compute `partialTraceRight (map h 1 ∘ ρ.op ∘ map h⁻¹ 1)` slotwise and pull `h` out via `hr`.
  apply LinearMap.ext
  intro x
  rw [LinearMap.partialTraceRight_apply]
  simp only [LinearMap.comp_apply]
  erw [LinearMap.partialTraceRight_apply, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hr]
  congr 2

/-- **Reshaping the kept right factor conjugates the right marginal.** For a bipartite state `ρ` on
`S ⊗ T` and a reshape `h : T ≃ₛ T'` acting only on the right factor, transporting along `id_S ⊗ h`
and then tracing out the left factor equals tracing out the left factor and then transporting the
`T`-marginal along `h`:

`(ρ.congr (id_S ⊗ h)).reducedRight = ρ.reducedRight.congr h`.

The `reducedRight` mirror of `State.reducedLeft_congr_tmul_left`, and the exact identity the weak-
monotonicity purification proof uses to push the reference `R` beside the traced block (the
`id ⊗ comm` step of `QSystem.pullRefReshape`). Derived from the kept-left conjugation lemma by
rewriting the `reducedRight`s through the factor-swap bridge `State.reducedRight_congr_comm` and
commuting the swap past the reshape (`QSystem.Iso.tmul_trans_comm`, `g := refl`). -/
theorem State.reducedRight_congr_tmul_right (h : T ≃ₛ T') (ρ : State (S ⊗ T)) :
    (ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl S) h)).reducedRight = ρ.reducedRight.congr h := by
  rw [State.reducedRight_congr_comm (ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl S) h)),
    ← State.congr_trans, QSystem.Iso.tmul_trans_comm, State.congr_trans,
    State.reducedLeft_congr_tmul_left, State.reducedRight_congr_comm ρ]

end AxQM
