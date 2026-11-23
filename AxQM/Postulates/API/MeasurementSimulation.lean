/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.SwapLinearity
import AxQM.Postulates.API.SchmidtDecomposition
import AxQM.Postulates.API.KitaevPhaseEstimation

/-!
# Measurement simulation across a bipartite pure state

Facts behind **Nielsen & Chuang, Proposition 12.14** (the LOCC
reduction, `AxQM/NC/Ch12/Proposition12_14.lean`). The crux of that proposition is that a measurement
performed by *Bob* on one factor of a bipartite pure state can be *simulated* by a measurement
performed by *Alice* on the other factor — up to a local unitary. The three facts below are the
ingredients of that proof. The `SWAP`-naturality lemma `Evolution.swap_op_mapL` and the
`SWAP`-linearity lemmas they build on are in `AxQM/Postulates/API/SwapLinearity.lean`.

* `Measurement.onRight_op_apply_eq_swap_onLeft_of_swapSymmetric` — the **mirror identity**: on a
  swap-symmetric bipartite pure state, Bob's operator on the right factor equals `SWAP` applied to
  Alice's (same) operator on the left factor, `(1 ⊗ Mⱼ)|ψ⟩ = SWAP((Mⱼ ⊗ 1)|ψ⟩)`. Used in
  Proposition 12.14.
* `Measurement.postMeasurement_pure` — the general **pure post-measurement bridge**: measuring a
  pure state `ψ` collapses it to the normalized vector `Mᵢ|ψ⟩ / ‖Mᵢ|ψ⟩‖`, i.e. the post-measurement
  `State` (`Measurement.postMeasurement`) is `(PureState.normalize (Mᵢ|ψ⟩)).toState`. (Plus the
  supporting `Measurement.op_ne_zero_of_bornProb_ne_zero`.)
* `PureState.sameSchmidtCoeffs_swap_evolvePure` — swapping the two factors of a bipartite pure state
  preserves its Schmidt coefficients: `SWAP|ξ⟩` and `|ξ⟩` have identical Schmidt coefficients.

-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A possible outcome has nonzero post-measurement vector.** If outcome `i` of measurement `m` on
the pure state `ψ` has nonzero Born probability, then `Mᵢ|ψ⟩ ≠ 0` (since the probability is
`‖Mᵢ|ψ⟩‖²`). -/
theorem Measurement.op_ne_zero_of_bornProb_ne_zero {ι : Type*} [Fintype ι]
    (m : Measurement ι S) (ψ : PureState S) (i : ι)
    (hp : m.bornProb ψ.toState i ≠ 0) : m.op i ψ.vec ≠ 0 := by
  intro h
  apply hp
  rw [m.bornProb_toState_eq_normSq ψ i, h, norm_zero]
  norm_num

/-- **Mirror identity for a swap-symmetric bipartite pure state.** On `S ⊗ S` with a swap-symmetric
state `ψ` (`SWAP|ψ⟩ = |ψ⟩`), Bob's operator `Mⱼ` on the right factor equals `SWAP` applied to
Alice's `Mⱼ` on the left factor: `(1 ⊗ Mⱼ)|ψ⟩ = SWAP((Mⱼ ⊗ 1)|ψ⟩)`. The crux of
Proposition 12.14 (equal Born probabilities, measurement simulation): it
follows from the `SWAP`-naturality `Evolution.swap_op_mapL` once swap-symmetry `SWAP|ψ⟩ = |ψ⟩` is
substituted. -/
theorem Measurement.onRight_op_apply_eq_swap_onLeft_of_swapSymmetric {ι : Type*} [Fintype ι]
    (m : Measurement ι S) {ψ : PureState (S ⊗ S)}
    (hψ : Evolution.swap.evolvePure ψ = ψ) (j : ι) :
    ((m.onRight S).op j) ψ.vec
      = (Evolution.swap (S := S)).op (((m.onLeft S).op j) ψ.vec) := by
  have hswpsi : (Evolution.swap (S := S)).op ψ.vec = ψ.vec := by
    rw [← Evolution.evolvePure_vec, hψ]
  have h := Evolution.swap_op_mapL (m.op j) ψ.vec
  rw [hswpsi] at h
  rw [Measurement.onRight_op, Measurement.onLeft_op]
  exact h.symm

/-- **Pure post-measurement bridge (Postulate 4 on a pure state).** Measuring `m` on a pure state
`ψ` and obtaining a possible outcome `i` collapses the system to the normalized vector
`Mᵢ|ψ⟩ / ‖Mᵢ|ψ⟩‖`: the post-measurement `State` `m.postMeasurement ψ.toState i` equals
`(PureState.normalize (Mᵢ|ψ⟩)).toState`. The general form of the observable-specific collapse lemmas
(`Observable.postMeasurement_signMeasurement_plus/minus`). Proof: the post-measurement operation on
`|ψ⟩⟨ψ|` is `Mᵢ|ψ⟩⟨ψ|Mᵢ† = |Mᵢψ⟩⟨Mᵢψ|` with trace `‖Mᵢψ‖²`, and the normalized rank-one folds the
`‖Mᵢψ‖⁻²` factor into `|normalize(Mᵢψ)⟩⟨normalize(Mᵢψ)|`. -/
theorem Measurement.postMeasurement_pure {ι : Type*} [Fintype ι]
    (m : Measurement ι S) (ψ : PureState S) (i : ι)
    (hp : m.bornProb ψ.toState i ≠ 0) (hv : m.op i ψ.vec ≠ 0) :
    m.postMeasurement ψ.toState i hp = (PureState.normalize (m.op i ψ.vec) hv).toState := by
  apply State.ext
  have hpost : ContinuousLinearMap.postOp m.op ψ.toState.op i
      = InnerProductSpace.rankOne ℂ (m.op i ψ.vec) (m.op i ψ.vec) := by
    simp only [ContinuousLinearMap.postOp, PureState.toState_op,
      InnerProductSpace.rankOne_comp, ContinuousLinearMap.adjoint_adjoint,
      InnerProductSpace.comp_rankOne]
  have htr : RCLike.re (LinearMap.trace ℂ S.space
      (InnerProductSpace.rankOne ℂ (m.op i ψ.vec) (m.op i ψ.vec) : S.space →ₗ[ℂ] S.space))
      = ‖m.op i ψ.vec‖ ^ 2 := by
    rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq]
  rw [Measurement.postMeasurement_op, ContinuousLinearMap.postState, hpost, htr,
    PureState.toState_op, PureState.normalize_vec, InnerProductSpace.rankOne_smul_smul_self]
  congr 1
  rw [map_inv₀, Complex.conj_ofReal]
  push_cast
  ring

/-- **Swapping the factors preserves the Schmidt coefficients.** For a bipartite pure state `ξ` on
`S ⊗ S`, the swapped state `SWAP|ξ⟩` has the same Schmidt coefficients as `|ξ⟩`
(`PureState.SameSchmidtCoeffs`). From a Schmidt decomposition `|ξ⟩ = ∑ᵢ λᵢ |aᵢ⟩|bᵢ⟩`, applying
`SWAP` gives `SWAP|ξ⟩ = ∑ᵢ λᵢ |bᵢ⟩|aᵢ⟩`, a Schmidt decomposition with the *same* coefficients `λᵢ`
and the orthonormal Schmidt bases exchanged. -/
theorem PureState.sameSchmidtCoeffs_swap_evolvePure (ξ : PureState (S ⊗ S)) :
    (Evolution.swap.evolvePure ξ).SameSchmidtCoeffs ξ := by
  obtain ⟨n, l, a, b, h⟩ := ξ.exists_isSchmidtDecomposition
  obtain ⟨hpos, ha, hb, _hnorm, hξ⟩ := h
  refine ⟨n, l, b, a, a, b, hpos, hb, ha, ha, hb, ?_, hξ⟩
  rw [Evolution.evolvePure_vec, hξ]
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun i _ => ?_))
  simp only [TensorProduct.smul_tmul', Evolution.swap_op_tmul, TensorProduct.tmul_smul]
  rfl

end AxQM
