/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TensorPowState
import AxQM.Postulates.API.Ensemble

/-!
# AxQM.Postulates.API — the i.i.d. product ensemble `{p_J, |ψ_J⟩}` and `ρ^⊗n`

For an **ensemble of pure states** `e = {pⱼ, |ψⱼ⟩}` (Nielsen & Chuang §2.4.1) with density
operator `ρ = e.toState = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|`, its **`n`-fold i.i.d. product ensemble** models `n`
independent uses of the source: it emits the product state `|ψ_J⟩ = |ψ_{j₁}⟩ ⊗ ⋯ ⊗ |ψ_{jₙ}⟩` with
probability `p_J = p_{j₁} ⋯ p_{jₙ}`, over all index sequences `J = (j₁, …, jₙ)`. This is the source
model of Nielsen & Chuang Exercise 12.8 (compression of an ensemble of quantum states, eq. (12.61)).

This file records that ensemble — `Ensemble.iidPow` — and the key bridge tying it to the
tensor-power state of the average:

* **`Ensemble.iidPow_toState`**: `(e.iidPow n).toState = e.toState.tensorPow n`, i.e. the density
  operator of the product ensemble is `ρ^⊗n`.

The bridge is the distributivity `∑_J (∏ᵢ pⱼ) • (⨂ᵢ |ψ_{Jᵢ}⟩⟨ψ_{Jᵢ}|) = ⨂ᵢ (∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|)` —
the multilinearity of the `n`-ary tensor `⨂` over the finite sum in each factor
(`MultilinearMap.map_sum` for `PiTensorProduct.tprod`, `map_smul_univ` to pull the products of
weights out), matched against the operator sum of `iidPow` factor by factor. Its per-copy input is
the *n-ary rank-one tensor identity*

* **`PureState.piTensor_toState`**: `(⨂ₚ i, ψ i).toState = ⨂ₚ i, (ψ i).toState`, the `n`-ary
  analogue of the binary `PureState.toState_tmul` — `|⨂ᵢ ψᵢ⟩⟨⨂ᵢ ψᵢ| = ⨂ᵢ |ψᵢ⟩⟨ψᵢ|`.

The ensemble-average-fidelity reliability of the Schumacher scheme (Exercise 12.8) is in
`AxQM/NC/Ch12/`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2, Exercise 12.8, eq. (12.61).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : ι → QSystem}

/-- **The `n`-ary rank-one tensor identity.** For a finite family of pure states
`ψ : ∀ i, PureState (S i)`, the density operator of the product pure state `⨂ₚ i, ψ i` is the
product of the individual density operators: `|⨂ᵢ ψᵢ⟩⟨⨂ᵢ ψᵢ| = ⨂ᵢ |ψᵢ⟩⟨ψᵢ|`, i.e.
`(⨂ₚ i, ψ i).toState = ⨂ₚ i, (ψ i).toState`. The `n`-ary analogue of the binary
`PureState.toState_tmul`.

Proof: both sides are rank-one / `mapCLM` operators that agree on every elementary tensor `⨂ₜ xᵢ` —
the left gives `⟨⨂ᵢ ψᵢ, ⨂ᵢ xᵢ⟩ • ⨂ᵢ ψᵢ = (∏ᵢ ⟨ψᵢ, xᵢ⟩) • ⨂ᵢ ψᵢ`
(`InnerProductSpace.rankOne_apply`, `PiTensorProduct.inner_tprod_tprod`) and the right gives
`⨂ᵢ (⟨ψᵢ, xᵢ⟩ • ψᵢ) = (∏ᵢ ⟨ψᵢ, xᵢ⟩) • ⨂ᵢ ψᵢ` (`PiTensorProduct.mapCLM_tprod`,
`MultilinearMap.map_smul_univ`) — so they are equal by `PiTensorProduct.ext`. -/
theorem PureState.piTensor_toState (ψ : ∀ i, PureState (S i)) :
    (⨂ₚ i, ψ i).toState = ⨂ₚ i, (ψ i).toState := by
  apply State.ext
  rw [State.piTensor_op, PureState.toState_op, PureState.piTensor_vec]
  have key : ∀ x : (i : ι) → (S i).space,
      (((rankOne ℂ) (⨂ₜ[ℂ] i, (ψ i).vec)) (⨂ₜ[ℂ] i, (ψ i).vec)) (⨂ₜ[ℂ] i, x i)
        = (PiTensorProduct.mapCLM fun i => (ψ i).toState.op) (⨂ₜ[ℂ] i, x i) := by
    intro x
    rw [InnerProductSpace.rankOne_apply, PiTensorProduct.mapCLM_tprod,
      PiTensorProduct.inner_tprod_tprod]
    simp only [PureState.toState_op, InnerProductSpace.rankOne_apply]
    rw [MultilinearMap.map_smul_univ]
    simp only [RingHom.id_apply]
  exact ContinuousLinearMap.ext_tprod key

/-- The action of `(⨂ₚ i, ψ i).toState.op` on an elementary tensor `⨂ₜ xᵢ`, obtained from
`PureState.piTensor_toState`: `|⨂ᵢ ψᵢ⟩⟨⨂ᵢ ψᵢ| (⨂ᵢ xᵢ) = ⨂ᵢ (|ψᵢ⟩⟨ψᵢ| xᵢ)`. The per-copy input to
`Ensemble.iidPow_toState`. -/
theorem PureState.piTensor_toState_op_tprod (ψ : ∀ i, PureState (S i)) (x : ∀ i, (S i).space) :
    (⨂ₚ i, ψ i).toState.op (⨂ₜ[ℂ] i, x i) = ⨂ₜ[ℂ] i, (ψ i).toState.op (x i) := by
  rw [PureState.piTensor_toState, State.piTensor_op]
  exact PiTensorProduct.mapCLM_tprod (fun i => (ψ i).toState.op) x

variable {T : QSystem}

/-- **The `n`-fold i.i.d. product ensemble** of an ensemble `e = {pⱼ, |ψⱼ⟩}` (Nielsen & Chuang
Exercise 12.8): `n` independent uses of the source `e`, indexed by length-`n` sequences
`J = (j₁, …, jₙ)` (packaged as `Fin (e.card ^ n)` via `finFunctionFinEquiv`). It emits the product
pure state `|ψ_J⟩ = ⨂ᵢ |ψ_{Jᵢ}⟩` with probability `p_J = ∏ᵢ p_{Jᵢ}`. The probabilities are
non-negative products and sum to `∏ᵢ (∑ⱼ pⱼ) = ∏ᵢ 1 = 1` (`Finset.prod_univ_sum`), so this is a
genuine `Ensemble (T ^⊗ₛ n)`. Its density operator is `ρ^⊗n` (`Ensemble.iidPow_toState`). -/
def Ensemble.iidPow (e : Ensemble T) (n : ℕ) : Ensemble (T ^⊗ₛ n) where
  card := e.card ^ n
  prob j := ∏ i, e.prob (finFunctionFinEquiv.symm j i)
  states j := ⨂ₚ i, e.states (finFunctionFinEquiv.symm j i)
  prob_nonneg j := Finset.prod_nonneg fun i _ => e.prob_nonneg _
  sum_prob := by
    rw [Equiv.sum_comp finFunctionFinEquiv.symm (fun J => ∏ i, e.prob (J i)),
      ← Fintype.piFinset_univ, ← Finset.prod_univ_sum,
      Finset.prod_congr rfl (fun i _ => e.sum_prob), Finset.prod_const_one]

@[simp]
theorem Ensemble.iidPow_prob (e : Ensemble T) (n : ℕ) (j : Fin (e.card ^ n)) :
    (e.iidPow n).prob j = ∏ i, e.prob (finFunctionFinEquiv.symm j i) := rfl

@[simp]
theorem Ensemble.iidPow_states (e : Ensemble T) (n : ℕ) (j : Fin (e.card ^ n)) :
    (e.iidPow n).states j = ⨂ₚ i, e.states (finFunctionFinEquiv.symm j i) := rfl

/-- **The i.i.d. product ensemble's density operator is the tensor-power state `ρ^⊗n`**
(Nielsen & Chuang Exercise 12.8, the identity `∑_J p_J |ψ_J⟩⟨ψ_J| = ρ^⊗n` with
`ρ = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|`): `(e.iidPow n).toState = e.toState.tensorPow n`.

Proof. Both operators agree on every elementary tensor `⨂ₜ xᵢ`. The right side
`ρ^⊗n = ⨂ᵢ ρ` distributes the sum `ρ = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|` in each factor by multilinearity of
`⨂ₜ` (`MultilinearMap.map_sum` then `map_smul_univ`), giving
`∑_J (∏ᵢ p_{Jᵢ}) • ⨂ᵢ (|ψ_{Jᵢ}⟩⟨ψ_{Jᵢ}| xᵢ)`. The left side is the ensemble operator sum
`∑_J p_J • |ψ_J⟩⟨ψ_J|` whose each summand acts as `⨂ᵢ (|ψ_{Jᵢ}⟩⟨ψ_{Jᵢ}| xᵢ)`
(`PureState.piTensor_toState_op_tprod`), matched to the right after reindexing the sum over
sequences (`finFunctionFinEquiv`). -/
theorem Ensemble.iidPow_toState (e : Ensemble T) (n : ℕ) :
    (e.iidPow n).toState = e.toState.tensorPow n := by
  apply State.ext
  rw [State.tensorPow_op]
  have key : ∀ x : Fin n → T.space,
      (e.iidPow n).toState.op (⨂ₜ[ℂ] i, x i)
        = (PiTensorProduct.mapCLM fun _ : Fin n => e.toState.op) (⨂ₜ[ℂ] i, x i) := by
    intro x
    have hR : (PiTensorProduct.mapCLM fun _ : Fin n => e.toState.op) (⨂ₜ[ℂ] i, x i)
        = ∑ J : Fin n → Fin e.card, (∏ i, (e.prob (J i) : ℂ)) •
            (⨂ₜ[ℂ] i, (e.states (J i)).toState.op (x i)) := by
      rw [PiTensorProduct.mapCLM_tprod]
      simp_rw [Ensemble.toState_op, sum_apply, smul_apply]
      rw [MultilinearMap.map_sum]
      simp_rw [MultilinearMap.map_smul_univ]
      simp only [RingHom.id_apply]
    rw [hR, Ensemble.toState_op]
    erw [sum_apply]
    rw [← Equiv.sum_comp finFunctionFinEquiv.symm
        (fun J : Fin n → Fin e.card => (∏ i, (e.prob (J i) : ℂ)) •
          (⨂ₜ[ℂ] i, (e.states (J i)).toState.op (x i)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [smul_apply, Ensemble.iidPow_states, Ensemble.iidPow_prob]
    rw [Complex.ofReal_prod]
    congr 1
    exact PureState.piTensor_toState_op_tprod (fun i => e.states (finFunctionFinEquiv.symm j i)) x
  exact ContinuousLinearMap.ext_tprod key

end AxQM
