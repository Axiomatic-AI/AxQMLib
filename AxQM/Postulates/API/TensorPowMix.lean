/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TensorPowState
import AxQM.Postulates.API.Mixture

/-!
# AxQM.Postulates.API — the tensor power of a mixture as an i.i.d. mixture of products

The **random-coding average** step of the Holevo–Schumacher–Westmoreland theorem (Nielsen & Chuang,
Theorem 12.8, eq. (12.80)) rests on the identity `E(σ_M) = σ̄^⊗n`: the expected output codeword of a
length-`n` random product-state code, averaged over the i.i.d. random choice of its `n` letters,
equals the `n`-fold tensor power of the *average* output state `σ̄ = ∑ⱼ pⱼ σⱼ`.

This file records the underlying algebraic identity — that the `n`-fold tensor power of a mixture is
the mixture (over all length-`n` index sequences, weighted by the i.i.d. product distribution) of
the corresponding product states:

* **`State.tensorPow_mix`**: `(∑ⱼ pⱼ σⱼ)^⊗n = ∑_s (∏ᵢ p_{sᵢ}) · (⨂ᵢ σ_{sᵢ})`.

It is the **mixed-state** counterpart of `Ensemble.iidPow_toState`
(`(e.iidPow n).toState = e.toState.tensorPow n`), which is the same identity for an ensemble of
*pure* inputs. HSW needs the mixed version because the objects being averaged are the *channel
outputs* `σⱼ = E(ρⱼ)`, which are generally mixed even when the inputs `ρⱼ` are pure.

The two supporting facts about the i.i.d. product weight `p_s = ∏ᵢ p_{sᵢ}` (non-negativity and
summation to one) are recorded as `iidProdWeight_nonneg` / `sum_iidProdWeight`; they make
`fun s => ∏ᵢ p_{sᵢ}` a probability distribution over the `|ι|ⁿ` length-`n` index sequences, i.e. the
distribution of the random codeword.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, eq. (12.80).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

omit [Fintype ι] in
/-- The **i.i.d. product weight** `p_s = ∏ᵢ p_{sᵢ}` of a length-`n` index sequence `s : Fin n → ι`
is non-negative, being a product of the non-negative single-letter probabilities `pⱼ`. Together with
`sum_iidProdWeight` this makes `fun s => ∏ᵢ p_{sᵢ}` the probability distribution of the random
length-`n` codeword. -/
theorem iidProdWeight_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (n : ℕ) (s : Fin n → ι) :
    0 ≤ ∏ i, p (s i) :=
  Finset.prod_nonneg fun i _ => hp (s i)

/-- The **i.i.d. product weights sum to one**: `∑_{s : Fin n → ι} ∏ᵢ p_{sᵢ} = 1`, so the length-`n`
product weight is a genuine probability distribution over the index sequences. The multiplicativity
of a sum over a product index (`Finset.prod_univ_sum`) collapses it to `∏ᵢ (∑ⱼ pⱼ) = ∏ᵢ 1 = 1`. -/
theorem sum_iidProdWeight (p : ι → ℝ) (hsum : ∑ i, p i = 1) (n : ℕ) :
    ∑ s : Fin n → ι, ∏ i, p (s i) = 1 := by
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum,
    Finset.prod_congr rfl fun i _ => hsum, Finset.prod_const_one]

/-- **The tensor power of a mixture is the i.i.d. mixture of product states** (Nielsen & Chuang,
Theorem 12.8, the random-coding average `E(σ_M) = σ̄^⊗n` of eq. (12.80)). For a finite family of
states `σ : ι → State S` and a probability distribution `p` (`∑ⱼ pⱼ = 1`), the `n`-fold tensor power
of the mixture `σ̄ = ∑ⱼ pⱼ σⱼ` equals the mixture — over all length-`n` index sequences
`s : Fin n → ι`, weighted by the i.i.d. product weight `p_s = ∏ᵢ p_{sᵢ}` (`sum_iidProdWeight`) — of
the product states `σ_s = σ_{s₁} ⊗ ⋯ ⊗ σ_{sₙ}`:

`(∑ⱼ pⱼ σⱼ)^⊗n = ∑_s (∏ᵢ p_{sᵢ}) · (⨂ᵢ σ_{sᵢ})`.

This is the mixed-state generalisation of the pure-state `Ensemble.iidPow_toState`
(`(e.iidPow n).toState = e.toState.tensorPow n`): where that averages an ensemble of *pure* inputs,
this averages a distribution over arbitrary *mixed* states — exactly the channel outputs
`σⱼ = E(ρⱼ)` of the HSW random-coding argument, for which the expected output codeword of the random
i.i.d. code equals `σ̄^⊗n`.

Proof. Both density operators agree on every elementary tensor `⨂ᵢ xᵢ`. The left side
`σ̄^⊗n = ⨂ᵢ σ̄` distributes the sum `σ̄.op = ∑ⱼ pⱼ σⱼ.op` inside each of the `n` factors by
multilinearity of the `n`-ary tensor (`MultilinearMap.map_sum`, then `MultilinearMap.map_smul_univ`
to pull the products of weights out), giving `∑_s (∏ᵢ p_{sᵢ}) • ⨂ᵢ (σ_{sᵢ}.op xᵢ)`. The right side
is the mixture operator sum `∑_s p_s • (⨂ᵢ σ_{sᵢ}).op`, whose each summand acts on `⨂ᵢ xᵢ` as
`⨂ᵢ (σ_{sᵢ}.op xᵢ)` (`State.piTensor_op`, `PiTensorProduct.mapCLM_tprod`) — matching term by term
(`Complex.ofReal_prod` bridging `↑(∏ᵢ p_{sᵢ}) = ∏ᵢ ↑p_{sᵢ}`). -/
theorem State.tensorPow_mix (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (σ : ι → State S) (n : ℕ) :
    (State.mix p hp hsum σ).tensorPow n
      = State.mix (fun s : Fin n → ι => ∏ i, p (s i)) (iidProdWeight_nonneg p hp n)
          (sum_iidProdWeight p hsum n) (fun s => State.piTensor fun i => σ (s i)) := by
  apply State.ext
  rw [State.tensorPow_op]
  -- Both operators agree on every elementary tensor `⨂ᵢ xᵢ` (mirroring `Ensemble.iidPow_toState`):
  -- the mixture is expanded via `mix_op`/`sum_apply` only *after* it is applied to `⨂ᵢ xᵢ`, so the
  -- operator stays on the tensor-power system's space and `rw` matches syntactically.
  refine ContinuousLinearMap.ext_tprod fun x => ?_
  -- Left side: distribute `mapCLM (fun _ => σ̄.op)` over the per-factor sums `σ̄.op = ∑ⱼ pⱼ σⱼ.op`.
  have hL : (PiTensorProduct.mapCLM fun _ : Fin n => (State.mix p hp hsum σ).op) (⨂ₜ[ℂ] i, x i)
      = ∑ s : Fin n → ι, (∏ i, (p (s i) : ℂ)) • ⨂ₜ[ℂ] i, (σ (s i)).op (x i) := by
    rw [PiTensorProduct.mapCLM_tprod]
    simp_rw [State.mix_op, _root_.sum_apply, _root_.smul_apply]
    rw [MultilinearMap.map_sum]
    simp_rw [MultilinearMap.map_smul_univ, RingHom.id_apply]
  -- Right side: expand the mixture only once it is applied to `⨂ᵢ xᵢ`, then match term by term.
  -- `change` re-presents the applied sum on the *raw* space `⨂[ℂ] i, S.space` (defeq, since the
  -- factor map `(⨂ᵢ σ_{sᵢ}).op` is `mapCLM (fun i => σ_{sᵢ}.op)` by `State.piTensor_op = rfl`), so
  -- `ContinuousLinearMap.sum_apply` distributes past the re-bundled tensor-power-system instance.
  rw [hL, State.mix_op]
  change (∑ s : Fin n → ι, (∏ i, (↑(p (s i)) : ℂ)) •
        (PiTensorProduct.tprod ℂ) fun i => (σ (s i)).op (x i))
      = (∑ s : Fin n → ι, (↑(∏ i, p (s i)) : ℂ) • PiTensorProduct.mapCLM fun i => (σ (s i)).op)
          ((PiTensorProduct.tprod ℂ) fun i => x i)
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [_root_.smul_apply, PiTensorProduct.mapCLM_tprod, Complex.ofReal_prod]

end AxQM
