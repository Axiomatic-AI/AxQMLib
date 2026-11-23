/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.PiTensorSuccHead
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.API.TensorPowState
import AxQM.Postulates.API.TensorPowDim
import AxQM.Postulates.API.Entropy

/-!
# AxQM — von Neumann entropy is additive across tensor factors

The von Neumann entropy adds over the factors of an (uncorrelated) product state. This file lifts
the binary additivity `State.vonNeumannEntropy_tmul` (N&C Exercise 11.13, `S(ρ ⊗ σ) = S(ρ) + S(σ)`)
to the `n`-ary indexed product `State.piTensor` and, as the constant-family special case, to the
`n`-fold tensor power `State.tensorPow`:

* `State.vonNeumannEntropy_piTensor`: `S(⨂ᵢ fᵢ) = ∑ᵢ S(fᵢ)`;
* `State.vonNeumannEntropy_tensorPow`: `S(ρ^⊗n) = n · S(ρ)`.

## Use in N&C Exercise 12.23

Copy-accounting for the **optimality of entanglement distillation** (N&C Exercise 12.23): distilling
Bell states out of `m` copies of `|ψ⟩` by LOCC can only reduce the entanglement entropy
(`State.LOCCConvertible.vonNeumannEntropy_le`), and the total entanglement entropy of the `m`
copies is `S(ρ_ψ^⊗m) = m · S(ρ_ψ)`. This exact linear scaling — supplied by
`State.vonNeumannEntropy_tensorPow` — is what turns the per-transformation monotone into the
asymptotic converse bound `rate ≤ S(ρ_ψ)` (the distillable entanglement cannot exceed `S(ρ_ψ)`).

## Proof

Induction on the number of tensor factors, mirroring `State.holevoChi_piTensor_le`.

* **Base (`n = 0`).** The empty product lives on the one-dimensional system `S ^⊗ₛ 0`, so its
  entropy is squeezed between `0` (`State.vonNeumannEntropy_nonneg`) and `log (dim) = log 1 = 0`
  (`State.vonNeumannEntropy_le_log_finrank` with `QSystem.finrank_tensorPow_space`), while the empty
  sum is `0`.
* **Step (`n+1`).** Peel the head factor with the `cons`-recursion isomorphism
  `State.tmul_piTensor_congr_tensorPowSuccHead_symm`, writing `⨂ᵢ fᵢ` as a system-isomorphic copy of
  `f 0 ⊗ (⨂ⱼ f j.succ)`. Entropy is transport-invariant (`State.vonNeumannEntropy_congr`), then the
  binary additivity (`State.vonNeumannEntropy_tmul`) and the induction hypothesis give
  `S(f 0) + ∑ⱼ S(f j.succ) = ∑ᵢ S(fᵢ)` (`Fin.sum_univ_succ`).

The `succ` step uses the head-peel recursion `State.tmul_piTensor_congr_tensorPowSuccHead_symm`
(`AxQM/Core/PiTensorSuccHead.lean`).
-/

noncomputable section

namespace AxQM

namespace State

variable {S : QSystem}

/-- **Additivity of the von Neumann entropy over an indexed product state.** For a finite family of
states `f : Fin n → State S`, the entropy of the product `⨂ᵢ fᵢ` is the sum of the entropies:

`S(⨂ᵢ fᵢ) = ∑ᵢ S(fᵢ)`.

The `n`-ary form of `State.vonNeumannEntropy_tmul`, proved by induction on the number of factors
using the head-peel recursion `State.tmul_piTensor_congr_tensorPowSuccHead_symm` (the empty product
sits on the one-dimensional system `S ^⊗ₛ 0`, so has zero entropy). -/
theorem vonNeumannEntropy_piTensor :
    ∀ {n : ℕ} (f : Fin n → State S),
      (State.piTensor f).vonNeumannEntropy = ∑ i, (f i).vonNeumannEntropy
  | 0, f => by
      -- `S ^⊗ₛ 0` is one-dimensional, so every state on it has zero entropy; the empty sum is `0`.
      have hz : ∀ σ : State (S ^⊗ₛ 0), σ.vonNeumannEntropy = 0 := fun σ => by
        have h := σ.vonNeumannEntropy_le_log_finrank
        rw [QSystem.finrank_tensorPow_space, pow_zero, Nat.cast_one, Real.log_one] at h
        exact le_antisymm h σ.vonNeumannEntropy_nonneg
      rw [Fin.sum_univ_zero]
      exact hz _
  | n + 1, f => by
      have ih := vonNeumannEntropy_piTensor (fun j : Fin n => f j.succ)
      -- Peel the head factor: `⨂ᵢ fᵢ ≃ₛ f 0 ⊗ (⨂ⱼ f j.succ)`, and entropy is transport-invariant.
      have hcongr : (State.piTensor f).vonNeumannEntropy
          = ((f 0).tmul (State.piTensor fun j : Fin n => f j.succ)).vonNeumannEntropy := by
        conv_lhs => rw [← State.tmul_piTensor_congr_tensorPowSuccHead_symm f]
        exact State.vonNeumannEntropy_congr _ _
      rw [hcongr, State.vonNeumannEntropy_tmul, ih, Fin.sum_univ_succ]

/-- **The von Neumann entropy is additive across copies.** For a state `ρ : State S` and `n : ℕ`,
the entropy of the `n`-fold tensor power scales linearly:

`S(ρ^⊗n) = n · S(ρ)`.

The constant-family special case of `State.vonNeumannEntropy_piTensor`, collapsing
`∑ _ : Fin n, S(ρ)` to `n · S(ρ)`. This is the copy-accounting behind the optimality of
entanglement distillation (N&C Exercise 12.23):
`m` copies of `|ψ⟩` carry total entanglement entropy `m · S(ρ_ψ)`. -/
theorem vonNeumannEntropy_tensorPow (ρ : State S) (n : ℕ) :
    (ρ.tensorPow n).vonNeumannEntropy = n * ρ.vonNeumannEntropy := by
  have h : (ρ.tensorPow n).vonNeumannEntropy = ∑ _i : Fin n, ρ.vonNeumannEntropy :=
    vonNeumannEntropy_piTensor (fun _ : Fin n => ρ)
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end State

end AxQM
