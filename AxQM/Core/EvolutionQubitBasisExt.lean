/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.WirePermutation
import AxQM.Postulates.API.Qubit
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Computational-basis extensionality for evolutions on a qubit register (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. `Cⁿ(X)` and every `Toffoli`/`CNOT`/`NOT` block
are **classical** gates — they permute the computational basis — so the natural way to prove two
such gates *equal* is to check they agree on every computational basis state and invoke *"agreement
on all basis states is full agreement"*. The results `cnx_evolvePure_towerKet`,
`tensorPowMcCtrlX_evolvePure_piTensor` and `placedMcCtrlX_evolvePure_qubitBasis` all state their
content as such a computational-basis **truth table**; turning a pair of matching truth tables into
an `Evolution` identity is the step this file makes into a lemma.

The library already has `Evolution.ext_tensorPow`: two evolutions of `S ^⊗ₛ n` are equal once their
operators agree on **every** elementary tensor `⨂ᵢ f i` (arbitrary vectors `f i : S.space`). Product
states span the register, so that is full agreement. This file specialises it to the qubit register,
replacing the *continuum* of elementary tensors `⨂ᵢ f i` by the *finite* family of computational
product states `⨂ᵢ |c i⟩` (`c : Fin m → Fin 2`): since the two computational basis vectors
`|0⟩, |1⟩` are a basis of `qubit.space`, the products `⨂ᵢ |c i⟩` are a basis of `qubit ^⊗ₛ m`
(`Basis.piTensorProduct`), so agreement there already forces operator equality.

## What is formalised

* `Evolution.ext_qubitBasis` — **two evolutions of `qubit ^⊗ₛ m` agreeing on every computational
  product state are equal.** It upgrades a computational-basis truth table (the form every
  classical-gate result is stated in) to an honest `Evolution` identity: to prove `A = B` for two
  classical gates it suffices to check `A |c⟩ = B |c⟩` for every bit-string `c : Fin m → Fin 2`.

## Design notes

* **Why the finite computational basis, not all product states.** `Evolution.ext_tensorPow` demands
  agreement on `⨂ᵢ f i` for *arbitrary* `f i : qubit.space` — but a classical gate's truth table is
  only ever known on the computational basis `|0⟩, |1⟩`. Because those two vectors are a `ℂ`-basis
  of the two-dimensional `qubit.space` (`finrank_qubit_space`, `qubitBasis_vec_orthonormal`), the
  computational products `⨂ᵢ |c i⟩` form the `Basis.piTensorProduct` basis of `qubit ^⊗ₛ m`, and a
  (continuous) linear map is determined by its values on a basis (`Basis.ext`). So the finite,
  checkable hypothesis is *equivalent* to the elementary-tensor one, not weaker.
* **The proof.** `Evolution.ext` reduces to `A.op = B.op`; `ContinuousLinearMap.coe_injective`
  reduces that to the underlying linear maps; `Basis.ext` against the qubit
  `Basis.piTensorProduct` reduces to agreement on each basis vector `⨂ᵢ |c i⟩`; and there the
  bridges `Evolution.evolvePure_vec` (`(A |ψ⟩).vec = A.op ψ.vec`) and `PureState.piTensor_vec`
  (`(⨂ᵢ ψ i).vec = ⨂ᵢ (ψ i).vec`) — both `@[simp]`/`rfl` — collapse the hypothesis `A |c⟩ = B |c⟩`
  onto the required operator equation by kernel-level defeq. The qubit `ℂ`-basis is the reusable
  `qubitModuleBasis` (`AxQM/Postulates/API/Qubit.lean`, alongside `quditOrthonormalBasis`).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Computational-basis extensionality for evolutions of a qubit register.** Two evolutions
`A B : Evolution (qubit ^⊗ₛ m)` are equal once they agree on every computational product basis state
`⨂ᵢ |c i⟩` (`c : Fin m → Fin 2`). This is the classical-gate analogue of `Evolution.ext_tensorPow`:
it replaces the continuum of elementary tensors `⨂ᵢ f i` by the finite, checkable family of
computational product states, because the two computational basis vectors `|0⟩, |1⟩` are a basis of
`qubit.space` and hence the products `⨂ᵢ |c i⟩` are a basis of the register
(`Basis.piTensorProduct`). It is the tool that turns a computational-basis truth table — the form in
which `Cⁿ(X)` and every `Toffoli`/`CNOT`/`NOT` block is specified — into an honest `Evolution`
identity ("agreement on all basis states is full agreement"). -/
theorem Evolution.ext_qubitBasis {m : ℕ} {A B : Evolution (qubit ^⊗ₛ m)}
    (h : ∀ c : Fin m → Fin 2,
      A.evolvePure (PureState.piTensor fun i => qubitBasis (c i))
        = B.evolvePure (PureState.piTensor fun i => qubitBasis (c i))) :
    A = B := by
  -- Reduce to equality of the underlying linear operators, then check on the computational product
  -- basis `⨂ᵢ |c i⟩`, the `Basis.piTensorProduct` of the qubit `ℂ`-basis `|0⟩, |1⟩`
  -- (`qubitModuleBasis`).
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  refine (Basis.piTensorProduct fun _ : Fin m => qubitModuleBasis).ext ?_
  intro c
  rw [Basis.piTensorProduct_apply]
  simp only [qubitModuleBasis_apply]
  -- The remaining operator goal is `congrArg vec (h c)` up to the `@[simp]`/`rfl` bridges
  -- `Evolution.evolvePure_vec` and `PureState.piTensor_vec` (kernel-level defeq).
  exact congrArg PureState.vec (h c)

end AxQM
