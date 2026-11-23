/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.PiTensor
import AxQM.Postulates.PiTensorState

/-!
# AxQM.Postulates.API — permuting the wires of an `n`-fold register

An arbitrary permutation of the wires of an `n`-qubit (more generally `n`-copy) register
`S ^⊗ₛ n`, realised as a genuine closed-system `Evolution`. This is the general-`n` **SWAP
network**: the two-factor `Evolution.swap` is the `n = 2` transposition, and here every wire
permutation `σ : Equiv.Perm (Fin n)` becomes a unitary `Evolution.permWires σ` on the register.

## What is formalised

* `Evolution.permWires σ` — the **wire-permutation gate** on `S ^⊗ₛ n`: the closed-system
  `Evolution` that relabels the tensor factors by `σ`. It is `Evolution.ofLinearIsometryEquiv` of
  the factor-reindexing isometry `PiTensorProduct.reindexₗᵢ` along `σ`, so it is an `Evolution`
  (Postulate 5) with unitarity inherited from that isometry — the same construction as
  `Evolution.swap`.
* `Evolution.ext_tensorPow` — the reusable extensionality principle for evolutions of a tensor
  power: two `Evolution (S ^⊗ₛ n)` are equal once their operators agree on every product state
  `⨂ₜ i, f i` (product states span the register).
* `Evolution.permWires_op_tprod` — the **action on a product state**:
  `permWires σ (⨂ᵢ |fᵢ⟩) = ⨂ᵢ |f_{σ⁻¹ i}⟩`, i.e. the factor sitting on wire `j` is moved to wire
  `σ j`. This is the computational content — it lets any wire permutation's effect on a
  computational-basis product input be read off directly.
* `Evolution.permWires_evolvePure_piTensor` — the **pure-state counterpart** of the above:
  `permWires σ (⨂ₚ i, ψ i) = ⨂ₚ i, ψ (σ⁻¹ i)`, the `evolvePure` action on a product `PureState`,
  the form a consumer evolving computational-basis states works with.
* `Evolution.permWires_one`, `Evolution.permWires_mul`, `Evolution.permWires_symm_comp`,
  `Evolution.permWires_comp_symm` — the **group functoriality**: the identity permutation is the
  identity gate, `permWires (σ * τ) = permWires σ · permWires τ` (a homomorphism from the symmetric
  group to the gate composition monoid), and `permWires σ⁻¹` is the two-sided inverse of
  `permWires σ`. These are exactly what makes `permWires` a *SWAP network*: any permutation
  factors into transpositions, so any wire routing is built by composing swaps.

## Design notes

* **Why a general `Equiv.Perm (Fin n)` gate.** Placing a `Toffoli`/`CNOT` on *non-contiguous*
  wires of an `(n+1)`-wire register — as Nielsen & Chuang Exercise 4.29 needs in order to
  reduce the multiply-controlled-`NOT` blocks of the tight `Cⁿ(X)` circuit to genuine two-control
  gates with no work qubit — is done by conjugating a contiguous gate by the wire permutation that
  brings the chosen wires together. This needs an arbitrary wire permutation as a unitary
  `Evolution`, which this file supplies in full generality (compare the fixed-3-wire `Gate3` and
  the two-factor `Evolution.swap`). It applies well beyond Exercise 4.29 (SWAP/sorting networks,
  symmetric-group actions on registers).
* **Why the `PiTensorProduct.reindexₗᵢ` route.** The register `S ^⊗ₛ n` is the *symmetric* n-ary
  `PiTensorProduct` (`AxQM/Postulates/PiTensor.lean`), on which relabelling
  the factors along `σ : Fin n ≃ Fin n` is exactly `PiTensorProduct.reindexₗᵢ`. Because `σ`
  permutes a **constant** family (`fun _ : Fin n ↦ S.space`), the reindexed family
  `fun i ↦ (fun _ ↦ S.space) (σ.symm i)` is definitionally the same family, so `reindexₗᵢ … σ` is
  a genuine self-isometry-equivalence of `(S ^⊗ₛ n).space` — no associator/reindex bookkeeping,
  unlike a right-nested binary tower. Its action on pure tensors is
  `PiTensorProduct.reindexₗᵢ_tprod`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {n : ℕ}

/-! ### The wire-permutation gate -/

/-- **The wire-permutation gate** on the `n`-fold register `S ^⊗ₛ n`: given a permutation
`σ : Equiv.Perm (Fin n)` of the wires, the closed-system `Evolution` that relabels the tensor
factors by `σ`. It is `Evolution.ofLinearIsometryEquiv` of the factor-reindexing isometry
`PiTensorProduct.reindexₗᵢ` along `σ`, so it is an `Evolution` with
unitarity inherited from that isometry (the general-`n` form of `Evolution.swap`). Its action on a
product state is `Evolution.permWires_op_tprod`. -/
def Evolution.permWires (σ : Equiv.Perm (Fin n)) : Evolution (S ^⊗ₛ n) :=
  Evolution.ofLinearIsometryEquiv (PiTensorProduct.reindexₗᵢ ℂ (fun _ : Fin n => S.space) σ)

/-- **Extensionality for evolutions of a tensor power:** two evolutions of `S ^⊗ₛ n` are equal once
their operators agree on every product state `⨂ₜ i, f i`. Product states span the register
(`PiTensorProduct.extₛₗ`), so agreement there is full agreement. The workhorse for proving
identities between `Evolution.permWires` gates. -/
theorem Evolution.ext_tensorPow {A B : Evolution (S ^⊗ₛ n)}
    (h : ∀ f : Fin n → S.space, A.op (⨂ₜ[ℂ] i, f i) = B.op (⨂ₜ[ℂ] i, f i)) : A = B := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  exact PiTensorProduct.ext (MultilinearMap.ext h)

/-- The underlying operator of the wire-permutation gate is the factor-reindexing isometry
`PiTensorProduct.reindexₗᵢ` along `σ`. The bridge from the `Evolution` gate to the
`PiTensorProduct.reindexₗᵢ` algebra. -/
theorem Evolution.permWires_op_apply (σ : Equiv.Perm (Fin n)) (x : (S ^⊗ₛ n).space) :
    (Evolution.permWires σ).op x
      = PiTensorProduct.reindexₗᵢ ℂ (fun _ : Fin n => S.space) σ x :=
  Evolution.ofLinearIsometryEquiv_op_apply _ x

/-- **Action of the wire-permutation gate on a product state:**
`permWires σ (⨂ᵢ |fᵢ⟩) = ⨂ᵢ |f_{σ⁻¹ i}⟩` — the factor on wire `j` is moved to wire `σ j`. The
computational content of the gate (from `PiTensorProduct.reindexₗᵢ_tprod`): the effect of any wire
permutation on a computational-basis product input is read off directly.

(Not tagged `@[simp]`: on the tensor power `S ^⊗ₛ n` the unfolding simp lemma
`QSystem.tensorPow_space` rewrites inside this lemma's left-hand side, so it is not in
simp-normal form; use it as an explicit rewrite.) -/
theorem Evolution.permWires_op_tprod (σ : Equiv.Perm (Fin n)) (f : Fin n → S.space) :
    (Evolution.permWires σ).op (⨂ₜ[ℂ] i, f i) = ⨂ₜ[ℂ] i, f (σ.symm i) := by
  erw [Evolution.permWires_op_apply, PiTensorProduct.reindexₗᵢ_tprod]

/-- **Action of the wire-permutation gate on a product pure state:**
`permWires σ (⨂ₚ i, ψ i) = ⨂ₚ i, ψ (σ⁻¹ i)` — the factor on wire `j` is moved to wire `σ j`. The
`PureState`/`evolvePure` counterpart of the operator-level `Evolution.permWires_op_tprod`, obtained
by pushing both sides to their underlying vectors (`PureState.piTensor_vec`). It lets any wire
permutation's effect on a computational-basis product input be read off at the state level. -/
theorem Evolution.permWires_evolvePure_piTensor (σ : Equiv.Perm (Fin n))
    (ψ : Fin n → PureState S) :
    (Evolution.permWires σ).evolvePure (PureState.piTensor fun i => ψ i)
      = PureState.piTensor fun i => ψ (σ.symm i) := by
  apply PureState.ext
  erw [Evolution.evolvePure_vec, PureState.piTensor_vec, Evolution.permWires_op_tprod,
    PureState.piTensor_vec]

/-! ### Group functoriality (the SWAP-network laws) -/

/-- **The identity permutation is the identity gate:** `permWires 1 = 1`. -/
theorem Evolution.permWires_one :
    Evolution.permWires (1 : Equiv.Perm (Fin n)) = Evolution.id (S := S ^⊗ₛ n) := by
  apply Evolution.ext_tensorPow
  intro f
  rw [Evolution.permWires_op_tprod, Evolution.id_op]
  erw [one_apply_eq_self]
  rfl

/-- **`Evolution.permWires` is a homomorphism** from the symmetric group to the gate-composition
monoid: `permWires (σ * τ) = permWires σ · permWires τ`. Composing wire permutations is composing
the gates — the law that lets any wire routing be assembled from transpositions (a SWAP network). -/
theorem Evolution.permWires_mul (σ τ : Equiv.Perm (Fin n)) :
    Evolution.permWires (S := S) (σ * τ)
      = (Evolution.permWires σ).comp (Evolution.permWires τ) := by
  apply Evolution.ext_tensorPow
  intro f
  rw [Evolution.comp_op]
  erw [ContinuousLinearMap.comp_apply]
  rw [Evolution.permWires_op_tprod, Evolution.permWires_op_tprod, Evolution.permWires_op_tprod]
  rfl

/-- **`permWires σ⁻¹` is a right inverse of `permWires σ`:** `permWires σ · permWires σ⁻¹ = 1`.
Undoing a wire permutation is applying the inverse permutation. -/
theorem Evolution.permWires_symm_comp (σ : Equiv.Perm (Fin n)) :
    (Evolution.permWires (S := S) σ).comp (Evolution.permWires σ⁻¹) = Evolution.id := by
  rw [← Evolution.permWires_mul, mul_inv_cancel, Evolution.permWires_one]

/-- **`permWires σ⁻¹` is a left inverse of `permWires σ`:** `permWires σ⁻¹ · permWires σ = 1`. -/
theorem Evolution.permWires_comp_symm (σ : Equiv.Perm (Fin n)) :
    (Evolution.permWires (S := S) σ⁻¹).comp (Evolution.permWires σ) = Evolution.id := by
  rw [← Evolution.permWires_mul, inv_mul_cancel, Evolution.permWires_one]

end AxQM
