/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import ToMathlib.Analysis.InnerProductSpace.TensorProduct
import ToMathlib.Analysis.InnerProductSpace.OperatorSumChoiKraus

/-!
# Concrete: amplitude damping of a dual-rail qubit (N&C, Exercise 8.23)

This file computes the action of the tensor-product amplitude-damping channel `E_AD ⊗ E_AD` on the
**dual-rail** encoding of a qubit (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 8.23, p. 381). Everything is stated for bare `LinearMap`s on `H ⊗ H`, an
`OrthonormalBasis` and `TensorProduct.map`. It depends on `Concrete/AmplitudeDampingChannel.lean`
and belongs with the rest of the amplitude-damping exercises (8.20–8.22). The statement of
Exercise 8.23 is in `AxQM/NC/Ch8/Exercise8_23.lean`.

## The exercise

A single logical qubit is represented with **two** physical qubits by the dual-rail encoding
`|ψ⟩ = a|01⟩ + b|10⟩` (eq. 8.113): a single excitation shared between two optical modes ("rails").
Each rail independently undergoes amplitude damping, so the joint channel is `E_AD ⊗ E_AD`, whose
operation elements are the four tensor products `Eᵢ ⊗ Eⱼ` (`i, j ∈ {0,1}`) of the single-qubit
operation elements `E₀ = diag(1, √(1-γ))`, `E₁ = √γ|0⟩⟨1|` (eq. 8.108). N&C ask to show the process
on `|ψ⟩` is an **error-detection code**: either *nothing* happens, or the state is sent to `|00⟩`,
which is orthogonal to every codeword.

## What this file proves (the branch computation)

Applying each of the four operation elements to the codeword `|ψ⟩ = a|01⟩ + b|10⟩` gives (this
file):

* `E₀ ⊗ E₀ : |ψ⟩ ↦ √(1-γ) |ψ⟩` — **no** photon lost from either rail; the codeword survives
  (shrunk by `√(1-γ)`). This is the "nothing happens" branch, so `E₀ ⊗ E₀` acts on the codespace
  as the scalar `√(1-γ)`, i.e. as N&C's dual-rail operation element `E₀ᵈʳ = √(1-γ) I`.
* `E₀ ⊗ E₁ : |ψ⟩ ↦ √γ·a |00⟩` — the excitation in the **second** rail is lost.
* `E₁ ⊗ E₀ : |ψ⟩ ↦ √γ·b |00⟩` — the excitation in the **first** rail is lost.
* `E₁ ⊗ E₁ : |ψ⟩ ↦ 0` — both rails cannot lose a photon at once (there is only one).

All three loss branches land in the single direction `|00⟩`, and `⟨00|ψ⟩ = 0`
(`dualRailVec_inner_ketZeroZero`): the error state is orthogonal to every dual-rail codeword, so
measuring "are there zero photons?" is a nondestructive error-detection test — the basis of the
robustness of the dual-rail qubit (N&C §7.4).

## A subtlety about the single error element `E₁ᵈʳ` (honesty note)

N&C summarise the three loss branches by a *single* dual-rail error element
`E₁ᵈʳ = √γ (|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115). This coherently sums the two distinguishable loss
branches `E₀ ⊗ E₁` (→ `√γ·a|00⟩`) and `E₁ ⊗ E₀` (→ `√γ·b|00⟩`) — whose *environments* end in the
orthogonal states `|0⟩⊗|1⟩` and `|1⟩⊗|0⟩`, so under `E_AD ⊗ E_AD` they contribute **incoherently**
(weight `γ(|a|² + |b|²) = γ`), whereas `E₁ᵈʳ` alone produces `√γ(a+b)|00⟩` (weight `γ|a+b|²`). The
faithful reduced error description therefore needs the *pair* `√γ|00⟩⟨01|`, `√γ|00⟩⟨10|` (the
restrictions of `E₀ ⊗ E₁`, `E₁ ⊗ E₀`), not the single `E₁ᵈʳ`. This branch computation is the
common ground both readings share.

Building on it, this file also develops the **density-operator process**
`dualRailADChannel_apply_dualRail` (`E_AD ⊗ E_AD(|ψ⟩⟨ψ|) = (1-γ)|ψ⟩⟨ψ| + γ|00⟩⟨00|` for a
normalised codeword), the **faithful reduced operation elements** `dualRailErrZeroOne`,
`dualRailErrOneZero` with their codespace completeness `dualRailFaithful_completeness`, and the
**formal refutation** `dualRailErrCombined_not_completeness` of N&C's single `E₁ᵈʳ`: with the
coherent single element the completeness sum `Σ (Eᵏ)† Eᵏ` fails to fix the codespace (an
off-diagonal `γ` leak), so `{E₀ᵈʳ, E₁ᵈʳ}` is not a trace-preserving operator sum. The qualitative
error-detection content is correct and is what is formalised; the single-`E₁ᵈʳ` normalisation is
corrected openly.

## Design

The two-qubit space is the tensor product `H ⊗[ℂ] H` of an *arbitrary* abstract qubit `H`
(a two-dimensional complex inner product space with computational basis `b`), which carries the
inner-product-space structure `TensorProduct.instInnerProductSpace`; the basis vectors are the pure
tensors `b i ⊗ₜ b j = |ij⟩`. The tensor operation elements are `TensorProduct.map` of the reusable
single-qubit `ampDampKrausZero`/`ampDampKrausOne` of `Concrete/AmplitudeDampingChannel.lean`; the
branch computations reduce by `TensorProduct.map_tmul` and the shared single-qubit apply-on-basis
lemmas `ampDampKraus*_apply_basis*` of that base module.
-/

open scoped InnerProductSpace TensorProduct

open InnerProductSpace (rankOne)

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **dual-rail codeword** `|ψ⟩ = a|01⟩ + b|10⟩` (N&C eq. 8.113): a single excitation shared
between the two rails of the two-qubit space `H ⊗ H`, with amplitudes `a` for `|01⟩ = |0⟩⊗|1⟩` and
`c` for `|10⟩ = |1⟩⊗|0⟩`. -/
noncomputable def dualRailVec (a c : ℂ) : TensorProduct ℂ H H :=
  a • (b 0 ⊗ₜ[ℂ] b 1) + c • (b 1 ⊗ₜ[ℂ] b 0)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **No-loss branch** `E₀ ⊗ E₀ : |ψ⟩ ↦ √(1-γ) |ψ⟩`. No photon is lost from either rail, so the
codeword survives, shrunk by `√(1-γ)`; on the dual-rail codespace `E₀ ⊗ E₀` is thus the scalar
`√(1-γ)`, i.e. N&C's dual-rail element `E₀ᵈʳ = √(1-γ) I` (eq. 8.114). -/
theorem dualRailVec_ampDampMap_zero_zero (γ : ℝ) (a c : ℂ) :
    (TensorProduct.map (ampDampKrausZero b γ) (ampDampKrausZero b γ)) (dualRailVec b a c)
      = (Real.sqrt (1 - γ) : ℂ) • dualRailVec b a c := by
  simp only [dualRailVec, map_add, map_smul, TensorProduct.map_tmul,
    ampDampKrausZero_apply_basisZero, ampDampKrausZero_apply_basisOne,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul, smul_add, mul_comm]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **Second-rail loss branch** `E₀ ⊗ E₁ : |ψ⟩ ↦ √γ·a |00⟩`. The excitation in the second rail
(the `|01⟩` component) decays to the vacuum `|00⟩`; the `|10⟩` component is annihilated. -/
theorem dualRailVec_ampDampMap_zero_one (γ : ℝ) (a c : ℂ) :
    (TensorProduct.map (ampDampKrausZero b γ) (ampDampKrausOne b γ)) (dualRailVec b a c)
      = (Real.sqrt γ : ℂ) • a • (b 0 ⊗ₜ[ℂ] b 0) := by
  simp only [dualRailVec, map_add, map_smul, TensorProduct.map_tmul,
    ampDampKrausZero_apply_basisZero, ampDampKrausZero_apply_basisOne,
    ampDampKrausOne_apply_basisZero, ampDampKrausOne_apply_basisOne,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.tmul_zero,
    add_zero, smul_smul, mul_comm]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **First-rail loss branch** `E₁ ⊗ E₀ : |ψ⟩ ↦ √γ·c |00⟩`. The excitation in the first rail
(the `|10⟩` component) decays to the vacuum `|00⟩`; the `|01⟩` component is annihilated. -/
theorem dualRailVec_ampDampMap_one_zero (γ : ℝ) (a c : ℂ) :
    (TensorProduct.map (ampDampKrausOne b γ) (ampDampKrausZero b γ)) (dualRailVec b a c)
      = (Real.sqrt γ : ℂ) • c • (b 0 ⊗ₜ[ℂ] b 0) := by
  simp only [dualRailVec, map_add, map_smul, TensorProduct.map_tmul,
    ampDampKrausZero_apply_basisZero, ampDampKrausZero_apply_basisOne,
    ampDampKrausOne_apply_basisZero, ampDampKrausOne_apply_basisOne,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_zero, TensorProduct.zero_tmul,
    zero_add, smul_smul, mul_comm]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **Double-loss branch** `E₁ ⊗ E₁ : |ψ⟩ ↦ 0`. Both rails cannot lose a photon at once — there is
only one excitation in the codeword — so this branch annihilates every dual-rail state. -/
theorem dualRailVec_ampDampMap_one_one (γ : ℝ) (a c : ℂ) :
    (TensorProduct.map (ampDampKrausOne b γ) (ampDampKrausOne b γ)) (dualRailVec b a c) = 0 := by
  simp only [dualRailVec, map_add, map_smul, TensorProduct.map_tmul,
    ampDampKrausOne_apply_basisZero, ampDampKrausOne_apply_basisOne,
    TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero, add_zero]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **Error orthogonality**: the loss/error state `|00⟩` is orthogonal to every dual-rail codeword
`|ψ⟩ = a|01⟩ + b|10⟩`, i.e. `⟨00|ψ⟩ = 0`. Hence detecting the vacuum `|00⟩` (a "are there zero
photons?" measurement) flags an error without disturbing the surviving codewords — the dual-rail
error-detection principle (N&C §7.4, Exercise 8.23). -/
theorem dualRailVec_inner_ketZeroZero (a c : ℂ) :
    inner ℂ (b 0 ⊗ₜ[ℂ] b 0) (dualRailVec b a c) = 0 := by
  simp only [dualRailVec, TensorProduct.smul_tmul', inner_add_right, TensorProduct.inner_tmul,
    inner_smul_right, b.inner_eq_ite, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, mul_one,
    zero_add]

/-! ## The density-operator error-detection process

`E_AD ⊗ E_AD` acts on density operators as the operator sum `ρ ↦ Σᵢⱼ (Eᵢ ⊗ Eⱼ) ρ (Eᵢ ⊗ Eⱼ)†`. On
the codeword projector `|ψ⟩⟨ψ|` (normalised, `‖a‖² + ‖c‖² = 1`) it collapses to
`(1-γ)|ψ⟩⟨ψ| + γ|00⟩⟨00|`: *nothing happens* (weight `1-γ`), or the state is sent to the vacuum
`|00⟩` (weight `γ`). Each single-qubit operation element is a `LinearMap`; it bridges to a
`ContinuousLinearMap` (the two-qubit space is finite-dimensional) so the rank-one conjugation
machinery `comp_rankOne_self_comp_adjoint` (`M |ψ⟩⟨ψ| M† = |Mψ⟩⟨Mψ|`) applies, and the branch
vectors `Mψ` are read off from `dualRailVec_ampDampMap_*` above. -/

/-- A single tensor operation element `E ⊗ F` of `E_AD ⊗ E_AD`, as a continuous linear map on the
two-qubit space, built from single-qubit operation elements `E, F : H →ₗ[ℂ] H` (the two-qubit space
is finite-dimensional, so each `LinearMap` bridges to a `ContinuousLinearMap`). -/
noncomputable def dualRailConjKraus (E F : H →ₗ[ℂ] H) :
    (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  TensorProduct.mapL (LinearMap.toContinuousLinearMap E) (LinearMap.toContinuousLinearMap F)

omit [CompleteSpace H] in
/-- The tensor operation element `E ⊗ F` (as a `ContinuousLinearMap`) agrees with the plain
`TensorProduct.map E F` on vectors, bridging to the branch computations
`dualRailVec_ampDampMap_*`. -/
theorem dualRailConjKraus_apply (E F : H →ₗ[ℂ] H) (x : TensorProduct ℂ H H) :
    dualRailConjKraus E F x = TensorProduct.map E F x := by
  rw [dualRailConjKraus, TensorProduct.mapL_apply, LinearMap.coe_toContinuousLinearMap,
    LinearMap.coe_toContinuousLinearMap]

/-- The **dual-rail amplitude-damping process** `E_AD ⊗ E_AD` as an operator sum on density
operators: `ρ ↦ Σᵢⱼ (Eᵢ ⊗ Eⱼ) ρ (Eᵢ ⊗ Eⱼ)†` over the four tensor products of the single-qubit
operation elements `E₀, E₁` (N&C eqs. 8.107–8.108). -/
noncomputable def dualRailADChannel (γ : ℝ)
    (ρ : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H)) :
    (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausZero b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausZero b γ))))
    + (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausOne b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausZero b γ) (ampDampKrausOne b γ))))
    + (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausZero b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausZero b γ))))
    + (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausOne b γ)).comp
      (ρ.comp (ContinuousLinearMap.adjoint
        (dualRailConjKraus (ampDampKrausOne b γ) (ampDampKrausOne b γ))))

omit [CompleteSpace H] in
/-- **The dual-rail error-detection process (N&C Exercise 8.23).** For a normalised dual-rail
codeword `|ψ⟩ = a|01⟩ + c|10⟩` (`‖a‖² + ‖c‖² = 1`) and `0 ≤ γ ≤ 1`, the tensor amplitude-damping
channel acts on the projector `|ψ⟩⟨ψ|` as
`E_AD ⊗ E_AD(|ψ⟩⟨ψ|) = (1-γ) |ψ⟩⟨ψ| + γ |00⟩⟨00|` —
*either nothing happens* (weight `1-γ`, the no-loss branch `E₀ ⊗ E₀`), *or* the excitation is lost
and the state collapses to the vacuum `|00⟩` (weight `γ`, the two loss branches `E₀ ⊗ E₁`, `E₁ ⊗ E₀`
adding incoherently since `E₁ ⊗ E₁` annihilates the codeword). The vacuum `|00⟩` is orthogonal to
every codeword (`dualRailVec_inner_ketZeroZero`), so this is a nondestructive error-detection
process. -/
theorem dualRailADChannel_apply_dualRail (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (a c : ℂ)
    (hnorm : ‖a‖ ^ 2 + ‖c‖ ^ 2 = 1) :
    dualRailADChannel b γ (rankOne ℂ (dualRailVec b a c) (dualRailVec b a c))
      = ((1 - γ : ℝ) : ℂ) • rankOne ℂ (dualRailVec b a c) (dualRailVec b a c)
        + (γ : ℂ) • rankOne ℂ (b 0 ⊗ₜ[ℂ] b 0) (b 0 ⊗ₜ[ℂ] b 0) := by
  have h00 : rankOne ℂ ((Real.sqrt (1 - γ) : ℂ) • dualRailVec b a c)
        ((Real.sqrt (1 - γ) : ℂ) • dualRailVec b a c)
      = ((1 - γ : ℝ) : ℂ) • rankOne ℂ (dualRailVec b a c) (dualRailVec b a c) :=
    InnerProductSpace.rankOne_real_sqrt_smul_self (by linarith) (dualRailVec b a c)
  have hk00term : ∀ t : ℂ, rankOne ℂ ((Real.sqrt γ : ℂ) • t • (b 0 ⊗ₜ[ℂ] b 0))
        ((Real.sqrt γ : ℂ) • t • (b 0 ⊗ₜ[ℂ] b 0))
      = ((γ : ℂ) * (t * (starRingEnd ℂ) t)) • rankOne ℂ (b 0 ⊗ₜ[ℂ] b 0) (b 0 ⊗ₜ[ℂ] b 0) := by
    intro t
    rw [InnerProductSpace.rankOne_smul_smul_self, InnerProductSpace.rankOne_smul_smul_self,
      smul_smul]
    congr 1
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hγ0]
  have hac : (γ : ℂ) * (a * (starRingEnd ℂ) a) + (γ : ℂ) * (c * (starRingEnd ℂ) c) = (γ : ℂ) := by
    have hmc : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [RCLike.mul_conj]; norm_cast
    rw [← mul_add, hmc a, hmc c, ← Complex.ofReal_add, hnorm, Complex.ofReal_one, mul_one]
  rw [dualRailADChannel, ContinuousLinearMap.comp_rankOne_self_comp_adjoint,
    ContinuousLinearMap.comp_rankOne_self_comp_adjoint,
    ContinuousLinearMap.comp_rankOne_self_comp_adjoint,
    ContinuousLinearMap.comp_rankOne_self_comp_adjoint]
  simp only [dualRailConjKraus_apply, dualRailVec_ampDampMap_zero_zero,
    dualRailVec_ampDampMap_zero_one, dualRailVec_ampDampMap_one_zero,
    dualRailVec_ampDampMap_one_one, map_zero]
  rw [h00, hk00term a, hk00term c, add_zero, add_assoc, ← add_smul, hac]

/-! ## The faithful reduced dual-rail operation elements and their completeness

N&C summarise the process by the two dual-rail operation elements `E₀ᵈʳ = √(1-γ) I` (eq. 8.114) and
`E₁ᵈʳ = √γ(|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115). As the module docstring explains, the *single* `E₁ᵈʳ`
is not a faithful reduced element (it sums the two distinguishable loss branches coherently). The
faithful reduced description keeps the no-loss element `E₀ᵈʳ` together with the **pair** of loss
elements `√γ|00⟩⟨01|`, `√γ|00⟩⟨10|` — the restrictions of `E₀ ⊗ E₁`, `E₁ ⊗ E₀` to their action on
the codespace — for which completeness `Σ (Eᵏ)† Eᵏ = I` holds on the codespace. -/

/-- The **no-loss dual-rail operation element** `E₀ᵈʳ = √(1-γ) · I` (N&C eq. 8.114): on the
dual-rail codespace the no-loss branch `E₀ ⊗ E₀` acts as the scalar `√(1-γ)`
(`dualRailVec_ampDampMap_zero_zero`), i.e. as `√(1-γ)` times the identity on the two-qubit space
`H ⊗ H` (it is basis-independent, so takes no basis argument). -/
noncomputable def dualRailKrausZeroDR (γ : ℝ) :
    (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  (Real.sqrt (1 - γ) : ℂ) • ContinuousLinearMap.id ℂ (TensorProduct ℂ H H)

/-- The **first faithful reduced error element** `√γ |00⟩⟨01|` — the restriction of the second-rail
loss branch `E₀ ⊗ E₁` (`dualRailVec_ampDampMap_zero_one`) to its action, sending the codeword to
`√γ·a |00⟩`. -/
noncomputable def dualRailErrZeroOne (γ : ℝ) : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  rankOne ℂ ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0)) (b 0 ⊗ₜ[ℂ] b 1)

/-- The **second faithful reduced error element** `√γ |00⟩⟨10|` — the restriction of the first-rail
loss branch `E₁ ⊗ E₀` (`dualRailVec_ampDampMap_one_zero`), sending the codeword to `√γ·c |00⟩`. -/
noncomputable def dualRailErrOneZero (γ : ℝ) : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  rankOne ℂ ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0)) (b 1 ⊗ₜ[ℂ] b 0)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The reduced element `√γ|00⟩⟨01|` reproduces the loss branch `E₀ ⊗ E₁` on the codeword:
`(√γ|00⟩⟨01|)|ψ⟩ = √γ·a |00⟩` (cf. `dualRailVec_ampDampMap_zero_one`). -/
theorem dualRailErrZeroOne_apply_dualRailVec (γ : ℝ) (a c : ℂ) :
    dualRailErrZeroOne b γ (dualRailVec b a c) = a • ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0)) := by
  rw [dualRailErrZeroOne, InnerProductSpace.rankOne_apply, dualRailVec]
  simp only [inner_add_right, inner_smul_right, TensorProduct.inner_tmul, b.inner_eq_ite,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_one, mul_zero, add_zero]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The reduced element `√γ|00⟩⟨10|` reproduces the loss branch `E₁ ⊗ E₀` on the codeword:
`(√γ|00⟩⟨10|)|ψ⟩ = √γ·c |00⟩` (cf. `dualRailVec_ampDampMap_one_zero`). -/
theorem dualRailErrOneZero_apply_dualRailVec (γ : ℝ) (a c : ℂ) :
    dualRailErrOneZero b γ (dualRailVec b a c) = c • ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0)) := by
  rw [dualRailErrOneZero, InnerProductSpace.rankOne_apply, dualRailVec]
  simp only [inner_add_right, inner_smul_right, TensorProduct.inner_tmul, b.inner_eq_ite,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_one, mul_zero, zero_add]

omit [CompleteSpace H] in
/-- `(E₀ᵈʳ)† E₀ᵈʳ = (1-γ) I` (for `γ ≤ 1`): the no-loss element's contribution to the completeness
sum, `(√(1-γ))² = 1-γ` times the identity. -/
theorem dualRailKrausZeroDR_adjoint_comp_self (γ : ℝ) (hγ1 : γ ≤ 1) :
    (ContinuousLinearMap.adjoint (dualRailKrausZeroDR γ)).comp (dualRailKrausZeroDR γ)
      = ((1 - γ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (TensorProduct ℂ H H) := by
  rw [dualRailKrausZeroDR, map_smulₛₗ, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, smul_smul, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]

omit [CompleteSpace H] in
/-- `(√γ|00⟩⟨01|)† (√γ|00⟩⟨01|) = γ |01⟩⟨01|` (`0 ≤ γ`): the `|01⟩`-diagonal contribution of the
first reduced error element to the completeness sum. -/
theorem dualRailErrZeroOne_adjoint_comp_self (γ : ℝ) (hγ0 : 0 ≤ γ) :
    (ContinuousLinearMap.adjoint (dualRailErrZeroOne b γ)).comp (dualRailErrZeroOne b γ)
      = (γ : ℂ) • rankOne ℂ (b 0 ⊗ₜ[ℂ] b 1) (b 0 ⊗ₜ[ℂ] b 1) := by
  have hk : inner ℂ (b 0 ⊗ₜ[ℂ] b 0) (b 0 ⊗ₜ[ℂ] b 0) = (1 : ℂ) := by
    simp
  rw [dualRailErrZeroOne, InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_comp_rankOne,
    inner_smul_left, inner_smul_right, hk, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hγ0]

omit [CompleteSpace H] in
/-- `(√γ|00⟩⟨10|)† (√γ|00⟩⟨10|) = γ |10⟩⟨10|` (`0 ≤ γ`): the `|10⟩`-diagonal contribution of the
second reduced error element to the completeness sum. -/
theorem dualRailErrOneZero_adjoint_comp_self (γ : ℝ) (hγ0 : 0 ≤ γ) :
    (ContinuousLinearMap.adjoint (dualRailErrOneZero b γ)).comp (dualRailErrOneZero b γ)
      = (γ : ℂ) • rankOne ℂ (b 1 ⊗ₜ[ℂ] b 0) (b 1 ⊗ₜ[ℂ] b 0) := by
  have hk : inner ℂ (b 0 ⊗ₜ[ℂ] b 0) (b 0 ⊗ₜ[ℂ] b 0) = (1 : ℂ) := by
    simp
  rw [dualRailErrOneZero, InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_comp_rankOne,
    inner_smul_left, inner_smul_right, hk, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hγ0]

omit [CompleteSpace H] in
/-- **Faithful completeness on the codespace.** The reduced dual-rail operation elements
`{E₀ᵈʳ = √(1-γ) I, √γ|00⟩⟨01|, √γ|00⟩⟨10|}` satisfy `Σ (Eᵏ)† Eᵏ = I` on the code: applied to any
codeword `|ψ⟩ = a|01⟩ + c|10⟩` the completeness operator returns `|ψ⟩`. This is the trace
preservation of the reduced (three-element) error description — in contrast to N&C's single `E₁ᵈʳ`
(`dualRailErrCombined_not_completeness`). -/
theorem dualRailFaithful_completeness (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (a c : ℂ) :
    ((ContinuousLinearMap.adjoint (dualRailKrausZeroDR (H := H) γ)).comp (dualRailKrausZeroDR γ)
        + (ContinuousLinearMap.adjoint (dualRailErrZeroOne b γ)).comp (dualRailErrZeroOne b γ)
        + (ContinuousLinearMap.adjoint (dualRailErrOneZero b γ)).comp (dualRailErrOneZero b γ))
        (dualRailVec b a c)
      = dualRailVec b a c := by
  rw [dualRailKrausZeroDR_adjoint_comp_self γ hγ1, dualRailErrZeroOne_adjoint_comp_self b γ hγ0,
    dualRailErrOneZero_adjoint_comp_self b γ hγ0]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply, dualRailVec, inner_add_right,
    inner_smul_right, TensorProduct.inner_tmul, b.inner_eq_ite, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, mul_one, mul_zero, add_zero, zero_add, smul_add, smul_smul]
  push_cast
  module

/-! ## Refutation of N&C's single dual-rail error element `E₁ᵈʳ` -/

/-- N&C's **single dual-rail error element** `E₁ᵈʳ = √γ (|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115): the
*coherent* sum of the two reduced loss elements. -/
noncomputable def dualRailErrCombined (γ : ℝ) : (TensorProduct ℂ H H) →L[ℂ] (TensorProduct ℂ H H) :=
  dualRailErrZeroOne b γ + dualRailErrOneZero b γ

omit [CompleteSpace H] in
/-- **Completeness leak of the single `E₁ᵈʳ`.** With `E₁ᵈʳ` the single coherent element of
eq. 8.115, the completeness operator `(E₀ᵈʳ)†E₀ᵈʳ + (E₁ᵈʳ)†E₁ᵈʳ` applied to the basis codeword
`|01⟩` returns `|01⟩ + γ|10⟩` — an off-diagonal `γ` leak between the two single-excitation states,
instead of the `|01⟩` a completeness relation would give. -/
theorem dualRailErrCombined_completeness_fails (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ((ContinuousLinearMap.adjoint (dualRailKrausZeroDR (H := H) γ)).comp (dualRailKrausZeroDR γ)
        + (ContinuousLinearMap.adjoint (dualRailErrCombined b γ)).comp (dualRailErrCombined b γ))
        (b 0 ⊗ₜ[ℂ] b 1)
      = (b 0 ⊗ₜ[ℂ] b 1) + (γ : ℂ) • (b 1 ⊗ₜ[ℂ] b 0) := by
  have hk : inner ℂ (b 0 ⊗ₜ[ℂ] b 0) (b 0 ⊗ₜ[ℂ] b 0) = (1 : ℂ) := by
    simp
  have hk01 : inner ℂ (b 0 ⊗ₜ[ℂ] b 1) (b 0 ⊗ₜ[ℂ] b 1) = (1 : ℂ) := by
    simp
  have hk10_01 : inner ℂ (b 1 ⊗ₜ[ℂ] b 0) (b 0 ⊗ₜ[ℂ] b 1) = (0 : ℂ) := by
    simp
  have hinner : inner ℂ ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0))
      ((Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0)) = (γ : ℂ) := by
    rw [inner_smul_left, inner_smul_right, hk, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hγ0]
  have hcomb01 : dualRailErrCombined b γ (b 0 ⊗ₜ[ℂ] b 1)
      = (Real.sqrt γ : ℂ) • (b 0 ⊗ₜ[ℂ] b 0) := by
    rw [dualRailErrCombined, add_apply, dualRailErrZeroOne, dualRailErrOneZero,
      InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply, hk01, hk10_01, one_smul,
      zero_smul, add_zero]
  rw [dualRailKrausZeroDR_adjoint_comp_self γ hγ1, add_apply,
    ContinuousLinearMap.comp_apply, hcomb01, smul_apply,
    ContinuousLinearMap.id_apply, dualRailErrCombined, dualRailErrZeroOne, dualRailErrOneZero,
    map_add, add_apply, InnerProductSpace.adjoint_rankOne,
    InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_apply,
    InnerProductSpace.rankOne_apply, hinner]
  module

omit [CompleteSpace H] in
/-- **Refutation of N&C's literal single-`E₁ᵈʳ` reading.** For `0 < γ ≤ 1`, N&C's `{E₀ᵈʳ, E₁ᵈʳ}`
completeness operator does not fix the codeword `|01⟩` (`Σ (Eᵏ)† Eᵏ ≠ I`): the single coherent
`E₁ᵈʳ = √γ(|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115) is **not** a trace-preserving operation-element
decomposition of `E_AD ⊗ E_AD` on the dual-rail code. The two distinguishable loss branches must be
kept as the *pair* `dualRailErrZeroOne`, `dualRailErrOneZero`, for which completeness does hold
(`dualRailFaithful_completeness`). -/
theorem dualRailErrCombined_not_completeness (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ((ContinuousLinearMap.adjoint (dualRailKrausZeroDR (H := H) γ)).comp (dualRailKrausZeroDR γ)
        + (ContinuousLinearMap.adjoint (dualRailErrCombined b γ)).comp (dualRailErrCombined b γ))
        (b 0 ⊗ₜ[ℂ] b 1)
      ≠ (b 0 ⊗ₜ[ℂ] b 1) := by
  rw [dualRailErrCombined_completeness_fails b γ hγ0.le hγ1]
  intro h
  have hz : (γ : ℂ) • (b 1 ⊗ₜ[ℂ] b 0) = 0 :=
    add_left_cancel (a := b 0 ⊗ₜ[ℂ] b 1) (by rw [add_zero]; exact h)
  rw [smul_eq_zero] at hz
  rcases hz with hγ | hk
  · exact absurd (Complex.ofReal_eq_zero.mp hγ) (ne_of_gt hγ0)
  · have hone : inner ℂ (b 1 ⊗ₜ[ℂ] b 0) (b 1 ⊗ₜ[ℂ] b 0) = (1 : ℂ) := by
      simp
    rw [hk, inner_zero_right] at hone
    exact one_ne_zero hone.symm

end AxQM.Concrete

end
