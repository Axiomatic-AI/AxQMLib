/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSPhaseBasis
import ToMathlib.Analysis.InnerProductSpace.MaxEntVecBasis

/-!
# The `n` EPR pairs expressed in the CSS state basis (Nielsen & Chuang, Exercise 12.36)

Nielsen & Chuang, Exercise 12.36 (p. 598), asks to **verify Equation (12.203)**,

  `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩|j⟩ = ∑_{v_k,z,x} |ξ_{v_k,z,x}⟩|ξ_{v_k,z,x}⟩`,     (12.203)

which rewrites the (unnormalised) maximally entangled state of `n` EPR pairs — separated into the
`n` qubits Alice keeps and the `n` qubits sent to Bob — in the CSS phase-coset basis of (12.202).

## The two equalities of (12.203)

Both equalities are equalities of the single vector `nEPRVec ι` in
`(bitReg ι).space ⊗ (bitReg ι).space`, the *(unnormalised)* maximally entangled vector
`∑ⱼ |j⟩ ⊗ |j⟩` of the two `n`-qubit halves — the
same object that N&C's Ex 12.34 identifies with the `n`-EPR-pair state `|β₀₀⟩⊗ⁿ` (unnormalised, the
convention of the whole `maxEntVec` framework; the normalised state is `2^{-n/2}` times this, and
N&C write (12.203) in the unnormalised form of its middle/right sums).

* **First equality `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩|j⟩`** (`nEPRVec_eq_sum_regBasis_tmul`). This is definitional:
  `nEPRVec ι = (regBasis ι).maxEntVec = ∑_w |w⟩ ⊗ |w⟩` over the computational basis `{|w⟩}` of the
  register (`regBasis`), by unfolding `OrthonormalBasis.maxEntVec`.
* **Second equality `∑ⱼ |j⟩|j⟩ = ∑_{v_k,z,x} |ξ⟩|ξ⟩`** (`cssPhaseBasis_maxEntVec_eq_regBasis`, and
  in explicit-sum form `nEPRVec_eq_sum_cssPhaseFamily_tmul`) — the substance. It is exactly the
  basis-independence of the maximally entangled vector under a **real** orthonormal change of basis
  (`OrthonormalBasis.maxEntVec_eq_of_forall_conjVec_eq`, the reusable core of Ex 12.36),
  instantiated with `b` the computational basis and `b'` the CSS phase-coset basis `cssPhaseBasis`
  (Ex 12.35).

## Why the realness hypothesis holds (and is necessary)

The maximally entangled vector `∑ᵢ bᵢ ⊗ bᵢ` — with the *same* space in both tensor factors and no
conjugation — is **not** invariant under an arbitrary orthonormal change of basis: under a unitary
transition `U` it transforms by `U ⊗ U`, invariant iff `U Uᵀ = 1`, i.e. iff the new basis is *real*
(the vector face of the transpose trick `(A ⊗ I)|α⟩ = (I ⊗ Aᵀ)|α⟩`). This is what N&C's "and thus we
may write" tacitly relies on. The CSS phase-coset states of (12.202),
`|ξ_{z,a}⟩ = |C₂|^{-1/2} ∑_{w ∈ C₂} (-1)^{z·w} |a + w⟩`, have coefficients `± |C₂|^{-1/2}`, all
**real**, hence are fixed by the computational-basis conjugation (`cssPhaseState_conjVec_regBasis`),
so the realness hypothesis is satisfied — faithfully, not by weakening the claim.

The statement of Exercise 12.36 is in `AxQM/NC/Ch12/Exercise12_36.lean`; compare Exercise 12.34,
which treats the same `maxEntVec` construction.
-/

open scoped Matrix InnerProductSpace TensorProduct

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- **The CSS phase-coset states are real relative to the computational basis.** Each state
`|ξ_{z,a}⟩` of (12.202) has real computational-basis coordinates (its coefficients are
`± |C₂|^{-1/2}`), so it is fixed by the conjugation `regBasis.conjVec` in the computational basis:
`regBasis.conjVec |ξ_{z,a}⟩ = |ξ_{z,a}⟩`. This is precisely the realness hypothesis that makes the
maximally entangled vector basis-independent under the CSS change of basis (see
`cssPhaseBasis_maxEntVec_eq_regBasis`). Proved via the criterion
`OrthonormalBasis.conjVec_eq_self_of_forall_inner_comm`: each coordinate
`⟨w | ξ_{z,a}⟩ = |C₂|^{-1/2} ∑_{a + w' = w, w' ∈ C₂} (-1)^{z·w'}` is a sum of reals, hence
self-conjugate. -/
theorem cssPhaseState_conjVec_regBasis (z a : ι → ZMod 2) :
    (regBasis ι).conjVec (cssPhaseState C₂ z a).vec = (cssPhaseState C₂ z a).vec := by
  refine (regBasis ι).conjVec_eq_self_of_forall_inner_comm _ (fun w => ?_)
  rw [cssPhaseState_vec]
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum,
    orthonormal_iff_ite.mp (regBasis ι).orthonormal, map_inv₀, Complex.conj_ofReal,
    map_pow, map_neg, map_one, mul_ite, mul_one, mul_zero, eq_comm]

/-- The **(unnormalised) maximally entangled vector of the `n` EPR pairs** `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩ ⊗ |j⟩`,
an element of `(bitReg ι).space ⊗ (bitReg ι).space` — the first factor holds the `n` qubits Alice
keeps, the second the `n` qubits sent to Bob (Nielsen & Chuang eq. (12.203), left/middle). It is the
maximally entangled vector `OrthonormalBasis.maxEntVec` of the computational basis `regBasis`; the
normalised `n`-EPR state is `2^{-n/2}` times this. -/
noncomputable def nEPRVec (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (bitReg ι).space ⊗[ℂ] (bitReg ι).space :=
  (regBasis ι).maxEntVec

/-- **First equality of Eq. (12.203):** `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩ ⊗ |j⟩`. The `n`-EPR maximally entangled
vector is the sum over the computational basis `{|w⟩}` of `|w⟩ ⊗ |w⟩`, by definition of
`OrthonormalBasis.maxEntVec`. -/
theorem nEPRVec_eq_sum_regBasis_tmul :
    nEPRVec ι = ∑ w : ι → ZMod 2, regBasis ι w ⊗ₜ[ℂ] regBasis ι w := by
  rw [nEPRVec, OrthonormalBasis.maxEntVec]

/-- **Second equality of Eq. (12.203), operator form:** `∑ⱼ |j⟩⊗|j⟩ = ∑_{v_k,z,x} |ξ⟩⊗|ξ⟩`, i.e. the
maximally entangled vector is the *same* whether expanded in the computational basis `regBasis` or
in the CSS phase-coset basis `cssPhaseBasis`: `cssPhaseBasis.maxEntVec = regBasis.maxEntVec`. This
is the literal content of Ex 12.36, obtained by instantiating the basis-independence core
`OrthonormalBasis.maxEntVec_eq_of_forall_conjVec_eq` with the computational and CSS bases; the
realness hypothesis it requires is `cssPhaseState_conjVec_regBasis`. -/
theorem cssPhaseBasis_maxEntVec_eq_regBasis :
    (cssPhaseBasis C₂).maxEntVec = (regBasis ι).maxEntVec :=
  OrthonormalBasis.maxEntVec_eq_of_forall_conjVec_eq (regBasis ι) (cssPhaseBasis C₂) fun p => by
    rw [cssPhaseBasis_apply, cssPhaseFamily]
    exact cssPhaseState_conjVec_regBasis C₂ _ _

/-- **Equation (12.203) in full:** the `n`-EPR maximally entangled vector expanded in the CSS
phase-coset basis, `|β₀₀⟩⊗ⁿ = ∑_{v_k,z,x} |ξ_{v_k,z,x}⟩ ⊗ |ξ_{v_k,z,x}⟩`. Combining the first
equality
(`nEPRVec_eq_sum_regBasis_tmul`) with the basis change (`cssPhaseBasis_maxEntVec_eq_regBasis`), the
right-hand sum ranges over the CSS coset index and the summand is the tensor square of the CSS
phase-coset state `cssPhaseFamily p = |ξ_p⟩`. -/
theorem nEPRVec_eq_sum_cssPhaseFamily_tmul :
    nEPRVec ι = ∑ p : cssPhaseIndex C₂, cssPhaseFamily C₂ p ⊗ₜ[ℂ] cssPhaseFamily C₂ p := by
  rw [nEPRVec, ← cssPhaseBasis_maxEntVec_eq_regBasis C₂, OrthonormalBasis.maxEntVec]
  simp only [cssPhaseBasis_apply]

end AxQM
