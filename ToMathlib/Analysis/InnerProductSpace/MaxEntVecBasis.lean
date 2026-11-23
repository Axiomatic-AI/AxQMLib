/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi

/-! # Basis independence of the maximally entangled vector under a real change of basis

For a finite-dimensional inner product space `E` over `𝕜`, the (unnormalised) **maximally entangled
vector** of an orthonormal basis `b` is `OrthonormalBasis.maxEntVec b = Σᵢ bᵢ ⊗ bᵢ ∈ E ⊗ E`.
Unlike the genuinely basis-independent "co-evaluation" element of `E ⊗ E*`, this vector — with the
*same* space in both tensor factors and no conjugation — is **not** invariant under an arbitrary
orthonormal change of basis: under a unitary transition `U` it transforms by `U ⊗ U`, and
`(U ⊗ U)(Σᵢ eᵢ ⊗ eᵢ) = Σᵢ eᵢ ⊗ eᵢ` holds iff `U Uᵀ = 1`, i.e. iff `U` is *real* orthogonal
(equivalently, the new basis vectors have real coordinates in the old one). This is the vector
counterpart of the transpose trick `(A ⊗ I)|α⟩ = (I ⊗ Aᵀ)|α⟩`
(`Matrix.kronecker_one_mulVec_maxEntVec`).

## Main results

* `OrthonormalBasis.maxEntVec_eq_of_forall_conjVec_eq` — if every vector of the orthonormal basis
  `b'` is **real relative to** `b` (fixed by the `b`-coordinate conjugation
  `OrthonormalBasis.conjVec`, `b.conjVec (b' k) = b' k`, i.e. its `b`-coordinates are all
  self-conjugate), then the two maximally entangled vectors coincide: `b'.maxEntVec = b.maxEntVec`,
  that is `Σₖ b'ₖ ⊗ b'ₖ = Σᵢ bᵢ ⊗ bᵢ`.
  The proof expands each `b' k` in the `b` basis on both tensor factors, contracts the resulting
  double coefficient sum with the completeness relation of `b'`
  (`OrthonormalBasis.sum_inner_mul_inner`) — using realness to turn one factor into its conjugate —
  and collapses the surviving `⟪bᵢ, bⱼ⟫ = δᵢⱼ`.

## Relation to Nielsen & Chuang, Exercise 12.36

N&C, *Quantum Computation and Quantum Information* (Exercise 12.36, p. 598), ask to verify
Equation (12.203),
`|β₀₀⟩⊗ⁿ = Σⱼ |j⟩|j⟩ = Σ_{vₖ,z,x} |ξ_{vₖ,z,x}⟩|ξ_{vₖ,z,x}⟩`,
which rewrites the (unnormalised) maximally entangled state of `n` EPR pairs in the CSS state basis.
The second equality is exactly `maxEntVec_eq_of_forall_conjVec_eq` applied with `b` the
computational basis and `b'` the CSS basis: the CSS states of Eq. (12.202),
`|ξ_{vₖ,z,x}⟩ = |C₂|^{-1/2} Σ_{w ∈ C₂} (-1)^{z·w} |vₖ + w + x⟩`,
have coefficients `± |C₂|^{-1/2}`, all **real**, so they satisfy the realness hypothesis; that they
form an orthonormal basis is the content of Exercise 12.35. This file supplies the reusable
linear-algebra core — the "and thus we may write" step of N&C's argument — in full generality; the
literal instantiation to the CSS orthonormal basis is completed once that basis object (Ex 12.35)
is in place. The realness hypothesis is genuinely necessary (see the module note above), and is what
N&C's phrasing tacitly relies on.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {ι : Type*} [Fintype ι]

/-- **Criterion for a vector to be real relative to an orthonormal basis.** If for every basis
index `i` the two inner products `⟪ψ, b i⟫` and `⟪b i, ψ⟫` agree — equivalently, every
`b`-coordinate `⟪b i, ψ⟫` of `ψ` is self-conjugate (real) — then `ψ` is fixed by the `b`-coordinate
conjugation, `b.conjVec ψ = ψ`. This is the workhorse for discharging the realness hypothesis of
`maxEntVec_eq_of_forall_conjVec_eq`: `conjVec` sends the coordinates to their conjugates
(`b.conjVec ψ = Σⱼ ⟪ψ, bⱼ⟫ • bⱼ`), so real coordinates leave it unchanged (`sum_repr'`). -/
theorem conjVec_eq_self_of_forall_inner_comm (b : OrthonormalBasis ι 𝕜 E) (ψ : E)
    (h : ∀ i, inner 𝕜 ψ (b i) = inner 𝕜 (b i) ψ) : b.conjVec ψ = ψ := by
  rw [OrthonormalBasis.conjVec]
  simp_rw [h]
  exact b.sum_repr' ψ

/-- **Basis independence of the maximally entangled vector under a real change of basis.**
If every vector of the orthonormal basis `b'` is real relative to the orthonormal basis `b` — i.e.
fixed by the `b`-coordinate conjugation, `b.conjVec (b' k) = b' k`, so that all of its
`b`-coordinates `⟪b i, b' k⟫` are self-conjugate — then the maximally entangled vectors of the two
bases coincide:
`b'.maxEntVec = b.maxEntVec`, that is `Σₖ b'ₖ ⊗ b'ₖ = Σᵢ bᵢ ⊗ bᵢ`.

This is the reusable core of the "and thus we may write" step of Nielsen & Chuang's Equation
(12.203) (Exercise 12.36): expanding the (unnormalised) maximally entangled state in *any* real
orthonormal basis reproduces its computational-basis form. The hypothesis is necessary — for a
genuinely complex change of basis the two vectors differ (this is the vector face of the transpose
trick `(A ⊗ I)|α⟩ = (I ⊗ Aᵀ)|α⟩`). -/
theorem maxEntVec_eq_of_forall_conjVec_eq {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι 𝕜 E) (b' : OrthonormalBasis κ 𝕜 E)
    (h : ∀ k, b.conjVec (b' k) = b' k) :
    b'.maxEntVec = b.maxEntVec := by
  classical
  -- Realness of the coordinates of `b' k` in `b`: `⟪b j, b' k⟫ = ⟪b' k, b j⟫`.
  have hreal : ∀ (k : κ) (j : ι), ⟪b j, b' k⟫_𝕜 = ⟪b' k, b j⟫_𝕜 := fun k j => by
    rw [← b.inner_conjVec_right (b' k) j, h k]
  -- The double coefficient sum collapses via completeness of `b'` and orthonormality of `b`.
  have key : ∀ i j : ι, (∑ k, ⟪b i, b' k⟫_𝕜 * ⟪b j, b' k⟫_𝕜) = (if i = j then (1 : 𝕜) else 0) := by
    intro i j
    simp_rw [fun k => hreal k j]
    rw [b'.sum_inner_mul_inner (b i) (b j), orthonormal_iff_ite.mp b.orthonormal i j]
  rw [OrthonormalBasis.maxEntVec, OrthonormalBasis.maxEntVec]
  calc ∑ k, b' k ⊗ₜ[𝕜] b' k
      = ∑ k, ∑ i, ∑ j, (⟪b i, b' k⟫_𝕜 * ⟪b j, b' k⟫_𝕜) • (b i ⊗ₜ[𝕜] b j) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        conv_lhs => rw [← b.sum_repr' (b' k)]
        rw [TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [TensorProduct.smul_tmul_smul]
    _ = ∑ i, ∑ j, (∑ k, ⟪b i, b' k⟫_𝕜 * ⟪b j, b' k⟫_𝕜) • (b i ⊗ₜ[𝕜] b j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_smul]
    _ = ∑ i, ∑ j, (if i = j then (1 : 𝕜) else 0) • (b i ⊗ₜ[𝕜] b j) := by
        simp_rw [key]
    _ = ∑ i, b i ⊗ₜ[𝕜] b i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp_rw [ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq Finset.univ i (fun j => b i ⊗ₜ[𝕜] b j)]
        simp

end OrthonormalBasis
