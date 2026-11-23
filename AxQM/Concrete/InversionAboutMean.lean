/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Concrete: the inversion-about-the-mean operator (Nielsen & Chuang, Exercise 6.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 6.2 (p. 251)
asks to show that the operator `2|ψ⟩⟨ψ| − I` — the second half of the Grover iteration,
`H⊗ⁿ (2|0⟩⟨0| − I) H⊗ⁿ = 2|ψ⟩⟨ψ| − I` (Eq. 6.6) — applied to a general state
`∑ₖ αₖ|k⟩` produces `∑ₖ (−αₖ + 2⟨α⟩)|k⟩` (Eq. 6.7), where `|ψ⟩ = (1/√N) ∑ₓ|x⟩` is the
equally-weighted superposition (6.4) and `⟨α⟩ ≡ (∑ₖ αₖ)/N` is the mean of the amplitudes.
Because the amplitude of each `|k⟩` is reflected through the common mean `⟨α⟩`, this
operator is N&C's *inversion about the mean*.

This is pure finite-dimensional linear algebra over `ℂ^N`: a state `∑ₖ αₖ|k⟩` is the
column vector `v : Fin n → ℂ`, the ket `|ψ⟩` a column vector, the operator `2|ψ⟩⟨ψ| − I`
the `n × n` matrix `2 • (|ψ⟩⟨ψ|) − 1` (the outer product `|ψ⟩⟨ψ|` being
`Matrix.vecMulVec ψ (star ψ)`), and its action on `v` the matrix–vector product `M *ᵥ v`.

## Contents

* `reflectionMatrix u` — the general reflection / "`2P − I`" operator `2|u⟩⟨u| − I`
  built from the rank-one outer product `|u⟩⟨u|`, with action lemma
  `reflectionMatrix_mulVec`. Reusable across the Grover cluster (Ex. 6.1's `2|0⟩⟨0| − I`,
  6.3, 6.6): "inversion about the mean" is just this reflection about `|ψ⟩`.
* `uniformSuperposition n` (`= |ψ⟩`), its component value `uniformSuperposition_apply`,
  self-conjugacy `star_uniformSuperposition`, and normalization
  `uniformSuperposition_dotProduct_self` (`⟨ψ|ψ⟩ = 1`, so `|ψ⟩` is the genuine state 6.4).
* `amplitudeMean v` (`= ⟨α⟩`) and `inversionAboutMean n` (`= 2|ψ⟩⟨ψ| − I`).
* `inversionAboutMean_mulVec_apply` — **the exercise**: the `k`-th component of
  `(2|ψ⟩⟨ψ| − I) v` equals `−vₖ + 2⟨α⟩` (Eq. 6.7).

## Design notes

* The component identity (6.7) is the exercise's content, so the headline theorem is
  stated component-wise (`(inversionAboutMean n *ᵥ v) k = − v k + 2 * amplitudeMean v`),
  matching Eq. (6.7) directly rather than as a vector equality.
* No `NeZero n` is assumed for the reflection/mean results: for `n = 0` they are vacuous
  (`Fin 0` is empty) and the arithmetic `(√n)⁻¹·(√n)⁻¹ = n⁻¹` still holds (`0 = 0`).
  Only normalization `⟨ψ|ψ⟩ = 1` needs `[NeZero n]` (the empty ket has norm `0`).
* The outer-product action `(|u⟩⟨w|) *ᵥ v = ⟨w|v⟩ • |u⟩` underlying every step is
  Mathlib's `Matrix.vecMulVec_mulVec` (whose scalar carries a `MulOpposite.op` for the
  general non-commutative case, discharged here by `op_smul_eq_smul` over the field `ℂ`),
  reused directly rather than re-derived.
-/

namespace AxQM.Concrete

open Matrix

/-- The **reflection operator** `2|u⟩⟨u| − I` as an `n × n` complex matrix, where the
outer product `|u⟩⟨u|` is `Matrix.vecMulVec u (star u)`. For a unit vector `u` this is the
reflection about the line `ℂ · u`; N&C's inversion about the mean (`inversionAboutMean`)
is the special case `u = |ψ⟩`, and Exercise 6.1's phase shift is the case `u = |0⟩`. -/
noncomputable def reflectionMatrix {n : ℕ} (u : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ) • vecMulVec u (star u) - 1

/-- Action of the reflection operator: `(2|u⟩⟨u| − I) v = (2⟨u, v⟩) • u − v`. The outer
product `|u⟩⟨u| = vecMulVec u (star u)` acts by `Matrix.vecMulVec_mulVec`; `op_smul_eq_smul`
drops the `MulOpposite.op` (the scalar `⟨u, v⟩` is central over the commutative field `ℂ`). -/
theorem reflectionMatrix_mulVec {n : ℕ} (u v : Fin n → ℂ) :
    reflectionMatrix u *ᵥ v = (2 * (star u ⬝ᵥ v)) • u - v := by
  rw [reflectionMatrix, sub_mulVec, smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    one_mulVec, smul_smul]

/-- The **equally-weighted superposition** `|ψ⟩ = (1/√N) ∑ₓ|x⟩` (N&C Eq. 6.4), as the
column vector in `ℂ^N` all of whose components equal `(√N)⁻¹`. -/
noncomputable def uniformSuperposition (n : ℕ) : Fin n → ℂ :=
  Function.const (Fin n) ((Real.sqrt n : ℂ))⁻¹

@[simp] theorem uniformSuperposition_apply (n : ℕ) (k : Fin n) :
    uniformSuperposition n k = ((Real.sqrt n : ℂ))⁻¹ := rfl

/-- The uniform superposition is self-conjugate (its components are real): `ψ* = ψ`. -/
theorem star_uniformSuperposition (n : ℕ) :
    star (uniformSuperposition n) = uniformSuperposition n := by
  ext j
  simp only [Pi.star_apply, uniformSuperposition_apply, star_inv₀, Complex.star_def,
    Complex.conj_ofReal]

/-- The reciprocals of `√n` multiply to `1/n` over `ℂ`: `(√n)⁻¹ · (√n)⁻¹ = n⁻¹`
(true for all `n`, including `n = 0` where both sides are `0`). -/
theorem sqrt_inv_mul_sqrt_inv (n : ℕ) :
    ((Real.sqrt n : ℂ))⁻¹ * ((Real.sqrt n : ℂ))⁻¹ = (n : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n),
    Complex.ofReal_natCast]

/-- The uniform superposition is **normalized**: `⟨ψ|ψ⟩ = 1` (so `|ψ⟩` is the genuine
state 6.4). Requires `N ≥ 1`, since the empty ket has zero norm. -/
theorem uniformSuperposition_dotProduct_self (n : ℕ) [NeZero n] :
    star (uniformSuperposition n) ⬝ᵥ uniformSuperposition n = 1 := by
  rw [star_uniformSuperposition, dotProduct]
  simp only [uniformSuperposition_apply, sqrt_inv_mul_sqrt_inv, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- The **mean of the amplitudes** `⟨α⟩ ≡ (∑ₖ αₖ)/N` of a vector `v = ∑ₖ αₖ|k⟩`. -/
noncomputable def amplitudeMean {n : ℕ} (v : Fin n → ℂ) : ℂ := (∑ k, v k) / n

/-- N&C's **inversion-about-the-mean** operator `2|ψ⟩⟨ψ| − I` (Eq. 6.6), the reflection
about the uniform superposition `|ψ⟩`. -/
noncomputable def inversionAboutMean (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  reflectionMatrix (uniformSuperposition n)

/-- **Nielsen & Chuang, Exercise 6.2 / Eq. (6.7).** Applying the inversion-about-the-mean
operator `2|ψ⟩⟨ψ| − I` to a general state `v = ∑ₖ αₖ|k⟩` reflects each amplitude about the
mean: the `k`-th component of `(2|ψ⟩⟨ψ| − I) v` equals `−αₖ + 2⟨α⟩`. -/
theorem inversionAboutMean_mulVec_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (inversionAboutMean n *ᵥ v) k = - v k + 2 * amplitudeMean v := by
  rw [inversionAboutMean, reflectionMatrix_mulVec, star_uniformSuperposition]
  simp only [Pi.sub_apply, Pi.smul_apply, uniformSuperposition_apply, smul_eq_mul, amplitudeMean,
    dotProduct]
  rw [← Finset.mul_sum, div_eq_mul_inv, ← sqrt_inv_mul_sqrt_inv n]
  ring

end AxQM.Concrete
