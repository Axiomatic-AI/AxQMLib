/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # The exponential of a scalar multiple of a sum of commuting elements

`NormedSpace.exp_sum_of_commute` states that in a Banach algebra the exponential of a sum of
pairwise-commuting elements is the (non-commutative) product of their exponentials,
`exp (∑ i, f i) = ∏ i, exp (f i)`. In applications the summands typically appear scaled by a common
scalar — most notably `-i t`, giving the time-evolution operator `e^{-iHt}` of a Hamiltonian
`H = ∑ₖ Hₖ` — so this file records the scalar-scaled form.

* `NormedSpace.exp_smul_sum_of_commute`: for a scalar `c : M` acting on `𝔸` by a distributive
  action compatible with multiplication (`DistribSMul`, `SMulCommClass`, `IsScalarTower`) and a
  pairwise-commuting family `f`, `exp (c • ∑ i, f i) = ∏ i, exp (c • f i)`. The scalar factors out
  of the sum and preserves commutativity, so this reduces to `exp_sum_of_commute` applied to
  `fun i => c • f i`; nothing in the proof uses more than a distributive, multiplication-compatible
  action, so the scalar type is left generic (it covers `ℚ`, `ℝ`, `ℂ`, `𝔸` itself, …).
* `NormedSpace.exp_neg_I_mul_smul_sum_of_commute`: the case `M = ℂ`, `c = -(i t)`, i.e.
  `exp (-(i t) • ∑ₖ Hₖ) = ∏ₖ exp (-(i t) • Hₖ)`.

The second is Exercise 4.47 of Nielsen & Chuang, *Quantum Computation and Quantum Information*
(p. 207): for a Hamiltonian `H = ∑ₖ Hₖ` whose summands mutually commute, `[Hⱼ, Hₖ] = 0`, the
evolution `e^{-iHt}` factors as `e^{-iH₁t} e^{-iH₂t} ⋯ e^{-iH_L t}`. Here the `L` factors are
indexed by an arbitrary `Finset` and the ordered product is a `Finset.noncommProd`: since the
factors commute the product is order-independent, matching the exercise's observation that the
order of the (commuting) factors is immaterial.

`NormedSpace.exp` is defined via the series `expSeries ℚ 𝔸`, so the algebra carries
`[NormedAlgebra ℚ 𝔸]` throughout; the complex scalar `-(i t) • ·` additionally needs
`[NormedAlgebra ℂ 𝔸]`, which is *not* implied by the former (it is carried only by the second
lemma). Concrete algebras such as `Matrix n n ℂ` or the bounded operators `H →L[ℂ] H` on a complex
Hilbert space satisfy both.
-/

@[expose] public section

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- In a Banach algebra, if a family `f` of elements pairwise commute then for any scalar `c`
acting on the algebra by a distributive, multiplication-compatible action the exponential of `c`
times their sum is the (non-commutative) product of the exponentials of `c • f i`:
`exp (c • ∑ i, f i) = ∏ i, exp (c • f i)`.
The scalar-free case is `NormedSpace.exp_sum_of_commute`. -/
theorem exp_smul_sum_of_commute {M ι : Type*} [DistribSMul M 𝔸] [SMulCommClass M 𝔸 𝔸]
    [IsScalarTower M 𝔸 𝔸] (s : Finset ι) (c : M) (f : ι → 𝔸)
    (h : (s : Set ι).Pairwise (Function.onFun Commute f)) :
    exp (c • ∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp (c • f i))
        fun _ hi _ hj hij => (((h hi hj hij).smul_left c).smul_right c).exp := by
  rw [Finset.smul_sum]
  exact exp_sum_of_commute s (fun i => c • f i)
    fun _ hi _ hj hij => ((h hi hj hij).smul_left c).smul_right c

/-- **Nielsen & Chuang, Exercise 4.47.** For a Hamiltonian written as a sum `H = ∑ₖ Hₖ` of
pairwise-commuting summands, the time-evolution operator factors over the summands:
`exp (-(i t) • ∑ₖ Hₖ) = ∏ₖ exp (-(i t) • Hₖ)`,
i.e. `e^{-iHt} = e^{-iH₁t} ⋯ e^{-iH_L t}`. Since the factors commute the product is taken as a
`Finset.noncommProd` and is independent of the order of the summands. This is the `M = ℂ`,
`c = -(i t)` instance of `NormedSpace.exp_smul_sum_of_commute`. -/
theorem exp_neg_I_mul_smul_sum_of_commute [NormedAlgebra ℂ 𝔸] {ι : Type*}
    (s : Finset ι) (t : ℝ) (H : ι → 𝔸)
    (h : (s : Set ι).Pairwise (Function.onFun Commute H)) :
    exp (-(Complex.I * t) • ∑ k ∈ s, H k) =
      s.noncommProd (fun k => exp (-(Complex.I * t) • H k))
        fun _ hi _ hj hij => (((h hi hj hij).smul_left _).smul_right _).exp :=
  exp_smul_sum_of_commute s (-(Complex.I * t)) H h

end NormedSpace
