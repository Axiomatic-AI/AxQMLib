/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EntropyExchange
public import ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropyConcave

/-! # Concavity of the entropy exchange in the quantum operation (Nielsen & Chuang, Exercise 12.13)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 12.13 asks one to show
that the **entropy exchange `S(ρ, E)` is concave in the quantum operation `E`**: for a convex
combination `E = p E₁ + (1 − p) E₂` of two trace-preserving quantum operations,
`p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, E)`.

This file carries out the proof at the operator/Hilbert–Schmidt level on which the entropy exchange
is developed (`ToMathlib/Analysis/InnerProductSpace/EntropyExchange.lean`): a state `ρ` is a density
operator on `H`, and a trace-preserving operation is presented by a finite family of operation
elements `E : ι → (H →L[ℂ] H)` with `∑ᵢ Eᵢ† Eᵢ = 1`.

## The mixture of two operations

The convex combination `p E₁ + (1 − p) E₂` of the operations with element families `E₁ : ι → …` and
`E₂ : κ → …` is the operation with the **combined element family** `channelMix p E₁ E₂` over the
disjoint union `ι ⊕ κ`, obtained by scaling each element of `E₁` by `√p` and each element of `E₂`
by `√(1 − p)` (N&C §8.4.1 — mixing operations amounts to concatenating their operation elements,
weighted by the square roots of the mixing probabilities). This is genuinely the mixed operation:

* `sum_adjoint_mul_channelMix` — it is trace preserving, `∑ₛ (channelMix)ₛ† (channelMix)ₛ = 1`
  (the `√p`/`√(1 − p)` weights make the two completeness relations add to `p·1 + (1 − p)·1 = 1`);
* `krausSumₗ_channelMix` — its action is the convex combination of channel actions,
  `Σₛ (channelMix)ₛ ρ (channelMix)ₛ† = p (Σᵢ E₁ᵢ ρ E₁ᵢ†) + (1 − p) (Σⱼ E₂ⱼ ρ E₂ⱼ†)`, i.e. exactly
  `p E₁(ρ) + (1 − p) E₂(ρ)`.

## The concavity

The reference-plus-system output state `ρ_{R'Q'} = entropyExchangeState b ρ E` is the frame operator
`Σᵢ |vec(√ρ Eᵢ†)⟩⟨vec(√ρ Eᵢ†)|`, so it is **affine in the operation**: scaling the family by `√r`
multiplies each rank-one term by `r` (`entropyExchangeState_real_smul`), and combining families over
`ι ⊕ κ` adds the frame operators (`Fintype.sum_sum_type`), giving

`ρ_{R'Q'}(channelMix p E₁ E₂) = p · ρ_{R'Q'}(E₁) + (1 − p) · ρ_{R'Q'}(E₂)`

(`entropyExchangeState_channelMix`). Since `S(ρ, E) = S(ρ_{R'Q'})`
(`entropyExchange_eq_vonNeumannEntropy_entropyExchangeState`) and the von Neumann entropy is concave
in the density operator (the faithfulness-free form
`ContinuousLinearMap.IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE`; the mixed output
state is generally rank-deficient — e.g. two equal operations give a pure `ρ_{R'Q'}` — so the
faithfulness-free form is essential), the concavity of the entropy exchange
`entropyExchange_channelMix_ge` follows.

## Main results

* `ContinuousLinearMap.channelMix` — the element family of the mixture `p E₁ + (1 − p) E₂`.
* `ContinuousLinearMap.krausSumₗ_channelMix` — the mixture's action is `p E₁(ρ) + (1 − p) E₂(ρ)`.
* `ContinuousLinearMap.entropyExchangeState_channelMix` — the output state is affine in the mixture.
* `ContinuousLinearMap.entropyExchange_channelMix_ge` — **concavity of the entropy exchange**,
  `p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, p E₁ + (1 − p) E₂)` (Nielsen & Chuang, Exercise 12.13).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (entropy exchange), Exercise 12.13; §8.4.1 (mixing quantum operations).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct ComplexConjugate ComplexOrder
open InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ιb ι κ : Type*} [Fintype ιb]

omit [FiniteDimensional ℂ H] in
/-- Absorbing a **real** scalar through the adjoint: `((c : ℂ) • A)† = (c : ℂ) • A†`, since the
complex conjugate of a real number is itself. The elementary scalar lemma behind the `√p`/`√(1−p)`
bookkeeping of a mixed quantum operation. -/
theorem adjoint_real_smul (c : ℝ) (A : H →L[ℂ] H) :
    adjoint ((c : ℂ) • A) = (c : ℂ) • adjoint A := by
  rw [← ContinuousLinearMap.star_eq_adjoint, star_smul, ContinuousLinearMap.star_eq_adjoint,
    show star ((c : ℂ)) = ((c : ℂ)) from Complex.conj_ofReal c]

/-- **The operation-element family of the mixture `p E₁ + (1 − p) E₂`** of two quantum operations
(Nielsen & Chuang §8.4.1). Over the disjoint union `ι ⊕ κ` of the two index sets, it scales the
elements of `E₁` by `√p` and those of `E₂` by `√(1 − p)`, so that `∑ₛ (·)ₛ ρ (·)ₛ†` reproduces the
convex combination `p E₁(ρ) + (1 − p) E₂(ρ)` (see `krausSumₗ_channelMix`). -/
noncomputable def channelMix (p : ℝ) (E₁ : ι → H →L[ℂ] H) (E₂ : κ → H →L[ℂ] H) :
    ι ⊕ κ → H →L[ℂ] H :=
  Sum.elim (fun i => (Real.sqrt p : ℂ) • E₁ i) (fun j => (Real.sqrt (1 - p) : ℂ) • E₂ j)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem channelMix_inl (p : ℝ) (E₁ : ι → H →L[ℂ] H) (E₂ : κ → H →L[ℂ] H) (i : ι) :
    channelMix p E₁ E₂ (Sum.inl i) = (Real.sqrt p : ℂ) • E₁ i := rfl

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem channelMix_inr (p : ℝ) (E₁ : ι → H →L[ℂ] H) (E₂ : κ → H →L[ℂ] H) (j : κ) :
    channelMix p E₁ E₂ (Sum.inr j) = (Real.sqrt (1 - p) : ℂ) • E₂ j := rfl

omit [FiniteDimensional ℂ H] in
/-- `(√r • A)† (√r • A) = r • (A† A)` for `0 ≤ r`: the completeness-preserving scalar law of a
weighted operation element. -/
theorem adjoint_real_smul_mul_self {r : ℝ} (hr : 0 ≤ r) (A : H →L[ℂ] H) :
    adjoint ((Real.sqrt r : ℂ) • A) * ((Real.sqrt r : ℂ) • A) = (r : ℂ) • (adjoint A * A) := by
  rw [adjoint_real_smul, smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hr]

omit [FiniteDimensional ℂ H] in
/-- **The mixture of two trace-preserving operations is trace preserving**: the combined family
`channelMix p E₁ E₂` satisfies the completeness relation `∑ₛ (channelMix)ₛ† (channelMix)ₛ = 1`. The
`√p`/`√(1 − p)` weights turn the two completeness relations `∑ᵢ E₁ᵢ† E₁ᵢ = 1`, `∑ⱼ E₂ⱼ† E₂ⱼ = 1`
into `p · 1 + (1 − p) · 1 = 1`. -/
theorem sum_adjoint_mul_channelMix [Fintype ι] [Fintype κ] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E₁ : ι → H →L[ℂ] H} {E₂ : κ → H →L[ℂ] H} (htp₁ : ∑ i, adjoint (E₁ i) * E₁ i = 1)
    (htp₂ : ∑ j, adjoint (E₂ j) * E₂ j = 1) :
    ∑ s, adjoint (channelMix p E₁ E₂ s) * channelMix p E₁ E₂ s = 1 := by
  have h1p : 0 ≤ 1 - p := by linarith
  rw [Fintype.sum_sum_type]
  simp only [channelMix_inl, channelMix_inr, adjoint_real_smul_mul_self hp0,
    adjoint_real_smul_mul_self h1p, ← Finset.smul_sum, htp₁, htp₂, ← add_smul]
  norm_num

omit [FiniteDimensional ℂ H] in
/-- **The mixed operation acts as the convex combination of the two operations**: for the combined
family `channelMix p E₁ E₂`, the Kraus (operator-sum) action is
`Σₛ (channelMix)ₛ ρ (channelMix)ₛ† = p (Σᵢ E₁ᵢ ρ E₁ᵢ†) + (1 − p) (Σⱼ E₂ⱼ ρ E₂ⱼ†)`, i.e. exactly
`p E₁(ρ) + (1 − p) E₂(ρ)`. This certifies that `channelMix p E₁ E₂` really is the mixture. -/
theorem krausSumₗ_channelMix [Fintype ι] [Fintype κ] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E₁ : ι → H →L[ℂ] H) (E₂ : κ → H →L[ℂ] H) (ρ : H →L[ℂ] H) :
    krausSumₗ (channelMix p E₁ E₂) ρ
      = (p : ℂ) • krausSumₗ E₁ ρ + ((1 - p : ℝ) : ℂ) • krausSumₗ E₂ ρ := by
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  rw [krausSumₗ_apply, Fintype.sum_sum_type, krausSumₗ_apply, krausSumₗ_apply,
    Finset.smul_sum, Finset.smul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) (Finset.sum_congr rfl fun j _ => ?_)
  · rw [channelMix_inl, adjoint_real_smul, smul_comp, comp_smul, comp_smul, smul_smul,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  · rw [channelMix_inr, adjoint_real_smul, smul_comp, comp_smul, comp_smul, smul_smul,
      ← Complex.ofReal_mul, Real.mul_self_sqrt h1p]

omit [FiniteDimensional ℂ H] in
/-- **Scaling a quantum operation by `√r` scales its reference-plus-system output state by `r`**
(`0 ≤ r`): `ρ_{R'Q'}(√r • E) = r • ρ_{R'Q'}(E)`. Each frame vector `vec(√ρ (√r • Eᵢ)†) = √r · vec(√ρ
Eᵢ†)` picks up `√r`, and the rank-one self-projector then picks up `√r · √r = r`
(`InnerProductSpace.rankOne_real_sqrt_smul_self`). The homogeneity behind affinity of
`entropyExchangeState` in the operation. -/
theorem entropyExchangeState_real_smul [Fintype ι] (b : OrthonormalBasis ιb ℂ H) (ρ : H →L[ℂ] H)
    (E : ι → H →L[ℂ] H) {r : ℝ} (hr : 0 ≤ r) :
    entropyExchangeState b ρ (fun i => (Real.sqrt r : ℂ) • E i)
      = (r : ℂ) • entropyExchangeState b ρ E := by
  unfold entropyExchangeState
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hvec : (TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint ((Real.sqrt r : ℂ) • E i))
      = (Real.sqrt r : ℂ) • (TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint (E i)) := by
    rw [adjoint_real_smul, mul_smul_comm, map_smul]
  rw [hvec]
  exact InnerProductSpace.rankOne_real_sqrt_smul_self hr _

omit [FiniteDimensional ℂ H] in
/-- **The reference-plus-system output state is affine in the quantum operation**: for the mixture
`channelMix p E₁ E₂` (with `0 ≤ p ≤ 1`),
`ρ_{R'Q'}(p E₁ + (1 − p) E₂) = p · ρ_{R'Q'}(E₁) + (1 − p) · ρ_{R'Q'}(E₂)`. The frame operator splits
over the disjoint union `ι ⊕ κ` (`Fintype.sum_sum_type`), and each branch is homogeneous of degree
one in the mixing weight (`entropyExchangeState_real_smul`). This is N&C's observation that
`ρ_{R'Q'}` (equivalently the `w`-matrix) is linear in the operation, the operation-side analogue of
its linearity in `ρ`. -/
theorem entropyExchangeState_channelMix [Fintype ι] [Fintype κ] (b : OrthonormalBasis ιb ℂ H)
    (ρ : H →L[ℂ] H) (E₁ : ι → H →L[ℂ] H) (E₂ : κ → H →L[ℂ] H) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyExchangeState b ρ (channelMix p E₁ E₂)
      = (p : ℂ) • entropyExchangeState b ρ E₁
        + ((1 - p : ℝ) : ℂ) • entropyExchangeState b ρ E₂ := by
  have h1p : 0 ≤ 1 - p := by linarith
  rw [entropyExchangeState, Fintype.sum_sum_type, ← entropyExchangeState, ← entropyExchangeState]
  simp only [channelMix_inl, channelMix_inr]
  rw [entropyExchangeState_real_smul b ρ E₁ hp0, entropyExchangeState_real_smul b ρ E₂ h1p]

/-- **Support condition for a convex sum of positive operators**: if `ρᵢ ≥ 0` for all `i`, the
weights `pᵢ ≥ 0`, and `pᵢ > 0`, then `ρᵢ` is supported inside the mixture `∑ⱼ pⱼ ρⱼ`, i.e.
`ker (∑ⱼ pⱼ ρⱼ) ≤ ker ρᵢ`. A vector `x` annihilated by the mixture satisfies
`0 = ∑ⱼ pⱼ ⟪x, ρⱼ x⟫`, a sum of nonnegative terms, so each vanishes; the `i`-th term (with `pᵢ > 0`)
forces `⟪x, ρᵢ x⟫ = 0`, whence `ρᵢ x = 0` by positivity. -/
theorem hasSupportLE_of_sum_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] {J : Type*} [Fintype J] {ρ : J → E →L[ℂ] E}
    (hρ : ∀ j, (ρ j).IsPositive) {p : J → ℝ} (hp : ∀ j, 0 ≤ p j) {i : J} (hpi : 0 < p i) :
    (ρ i).HasSupportLE (∑ j, (p j : ℂ) • ρ j) := by
  rw [ContinuousLinearMap.hasSupportLE_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [ContinuousLinearMap.coe_coe] at hx ⊢
  have hzsum : ∑ j, (p j : ℂ) * inner ℂ x ((ρ j) x) = 0 := by
    have h0 : inner ℂ x ((∑ j, (p j : ℂ) • ρ j) x) = 0 := by rw [hx]; simp
    rw [sum_apply, inner_sum] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun j _ => by
      rw [smul_apply, inner_smul_right]
  have hznn : ∀ j ∈ (Finset.univ : Finset J), (0 : ℂ) ≤ (p j : ℂ) * inner ℂ x ((ρ j) x) :=
    fun j _ => mul_nonneg (by exact_mod_cast hp j) ((hρ j).inner_nonneg_right x)
  have hzi : (p i : ℂ) * inner ℂ x ((ρ i) x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hznn).mp hzsum i (Finset.mem_univ i)
  have hpi' : (p i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpi
  have hinner0 : inner ℂ x ((ρ i) x) = 0 := (mul_eq_zero.mp hzi).resolve_left hpi'
  exact ContinuousLinearMap.apply_eq_zero_of_re_inner_self_eq_zero
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (hρ i)) (by rw [hinner0]; simp)

/-- **Concavity of the entropy exchange in the quantum operation** (Nielsen & Chuang,
Exercise 12.13). For a state `ρ` and two trace-preserving quantum operations with operation-element
families `E₁`, `E₂`, the entropy exchange of the mixture `p E₁ + (1 − p) E₂` (realized by
`channelMix p E₁ E₂`, `krausSumₗ_channelMix`) is at least the convex combination of the two entropy
exchanges:

`p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, p E₁ + (1 − p) E₂)`.

The entropy exchange is the entropy of the reference-plus-system state `ρ_{R'Q'}`
(`entropyExchange_eq_vonNeumannEntropy_entropyExchangeState`), which is affine in the operation
(`entropyExchangeState_channelMix`); concavity then reduces to (the faithfulness-free form of)
concavity of the von Neumann entropy
(`ContinuousLinearMap.IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE`), each mixture
component being supported inside the mixed state (`hasSupportLE_of_sum_smul`). -/
theorem entropyExchange_channelMix_ge [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : OrthonormalBasis ιb ℂ H) {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) (E₁ : ι → H →L[ℂ] H)
    (E₂ : κ → H →L[ℂ] H) (htp₁ : ∑ i, adjoint (E₁ i) * E₁ i = 1)
    (htp₂ : ∑ j, adjoint (E₂ j) * E₂ j = 1) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * entropyExchange ρ E₁ + (1 - p) * entropyExchange ρ E₂
      ≤ entropyExchange ρ (channelMix p E₁ E₂) := by
  have h1p : 0 ≤ 1 - p := by linarith
  rw [entropyExchange_eq_vonNeumannEntropy_entropyExchangeState b hρ.nonneg E₁,
    entropyExchange_eq_vonNeumannEntropy_entropyExchangeState b hρ.nonneg E₂,
    entropyExchange_eq_vonNeumannEntropy_entropyExchangeState b hρ.nonneg (channelMix p E₁ E₂)]
  set σ₁ := entropyExchangeState b ρ E₁ with hσ₁def
  set σ₂ := entropyExchangeState b ρ E₂ with hσ₂def
  set σ := entropyExchangeState b ρ (channelMix p E₁ E₂) with hσdef
  have hσ₁ : σ₁.IsDensityOp := entropyExchangeState_isDensityOp b hρ htp₁
  have hσ₂ : σ₂.IsDensityOp := entropyExchangeState_isDensityOp b hρ htp₂
  have hσ : σ.IsDensityOp :=
    entropyExchangeState_isDensityOp b hρ (sum_adjoint_mul_channelMix hp0 hp1 htp₁ htp₂)
  have haff : σ = (p : ℂ) • σ₁ + ((1 - p : ℝ) : ℂ) • σ₂ :=
    entropyExchangeState_channelMix b ρ E₁ E₂ hp0 hp1
  -- Package the two operations as a `Fin 2`-indexed family for the concavity lemma.
  have hρf : ∀ i : Fin 2, (![σ₁, σ₂] i).IsDensityOp := by
    intro i; fin_cases i
    · simpa using hσ₁
    · simpa using hσ₂
  have hpf : ∀ i : Fin 2, 0 ≤ ![p, 1 - p] i := by
    intro i; fin_cases i
    · simpa using hp0
    · simpa using h1p
  have hσeq : σ = ∑ i : Fin 2, ((![p, 1 - p] i : ℝ) : ℂ) • ![σ₁, σ₂] i := by
    rw [Fin.sum_univ_two]; simpa using haff
  have hsupp : ∀ i : Fin 2, 0 < ![p, 1 - p] i → (![σ₁, σ₂] i).HasSupportLE σ := by
    intro i hi
    rw [hσeq]
    exact hasSupportLE_of_sum_smul (fun j => (hρf j).isPositive) hpf hi
  have key := IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE hρf hσ hpf hσeq hsupp
  rw [Fin.sum_univ_two] at key
  simpa using key

end ContinuousLinearMap
