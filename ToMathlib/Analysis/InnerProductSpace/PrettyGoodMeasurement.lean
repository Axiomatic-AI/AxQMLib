/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.POVM
public import ToMathlib.Analysis.InnerProductSpace.GeneralizedInverseSqrt

/-!
# The pretty-good (square-root) POVM of a positive family

Given a finite family of positive operators `A : ι → E →L[ℂ] E` on a finite-dimensional complex
inner product space, this file assembles the **pretty-good (square-root) measurement** into a
genuine `POVM` over the outcome set `Option ι`.  With total operator `S = ∑ⱼ A j`, the effects are

`E i = S⁻¹ᐟ² · A i · S⁻¹ᐟ²`   (`some i`),   `E₀ = 1 - ∑ᵢ E i`   (`none`, the "inconclusive"/junk
outcome),

where `S⁻¹ᐟ²` is the generalized inverse square root (`ContinuousLinearMap.genInvSqrt`).  Each `E i`
is positive (conjugation of `A i ≥ 0` by the self-adjoint `S⁻¹ᐟ²`,
`ContinuousLinearMap.genInvSqrt_conjugate_nonneg`), the completeness bound
`ContinuousLinearMap.sum_genInvSqrt_conjugate_le_one` gives `∑ᵢ E i ≤ 1` so the junk effect
`E₀ ≥ 0`, and the two together sum to `1` by construction — the three `POVM` obligations.

## What this file provides

* `POVM.prettyGood` — the pretty-good POVM `POVM (Option ι) ℂ E` of a positive family `A`.
* `POVM.prettyGood_elements_some`, `POVM.prettyGood_elements_none` — the effect formulas.

## Motivation

This is the "square-root measurement" / pretty-good measurement, the decoding POVM at the heart of
the achievability direction of the **Holevo–Schumacher–Westmoreland theorem** (Nielsen & Chuang,
Box 12.5, eq. (12.78)): Bob's decoder is exactly `POVM.prettyGood` applied to the family
`A_M = P · P_M · P` built from the typical projector `P` of the average output `σ̄⊗ⁿ` and the
conditional-typical projectors `P_M` of the codewords, with the junk element `E₀` collecting the
inconclusive outcome.  The construction is stated generally (for any positive family) because it is
the standard reusable object; the physics-specific instantiation is a one-liner in the consumer.

The statements involve only `POVM`, operators `A : E →L[ℂ] E`, the identity `1`, the generalized
inverse square root, and `Finset.sum`; they extend the `POVM` API
(`ToMathlib.Analysis.InnerProductSpace.POVM`) with the completeness core of
`ToMathlib.Analysis.InnerProductSpace.GeneralizedInverseSqrt`.
-/

@[expose] public section

noncomputable section

namespace POVM

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] {ι : Type*} [Fintype ι]

open ContinuousLinearMap in
/-- **The pretty-good (square-root) POVM of a positive family** `A : ι → E →L[ℂ] E`.  With total
operator `S = ∑ⱼ A j`, the effect at outcome `some i` is the conjugation `S⁻¹ᐟ² · A i · S⁻¹ᐟ²`, and
the effect at `none` is the "inconclusive" junk operator `E₀ = 1 - ∑ᵢ S⁻¹ᐟ² · A i · S⁻¹ᐟ²`.

The three POVM obligations are exactly the results of `GeneralizedInverseSqrt`:
* each `some`-effect is positive by `genInvSqrt_conjugate_nonneg` (conjugation of the positive `A i`
  by the self-adjoint `S⁻¹ᐟ²`);
* the `none`-effect is positive because `∑ᵢ E i ≤ 1` (`sum_genInvSqrt_conjugate_le_one`), so
  `1 - ∑ᵢ E i ≥ 0`;
* the effects sum to `1` by `1 - ∑ᵢ E i` cancelling `∑ᵢ E i`.

This is the decoding POVM of the HSW theorem (Nielsen & Chuang, Box 12.5, eq. (12.78)) once `A i` is
instantiated to `P · Pᵢ · P`. -/
def prettyGood (A : ι → E →L[ℂ] E) (hA : ∀ i, 0 ≤ A i) : POVM (Option ι) ℂ E where
  elements := fun o => o.rec
    (1 - ∑ i, (∑ j, A j).genInvSqrt * A i * (∑ j, A j).genInvSqrt)
    (fun i => (∑ j, A j).genInvSqrt * A i * (∑ j, A j).genInvSqrt)
  isPositive := by
    rintro (_ | i)
    · exact nonneg_iff_isPositive.mp
        (sub_nonneg.mpr (sum_genInvSqrt_conjugate_le_one A hA))
    · exact nonneg_iff_isPositive.mp (genInvSqrt_conjugate_nonneg A hA i)
  sum_eq_one := by
    rw [Fintype.sum_option]
    change (1 - ∑ i, (∑ j, A j).genInvSqrt * A i * (∑ j, A j).genInvSqrt)
        + ∑ i, (∑ j, A j).genInvSqrt * A i * (∑ j, A j).genInvSqrt = 1
    abel

open ContinuousLinearMap in
/-- The pretty-good POVM effect at a genuine outcome `some i` is the conjugation
`S⁻¹ᐟ² · A i · S⁻¹ᐟ²` (`S = ∑ⱼ A j`). -/
@[simp]
theorem prettyGood_elements_some (A : ι → E →L[ℂ] E) (hA : ∀ i, 0 ≤ A i) (i : ι) :
    (prettyGood A hA).elements (some i)
      = (∑ j, A j).genInvSqrt * A i * (∑ j, A j).genInvSqrt :=
  rfl

open ContinuousLinearMap in
/-- The pretty-good POVM junk effect at the inconclusive outcome `none` is
`E₀ = 1 - ∑ᵢ S⁻¹ᐟ² · A i · S⁻¹ᐟ²`. -/
@[simp]
theorem prettyGood_elements_none (A : ι → E →L[ℂ] E) (hA : ∀ i, 0 ≤ A i) :
    (prettyGood A hA).elements none
      = 1 - ∑ i, (∑ j, A j).genInvSqrt * A i * (∑ j, A j).genInvSqrt :=
  rfl

end POVM
