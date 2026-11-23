/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.GeneralizedInverseSqrt
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# The square root of a Gram operator via the generalized inverse square root

For a continuous linear map `V : F →L[ℂ] G` between finite-dimensional complex Hilbert spaces, with
total operator `S = V ∘ V⋆` on `G` and Gram operator `Γ = V⋆ ∘ V` on `F`, this file proves the
**Gram square-root identity**

`V⋆ · S⁻¹ᐟ² · V  =  √Γ`   (`√Γ = cfc Real.sqrt Γ`, `S⁻¹ᐟ² = S.genInvSqrt`),

i.e. conjugating the generalized inverse square root of `S = V V⋆` by `V` yields the *ordinary*
operator square root of the Gram operator `Γ = V⋆ V`.

## Motivation

This is the operator content of **Nielsen & Chuang's Box 12.5**, the achievability half of the
**Holevo–Schumacher–Westmoreland theorem** (`χ(E) = C⁽¹⁾(E)`, N&C Theorem 12.8).  There the columns
of `V` are the typical-subspace–compressed codeword eigenvectors `|Ẽ_c⟩ = P |E^M_K⟩` (indexed by
`c = (M, K)` with `K` in the conditional-typical set), so `Γ` is their Gram matrix
`γ_{c,c'} = ⟨Ẽ_c | Ẽ_{c'}⟩` and `S = ∑_M P Pₘ P` is the total operator of the pretty-good decoder.
The coefficients `α_{c,c'} = ⟨Ẽ_c | S⁻¹ᐟ² | Ẽ_{c'}⟩` that N&C introduce between eqs. (12.85) and
(12.86) are exactly the entries of the operator `V⋆ · S⁻¹ᐟ² · V`, and their identity `α = Γ^{1/2}`
— the hinge that makes the diagonal decoding overlap `α_{c,c}` bounded by `1`, so the square-root
operator inequality (12.89)–(12.91) controls the decoding error — is precisely the theorem below.

## What this file provides

* `ContinuousLinearMap.genInvSqrt_mul_self_mul_genInvSqrt_mul_self` — the **support-projection
  identity** `A⁻¹ᐟ² · A · A⁻¹ᐟ² · A = A` for `0 ≤ A`: the support projection of `A` fixes `A`.
* `ContinuousLinearMap.genInvSqrt_supportProj_comp_self` — `S⁻¹ᐟ² · S · S⁻¹ᐟ² · V = V` for
  `S = V ∘ V⋆`: the support projection of `S = V V⋆` fixes the range of `V`.
* `ContinuousLinearMap.adjoint_comp_genInvSqrt_comp_self_mul_self` — `α² = Γ`, i.e.
  `(V⋆ · S⁻¹ᐟ² · V) · (V⋆ · S⁻¹ᐟ² · V) = V⋆ · V`.
* `ContinuousLinearMap.adjoint_comp_genInvSqrt_comp_self` — the **Gram square-root identity**
  `V⋆ · S⁻¹ᐟ² · V = √(V⋆ · V)`.

## Proof

Writing `α = V⋆ · S⁻¹ᐟ² · V`, positivity of `α` is the conjugation of the positive `S⁻¹ᐟ²` by `V`.
For `α² = Γ`: the support projection `P = S⁻¹ᐟ² · S · S⁻¹ᐟ²` of the positive `S` fixes the range of
`V` (`P · V = V`), because the "defect" `W = (1 - P) · V` has `W · W⋆ = (1 - P) · S · (1 - P) = 0`
(as `(1 - P) · S = 0`, folding the triple product of functional-calculus images to
`cfc (x ↦ (√x)⁻¹ · x · (√x)⁻¹ · x) S = cfc id S = S`), hence `W = 0`.  Then

`α² = V⋆ · S⁻¹ᐟ² · (V · V⋆) · S⁻¹ᐟ² · V = V⋆ · (S⁻¹ᐟ² · S · S⁻¹ᐟ²) · V = V⋆ · P · V = V⋆ · V = Γ`.

Finally, a positive operator with square `Γ` is the operator square root of `Γ`: `α = √Γ` by
`cfc_real_sqrt_mul_self_eq_self_of_nonneg` (`0 ≤ α ⟹ √(α · α) = α`).

-/

@[expose] public section

open scoped ComplexOrder

noncomputable section

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
  [CompleteSpace G]

/-- **The support projection of a positive operator fixes the operator.**  For `A ≥ 0`,

`A⁻¹ᐟ² · A · A⁻¹ᐟ² · A = A`,

where `A⁻¹ᐟ² = A.genInvSqrt`.  The composite `A⁻¹ᐟ² · A · A⁻¹ᐟ²` is the orthogonal projection onto
the range of `A`, which acts as the identity on `A`.  Proved by folding the four functional-calculus
images of `A` to a single `cfc` whose symbol `(√x)⁻¹ · x · (√x)⁻¹ · x` equals `x` on the
(nonnegative) spectrum. -/
theorem genInvSqrt_mul_self_mul_genInvSqrt_mul_self {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    A.genInvSqrt * A * A.genInvSqrt * A = A := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f => hsa.continuousOn_spectrum f
  have hfold : A.genInvSqrt * A * A.genInvSqrt * A
      = cfc (fun x => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ * x) A := by
    have hmid : A.genInvSqrt * A * A.genInvSqrt * A
        = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A * cfc (id : ℝ → ℝ) A
            * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A * cfc (id : ℝ → ℝ) A := by
      rw [cfc_id ℝ A]; rfl
    rw [hmid, ← cfc_mul _ _ A (hc _) (hc _), ← cfc_mul _ _ A (hc _) (hc _),
      ← cfc_mul _ _ A (hc _) (hc _)]
    simp only [id_eq]
  rw [hfold]
  conv_rhs => rw [← cfc_id ℝ A]
  refine cfc_congr (fun x hx => ?_)
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  rcases eq_or_lt_of_le hx0 with h | h
  · simp [← h]
  · rw [id_eq]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
    field_simp
    nlinarith [hxx, Real.sq_sqrt hx0]

/-- **The support projection of a positive operator fixes its generalized inverse square root.**
For `A ≥ 0`,

`A⁻¹ᐟ² · (A⁻¹ᐟ² · A · A⁻¹ᐟ²)  =  A⁻¹ᐟ²`,

where `A⁻¹ᐟ² = A.genInvSqrt` and the composite `A⁻¹ᐟ² · A · A⁻¹ᐟ²` is the orthogonal projection onto
the range of `A`.  The left-of-`A⁻¹ᐟ²` companion of `genInvSqrt_mul_self_mul_genInvSqrt_mul_self`
(which fixes `A` instead): the support projection acts as the identity on `A⁻¹ᐟ²`.  Proved by
folding the four functional-calculus images of `A` to a single `cfc` whose symbol
`(√x)⁻¹ · (√x)⁻¹ · x · (√x)⁻¹` equals `(√x)⁻¹` on the (nonnegative) spectrum. -/
theorem genInvSqrt_mul_genInvSqrt_mul_self_mul_genInvSqrt {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    A.genInvSqrt * (A.genInvSqrt * A * A.genInvSqrt) = A.genInvSqrt := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f => hsa.continuousOn_spectrum f
  have hmid : A.genInvSqrt * (A.genInvSqrt * A * A.genInvSqrt)
      = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A
          * cfc (id : ℝ → ℝ) A * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A := by
    rw [cfc_id ℝ A]; rfl
  rw [hmid, ← cfc_mul _ _ A (hc _) (hc _), ← cfc_mul _ _ A (hc _) (hc _),
    ← cfc_mul _ _ A (hc _) (hc _)]
  simp only [id_eq]
  conv_rhs => rw [show A.genInvSqrt = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A from rfl]
  refine cfc_congr (fun x hx => ?_)
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  rcases eq_or_lt_of_le hx0 with h | h
  · simp [← h]
  · have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
    field_simp
    nlinarith [hxx, Real.sq_sqrt hx0]

omit [FiniteDimensional ℂ F] in
/-- **The support projection of `S = V V⋆` fixes the range of `V`.**  For `V : F →L[ℂ] G` with
`S = V ∘ V⋆`,

`S⁻¹ᐟ² · S · S⁻¹ᐟ² · V = V`.

The support projection `P = S⁻¹ᐟ² · S · S⁻¹ᐟ²` of `S` projects onto the range of `S = V V⋆`, which
is the range of `V`; hence `P` fixes `V`.  Concretely, the defect `W = (1 - P) · V` satisfies
`W · W⋆ = (1 - P) · S · (1 - P) = 0` (since `(1 - P) · S = 0` by
`genInvSqrt_mul_self_mul_genInvSqrt_mul_self`), so `W = 0`. -/
theorem genInvSqrt_supportProj_comp_self (V : F →L[ℂ] G) :
    ((V.comp (adjoint V)).genInvSqrt * (V.comp (adjoint V)) *
        (V.comp (adjoint V)).genInvSqrt).comp V = V := by
  set S := V.comp (adjoint V) with hS
  have hSnn : 0 ≤ S := nonneg_iff_isPositive.mpr (isPositive_self_comp_adjoint V)
  set P := S.genInvSqrt * S * S.genInvSqrt with hP
  have h1V : (1 : G →L[ℂ] G).comp V = V := by ext x; simp
  -- `P` is self-adjoint (conjugation of the self-adjoint `S` by the self-adjoint `S⁻¹ᐟ²`).
  have hPsa : IsSelfAdjoint P := by
    rw [hP]
    simpa [(isSelfAdjoint_genInvSqrt hSnn).star_eq] using hSnn.isSelfAdjoint.conjugate S.genInvSqrt
  have hadj1P : adjoint ((1 : G →L[ℂ] G) - P) = 1 - P := by
    rw [← star_eq_adjoint, star_sub, star_one, hPsa.star_eq]
  -- `(1 - P) · S = 0` from the support-projection identity `P · S = S`.
  have hPS : P * S = S := by rw [hP]; exact genInvSqrt_mul_self_mul_genInvSqrt_mul_self hSnn
  have h1PS : (1 - P) * S = 0 := by rw [sub_mul, one_mul, hPS, sub_self]
  -- The defect `W = (1 - P) · V` satisfies `W · W⋆ = (1 - P) · S · (1 - P) = 0`, hence `W = 0`.
  set W := ((1 : G →L[ℂ] G) - P).comp V with hW
  have hWadj : adjoint W = (adjoint V).comp (1 - P) := by
    rw [hW, adjoint_comp, hadj1P]
  have hWW : W.comp (adjoint W) = 0 := by
    have e1 : W.comp (adjoint W) = (1 - P).comp (S.comp (1 - P)) := by
      rw [hW, hWadj, comp_assoc, ← comp_assoc V (adjoint V) (1 - P), ← hS]
    rw [e1, show (1 - P).comp (S.comp (1 - P)) = ((1 - P) * S) * (1 - P) by rw [← comp_assoc]; rfl,
      h1PS, zero_mul]
  have hW0 : W = 0 := by
    have hadjW : adjoint W = 0 :=
      (adjoint_comp_self_eq_zero_iff (A := adjoint W)).mp (by rw [adjoint_adjoint]; exact hWW)
    rw [← adjoint_adjoint W, hadjW, map_zero]
  -- `(1 - P) · V = 0` unfolds to `P · V = V`.
  have hfin : ((1 : G →L[ℂ] G) - P).comp V = 0 := hW0
  rw [sub_comp, h1V, sub_eq_zero] at hfin
  exact hfin.symm

omit [FiniteDimensional ℂ F] in
/-- **The conjugated generalized inverse square root squares to the Gram operator** (`α² = Γ`).  For
`V : F →L[ℂ] G` with `S = V ∘ V⋆` and `α = V⋆ · S⁻¹ᐟ² · V`,

`α · α = V⋆ · V`.

This is the algebraic heart of N&C's `α = Γ^{1/2}` (Box 12.5): expanding `α²` collapses the middle
`S⁻¹ᐟ² · (V V⋆) · S⁻¹ᐟ² = S⁻¹ᐟ² · S · S⁻¹ᐟ²` to the support projection of `S`, which fixes `V`
(`genInvSqrt_supportProj_comp_self`), leaving `V⋆ · V`. -/
theorem adjoint_comp_genInvSqrt_comp_self_mul_self (V : F →L[ℂ] G) :
    ((adjoint V).comp (((V.comp (adjoint V)).genInvSqrt).comp V))
        * ((adjoint V).comp (((V.comp (adjoint V)).genInvSqrt).comp V))
      = (adjoint V).comp V := by
  set S := V.comp (adjoint V) with hS
  have hkey := genInvSqrt_supportProj_comp_self V
  rw [← hS] at hkey
  rw [ContinuousLinearMap.mul_def]
  have hrw : ((adjoint V).comp (S.genInvSqrt.comp V)).comp ((adjoint V).comp (S.genInvSqrt.comp V))
      = (adjoint V).comp ((S.genInvSqrt * S * S.genInvSqrt).comp V) := by
    simp only [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.mul_def]
    rw [← comp_assoc V (adjoint V) (S.genInvSqrt.comp V), ← hS]
  rw [hrw, hkey]

omit [FiniteDimensional ℂ F] in
/-- **The Gram square-root identity** (Nielsen & Chuang, Box 12.5, the identity `α = Γ^{1/2}`
between eqs. (12.85) and (12.86)).  For `V : F →L[ℂ] G` with total operator `S = V ∘ V⋆` on `G`
and Gram operator `Γ = V⋆ ∘ V` on `F`,

`V⋆ · S⁻¹ᐟ² · V  =  √Γ`,

where `S⁻¹ᐟ² = S.genInvSqrt` is the generalized inverse square root and `√Γ = cfc Real.sqrt Γ` is
the ordinary operator square root.  Conjugating the generalized inverse square root of `S = V V⋆` by
`V` yields the operator square root of the Gram operator `Γ = V⋆ V`.

The operator `α = V⋆ · S⁻¹ᐟ² · V` is positive (a conjugation of the positive `S⁻¹ᐟ²`) and squares to
`Γ` (`adjoint_comp_genInvSqrt_comp_self_mul_self`); a positive operator with square `Γ` is the
operator square root of `Γ`, so `α = √Γ` (`cfc_real_sqrt_mul_self_eq_self_of_nonneg`). -/
theorem adjoint_comp_genInvSqrt_comp_self (V : F →L[ℂ] G) :
    (adjoint V).comp (((V.comp (adjoint V)).genInvSqrt).comp V)
      = cfc Real.sqrt ((adjoint V).comp V) := by
  have hSnn : 0 ≤ V.comp (adjoint V) :=
    nonneg_iff_isPositive.mpr (isPositive_self_comp_adjoint V)
  -- `α = V⋆ · S⁻¹ᐟ² · V` is positive: a conjugation of the positive `S⁻¹ᐟ²` by `V`.
  have hαnn : 0 ≤ (adjoint V).comp (((V.comp (adjoint V)).genInvSqrt).comp V) := by
    have h := (nonneg_iff_isPositive.mp (genInvSqrt_nonneg hSnn)).conj_adjoint (adjoint V)
    rw [adjoint_adjoint] at h
    exact nonneg_iff_isPositive.mpr h
  -- `α` is positive with `α · α = Γ`, so `α = √Γ` (`cfc_real_sqrt_mul_self_eq_self_of_nonneg`).
  rw [← adjoint_comp_genInvSqrt_comp_self_mul_self V]
  exact (cfc_real_sqrt_mul_self_eq_self_of_nonneg hαnn).symm

/-- **A projection fixing a positive operator also fixes its generalized inverse square root.**  For
`A ≥ 0` and an operator `P` that fixes `A` on both sides (`A · P = A` and `P · A = A` — e.g. `P` the
orthogonal projection onto a subspace containing the range of `A`, or any `A = P · B · P`),

`A⁻¹ᐟ² · P  =  A⁻¹ᐟ²`,

where `A⁻¹ᐟ² = A.genInvSqrt`.  Since `A⁻¹ᐟ² = cfc (√·)⁻¹ A` is a functional-calculus image of `A`,
it inherits the support of `A`; the hypotheses say `P` is the identity there, so `P` is absorbed.

Concretely, `P` commutes with `A⁻¹ᐟ²` (as it commutes with `A`, `Commute.cfc_real`), and the support
projection `Π = A⁻¹ᐟ² · A · A⁻¹ᐟ²` of `A` absorbs `P` on the right (`Π · P = Π`, moving `P` past
`A⁻¹ᐟ²` by commutation and using `A · P = A`); since `A⁻¹ᐟ² · Π = A⁻¹ᐟ²`
(`genInvSqrt_mul_genInvSqrt_mul_self_mul_genInvSqrt`), `A⁻¹ᐟ² · P = A⁻¹ᐟ² · Π · P = A⁻¹ᐟ² · Π
= A⁻¹ᐟ²`. -/
theorem genInvSqrt_mul_of_mul_eq_self {A : E →L[ℂ] E} (hA : 0 ≤ A) {P : E →L[ℂ] E}
    (hAP : A * P = A) (hPA : P * A = A) :
    A.genInvSqrt * P = A.genInvSqrt := by
  -- The support projection `Π = A⁻¹ᐟ² · A · A⁻¹ᐟ²` of `A` fixes `A⁻¹ᐟ²`:  `A⁻¹ᐟ² · Π = A⁻¹ᐟ²`.
  have hB := genInvSqrt_mul_genInvSqrt_mul_self_mul_genInvSqrt hA
  -- `P` commutes with `A⁻¹ᐟ² = cfc (√·)⁻¹ A` because it commutes with `A`.
  have hcomm : Commute A P := hAP.trans hPA.symm
  have hcommG : A.genInvSqrt * P = P * A.genInvSqrt :=
    Commute.cfc_real hcomm (fun x : ℝ => (Real.sqrt x)⁻¹)
  -- The support projection absorbs `P` on the right:  `Π · P = Π`.
  have hsuppP : (A.genInvSqrt * A * A.genInvSqrt) * P = A.genInvSqrt * A * A.genInvSqrt := by
    calc (A.genInvSqrt * A * A.genInvSqrt) * P
        = A.genInvSqrt * A * (A.genInvSqrt * P) := by rw [mul_assoc]
      _ = A.genInvSqrt * A * (P * A.genInvSqrt) := by rw [hcommG]
      _ = A.genInvSqrt * (A * P) * A.genInvSqrt := by rw [mul_assoc, mul_assoc, mul_assoc]
      _ = A.genInvSqrt * A * A.genInvSqrt := by rw [hAP]
  calc A.genInvSqrt * P
      = (A.genInvSqrt * (A.genInvSqrt * A * A.genInvSqrt)) * P := by rw [hB]
    _ = A.genInvSqrt * ((A.genInvSqrt * A * A.genInvSqrt) * P) := by rw [mul_assoc]
    _ = A.genInvSqrt * (A.genInvSqrt * A * A.genInvSqrt) := by rw [hsuppP]
    _ = A.genInvSqrt := hB

end ContinuousLinearMap
