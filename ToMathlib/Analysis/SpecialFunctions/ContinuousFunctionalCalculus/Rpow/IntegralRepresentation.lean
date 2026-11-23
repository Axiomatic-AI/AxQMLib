/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
public import ToMathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Operator convexity of the `(1, 2)` integrand

`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation` now
contains the integral representation of `x ↦ x ^ p` (both the scalar and `cfcₙ` versions) for
`p ∈ (0, 1)` and `p ∈ (1, 2)`, together with the operator concavity of `rpowIntegrand₀₁`. The one
piece not (yet) upstream is the operator *convexity* of `rpowIntegrand₁₂` on `p ∈ (1, 2)`, proved
here the same way upstream proves operator concavity of `rpowIntegrand₀₁`: reduce to the `t = 1`
case via the rescaling identity, then relate `rpowIntegrand₁₂ p 1` to `1 - (1 + x)⁻¹` (whose
operator concavity is `CFC.concaveOn_one_sub_one_add_inv_real`) via `id - rpowIntegrand₁₂ p 1 =
(1 - (1+x)⁻¹)`-shaped subtraction.

## Main results

* `CFC.convexOn_cfcₙ_rpowIntegrand₁₂`: `rpowIntegrand₁₂ p t` is operator convex for all
  `p` and all `t ∈ Ioi 0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace CFC
open Real

section NonUnitalCFC

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable {p t x : ℝ}

/-- The `t`-rescaling identity: `rpowIntegrand₁₂ p t x = t ^ (p - 1) · rpowIntegrand₁₂ p 1 (x/t)`
on `Ici 0` for `t > 0`. This is the key step in reducing operator convexity of the integrand at
general `t > 0` to the `t = 1` case. -/
lemma rpowIntegrand₁₂_eqOn_mul_rpowIntegrand₁₂_one (ht : 0 < t) :
    (Ici 0).EqOn (rpowIntegrand₁₂ p t)
      (fun x ↦ t ^ (p - 1) * (rpowIntegrand₁₂ p 1 (t⁻¹ • x))) := by
  intro x (hx : 0 ≤ x)
  simp only [rpowIntegrand₁₂, smul_eq_mul, Real.one_rpow, one_mul, inv_one]
  have ht' : t ≠ 0 := ht.ne'
  have htx : (t + x) ≠ 0 := by positivity
  have h1tx : (1 + t⁻¹ * x) ≠ 0 := by positivity
  field_simp

lemma continuousOn_rpowIntegrand₁₂_Ici (ht : 0 < t) :
    ContinuousOn (rpowIntegrand₁₂ p t) (Ici 0) :=
  (continuousOn_rpowIntegrand₁₂_uncurry _ (fun _ a ↦ a)).uncurry_left t ht

/-- Generic `cfcₙ`-rescaling: if `f` is pointwise equal to `c • g ∘ (t⁻¹ • ·)` on `Ici 0`,
`g` is continuous on `Ici 0` and vanishes at `0`, then `cfcₙ f a = c • cfcₙ g (t⁻¹ • a)` for
`0 ≤ a` and `0 < t`. -/
private lemma cfcₙ_eq_smul_cfcₙ_smul_inv_of_eqOn
    {f g : ℝ → ℝ} {t c : ℝ} (ht : 0 < t)
    (h_eqOn : (Ici 0).EqOn f (fun x ↦ c * g (t⁻¹ • x)))
    (h_cont : ContinuousOn g (Ici 0)) (hg0 : g 0 = 0)
    (a : A) (ha : 0 ≤ a) :
    cfcₙ f a = c • cfcₙ g (t⁻¹ • a) := by
  have hspec : quasispectrum ℝ a ⊆ Ici 0 := by grind
  have h_mapsTo : MapsTo (t⁻¹ • · : ℝ → ℝ) (Ici 0) (Ici 0) := by
    intro x hx
    simp only [mem_Ici, smul_eq_mul] at hx ⊢
    positivity
  have h_cont_comp : ContinuousOn (fun x ↦ g (t⁻¹ • x)) (Ici 0) :=
    h_cont.comp (by fun_prop) h_mapsTo
  calc _ = cfcₙ (fun x ↦ c * (g (t⁻¹ • x))) a := cfcₙ_congr (Set.EqOn.mono hspec h_eqOn)
    _ = c • cfcₙ (fun x ↦ g (t⁻¹ • x)) a := by
          refine cfcₙ_smul (R := ℝ) c _ a (h_cont_comp.mono hspec) ?_
          simpa using hg0
    _ = c • cfcₙ g (t⁻¹ • a) := by
          congr! 1
          refine cfcₙ_comp_smul (R := ℝ) t⁻¹ g a
            (h_cont.mono (h_mapsTo.mono_left hspec).image_subset) ?_
          simpa using hg0

lemma cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one {p t : ℝ} (ht : 0 < t)
    (a : A) (ha : 0 ≤ a) :
    cfcₙ (rpowIntegrand₁₂ p t) a = t ^ (p - 1) • cfcₙ (rpowIntegrand₁₂ p 1) (t⁻¹ • a) :=
  cfcₙ_eq_smul_cfcₙ_smul_inv_of_eqOn ht (rpowIntegrand₁₂_eqOn_mul_rpowIntegrand₁₂_one ht)
    (continuousOn_rpowIntegrand₁₂_Ici zero_lt_one) (rpowIntegrand₁₂_zero zero_lt_one) a ha

end NonUnitalCFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The `cfcₙ`-level decomposition at `t = 1`: `cfcₙ (rpowIntegrand₁₂ p 1) c = c - cfcₙ φ c`
where `φ x = 1 - (1 + x)⁻¹`. Lets the operator convexity of `rpowIntegrand₁₂ p 1` reduce to
the operator concavity of `φ` (`CFC.concaveOn_one_sub_one_add_inv_real`) via
`(c ↦ c) - (op-concave) = op-convex`. -/
private lemma cfcₙ_rpowIntegrand₁₂_one_eq_sub (p : ℝ) (c : A) (hc : 0 ≤ c) :
    cfcₙ (rpowIntegrand₁₂ p 1) c = c - cfcₙ (fun x : ℝ ↦ 1 - (1 + x)⁻¹) c :=
  calc cfcₙ (rpowIntegrand₁₂ p 1) c
      = cfcₙ (fun x : ℝ ↦ x - (1 - (1 + x)⁻¹)) c := by
        refine cfcₙ_congr fun x _ ↦ ?_
        simp only [Real.rpowIntegrand₁₂, Real.one_rpow, one_mul, inv_one]
        ring
    _ = cfcₙ (fun x : ℝ ↦ x) c - cfcₙ (fun x : ℝ ↦ 1 - (1 + x)⁻¹) c := by
        refine cfcₙ_sub _ _ c (hg := ?_)
        refine ContinuousOn.sub continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun x hx ↦ ?_)
        have : (0 : ℝ) ≤ x := by grind
        linarith
    _ = c - cfcₙ (fun x : ℝ ↦ 1 - (1 + x)⁻¹) c := by rw [cfcₙ_id' ℝ c]

/-- `rpowIntegrand₁₂ p t` is operator convex for all `p` and all `t ∈ Ioi 0`. -/
lemma convexOn_cfcₙ_rpowIntegrand₁₂ {p : ℝ} {t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : A)) (cfcₙ (rpowIntegrand₁₂ p t)) := by
  refine ⟨convex_Ici 0, fun a (ha : 0 ≤ a) b (hb : 0 ≤ b) α β hα hβ hαβ ↦ ?_⟩
  have hab : (0 : A) ≤ α • a + β • b := add_nonneg (smul_nonneg hα ha) (smul_nonneg hβ hb)
  rw [cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one ht a ha,
      cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one ht b hb,
      cfcₙ_rpowIntegrand₁₂_eq_cfcₙ_rpowIntegrand₁₂_one ht (α • a + β • b) hab,
      smul_comm α (t ^ (p - 1)), smul_comm β (t ^ (p - 1)), ← smul_add]
  refine smul_le_smul_of_nonneg_left ?_ (by positivity)
  rw [cfcₙ_rpowIntegrand₁₂_one_eq_sub p _ (by positivity),
      cfcₙ_rpowIntegrand₁₂_one_eq_sub p _ (by positivity : (0 : A) ≤ t⁻¹ • a),
      cfcₙ_rpowIntegrand₁₂_one_eq_sub p _ (by positivity : (0 : A) ≤ t⁻¹ • b),
      smul_sub, smul_sub, sub_add_sub_comm,
      smul_add, smul_comm t⁻¹ α a, smul_comm t⁻¹ β b, sub_le_sub_iff_left]
  refine CFC.concaveOn_one_sub_one_add_inv_real.2
    (?_ : 0 ≤ t⁻¹ • a) (?_ : 0 ≤ t⁻¹ • b) hα hβ hαβ <;> positivity

end NonUnitalCStarAlgebra

end CFC
