/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral

/-!
# A joint integrability/commutation lemma for the non-unital continuous functional calculus

Combines `integrableOn_cfcₙ` and `cfcₙ_setIntegral` into a single lemma, the typical
consumer pattern when establishing operator-valued integral representations.
-/

@[expose] public section

open MeasureTheory Topology
open scoped ContinuousMapZero

section nonunital

open ContinuousMapZero

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

open Function Set in
/-- Joint version of `integrableOn_cfcₙ` and `cfcₙ_setIntegral`: under the same hypotheses,
both the integrability of `fun x ↦ cfcₙ (f x) a` over `s` and the identity
`cfcₙ (fun r ↦ ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ` hold. This is the typical
consumer pattern when establishing operator-valued integral representations: callers want
both conclusions from a single setup. -/
lemma integrableOn_and_cfcₙ_setIntegral [NormedSpace ℝ A]
    [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x ↦ cfcₙ (f x) a) s μ ∧
    cfcₙ (fun r ↦ ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ :=
  ⟨integrableOn_cfcₙ hs f bound a hf f_zero bound_ge bound_int,
    cfcₙ_setIntegral hs f bound a hf f_zero bound_ge bound_int⟩

end nonunital
