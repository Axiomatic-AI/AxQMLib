/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Density

/-!
# Trace of a rank-one operator composed with another operator

`tr(|v⟩⟨v| ∘ A) = ⟪v, A v⟫`: the trace of the rank-one self-projector at `v`
composed with `A` is the diagonal matrix element of `A` at `v`. Proof by
trace-cyclicity + `comp_rankOne` + `trace_rankOne`.
-/

@[expose] public section

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- `tr(|v⟩⟨v| ∘ A) = ⟪v, A v⟫`. -/
theorem trace_rankOne_self_comp (v : E) (A : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E (((rankOne 𝕜 v v) ∘L A : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = inner 𝕜 v (A v) := by
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
    ← ContinuousLinearMap.toLinearMap_comp,
    InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne]

end InnerProductSpace
