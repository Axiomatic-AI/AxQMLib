/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The range of a rank-one operator has dimension at most one
-/

public section

namespace InnerProductSpace

/-- The range of a rank-one operator has dimension at most one. -/
lemma finrank_range_rankOne_le_one {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (x : E) (y : F) :
    Module.finrank 𝕜 (LinearMap.range (rankOne 𝕜 x y : F →L[𝕜] E).toLinearMap) ≤ 1 := by
  have hx1 : Module.finrank 𝕜 (𝕜 ∙ x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; exact zero_le_one
    · exact (finrank_span_singleton hx).le
  refine (Submodule.finrank_mono ?_).trans hx1
  rintro _ ⟨z, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end InnerProductSpace
