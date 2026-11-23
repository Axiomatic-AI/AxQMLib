/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Membership in the kernel of a continuous linear map
-/

@[expose] public section

namespace ContinuousLinearMap

variable {R₁ : Type*} {R₂ : Type*} [Semiring R₁] [Semiring R₂]
  {σ₁₂ : R₁ →+* R₂} {M₁ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂]

@[simp]
theorem mem_ker {f : M₁ →SL[σ₁₂] M₂} {x : M₁} : x ∈ LinearMap.ker (f : M₁ →ₛₗ[σ₁₂] M₂) ↔ f x = 0 :=
  LinearMap.mem_ker

end ContinuousLinearMap
