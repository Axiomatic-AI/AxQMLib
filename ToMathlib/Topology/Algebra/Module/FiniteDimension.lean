/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import ToMathlib.Algebra.Ring.Equiv

/-!
# CLM/LM round-trip and ring-inverse bridge lemmas in finite dimensions

A round-trip identity for `LinearMap.toContinuousLinearMap` / the `CLM → LM` coercion, and a
`simp` bridge identifying `Ring.inverse` computed at the `→L` level with `Ring.inverse` computed
at the `→ₗ` level.
-/

universe u v w x

@[expose] public section

variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w}
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] {F' : Type x} [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul 𝕜 F']

variable [CompleteSpace 𝕜]

namespace LinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- Round-trip identity: for a continuous linear map `f` between finite-dimensional spaces,
forgetting continuity and then re-promoting to `→L` recovers `f`. -/
@[simp]
theorem _root_.ContinuousLinearMap.toLinearMap_toContinuousLinearMap (f : E →L[𝕜] F') :
    LinearMap.toContinuousLinearMap (f : E →ₗ[𝕜] F') = f :=
  toContinuousLinearMap.apply_symm_apply f

/-- Ring inverse commutes with the `CLM → LM` coercion in finite dimensions: the inverse of `f` in
the `→L` ring coerces to the inverse of `↑f` in the `→ₗ` ring. Provided as a `@[simp]` bridge so
that expressions like `↑(B - X * Ring.inverse A * X)` reduce to their `→ₗ` counterparts. -/
@[simp]
theorem _root_.ContinuousLinearMap.coe_ringInverse {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E'] (f : E' →L[𝕜] E') :
    ((Ring.inverse f : E' →L[𝕜] E') : E' →ₗ[𝕜] E') = Ring.inverse (f : E' →ₗ[𝕜] E') :=
  (Module.End.toContinuousLinearMap E').symm.toRingEquiv.map_ringInverse f

end LinearMap
