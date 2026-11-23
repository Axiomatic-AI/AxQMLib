/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A continuous linear map through a scalar multiple of a double sum

A continuous linear map is linear, so it commutes with a scalar multiple and with finite sums.  This
file records the packaged form for a *double* finite sum,

`f (c • ∑ᵢ ∑ⱼ g i j) = c • ∑ᵢ ∑ⱼ f (g i j)`,

as a single named lemma.  It is a convenience wrapper over `map_smul` and `map_sum`, useful when the
whole distribution must be applied in one rewrite (for instance to push an operator through a
double-indexed sum whose summands live in a type whose module instance is only definitionally —
not syntactically — the expected one, so that the individual `map_smul`/`map_sum` rewrites do not
fire termwise).
-/

@[expose] public section

open Finset in
/-- A continuous linear map distributes over a scalar multiple of a double finite sum:
`f (c • ∑ᵢ ∑ⱼ g i j) = c • ∑ᵢ ∑ⱼ f (g i j)`. -/
theorem ContinuousLinearMap.map_smul_double_sum {R : Type*} {M M₂ : Type*} {ι κ : Type*}
    [Semiring R] [Fintype ι] [Fintype κ] [AddCommMonoid M] [TopologicalSpace M] [Module R M]
    [AddCommMonoid M₂] [TopologicalSpace M₂] [Module R M₂] (f : M →L[R] M₂) (c : R)
    (g : ι → κ → M) :
    f (c • ∑ i, ∑ j, g i j) = c • ∑ i, ∑ j, f (g i j) := by
  rw [map_smul, map_sum]; simp_rw [map_sum]
