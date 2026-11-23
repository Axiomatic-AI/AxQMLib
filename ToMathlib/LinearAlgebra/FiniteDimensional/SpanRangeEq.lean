/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Span equality from a one-sided inclusion and linear independence

If two linearly independent families indexed by the same finite type have one span contained in the
other, then the spans are equal: over a division ring both spans have `finrank` equal to the shared
index cardinality, so the inclusion is forced to be an equality.

## Main results

* `Submodule.span_range_eq_of_le_of_linearIndependent`: for linearly independent families
  `v w : ι → V` over a division ring `K` with `ι` finite, `span (range w) ≤ span (range v)` implies
  `span (range w) = span (range v)`.
-/

@[expose] public section

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Finite ι]

/-- **Span equality from a one-sided inclusion and linear independence.** If `v` and `w` are
linearly independent families indexed by the same finite type and `span (range w) ≤ span (range v)`,
then `span (range w) = span (range v)`. Both spans are finite-dimensional
(`FiniteDimensional.span_of_finite`) with `finrank` equal to the shared index cardinality
(`finrank_span_eq_card`), so the inclusion is an equality by `Submodule.eq_of_le_of_finrank_eq`. -/
theorem Submodule.span_range_eq_of_le_of_linearIndependent {v w : ι → V}
    (hle : Submodule.span K (Set.range w) ≤ Submodule.span K (Set.range v))
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    Submodule.span K (Set.range w) = Submodule.span K (Set.range v) := by
  cases nonempty_fintype ι
  have : FiniteDimensional K (Submodule.span K (Set.range v)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range v)
  exact Submodule.eq_of_le_of_finrank_eq hle
    (by rw [finrank_span_eq_card hw, finrank_span_eq_card hv])
