/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A one-sided bound on the rank of a singleton span
-/

public section

open Module

universe u v

variable {K : Type u} {V : Type v}

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Span

open Submodule

theorem finrank_span_singleton_le_one (v : V) : finrank K (K ∙ v) ≤ 1 := by
  by_cases hv : v = 0
  · subst hv; rw [Submodule.span_zero_singleton, finrank_bot]; exact Nat.zero_le _
  · exact (finrank_span_singleton hv).le

end Span

end DivisionRing
