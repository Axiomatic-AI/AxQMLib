/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues of an idempotent operator

This file records the elementary fact that every eigenvalue of an idempotent linear operator
`T : Module.End 𝕜 E` (`T ∘ T = T`) is either `0` or `1`.

This is the abstract heart of Nielsen & Chuang's *Quantum Computation and Quantum Information*,
Exercise 2.23 ("show that the eigenvalues of a projector `P` are all either `0` or `1`"): a
projector is idempotent (Exercise 2.16), and the eigenvalue restriction uses *only* idempotence,
via the one-line computation `μ² • v = T (T v) = T v = μ • v` on an eigenvector `v ≠ 0`.

## Main results

* `Module.End.HasEigenvalue.eq_zero_or_one_of_isIdempotentElem`: for idempotent `T` and any
  eigenvalue `μ` of `T`, `μ = 0 ∨ μ = 1`.

The file `Mathlib/FieldTheory/IsAlgClosed/Spectrum.lean` proves the sibling
`IsIdempotentElem.spectrum_subset` (`spectrum 𝕜 p ⊆ {0, 1}` for an idempotent element of any
`𝕜`-algebra); this file gives the complementary eigenvalue-predicate (`Module.End.HasEigenvalue`)
form, proved directly from the eigenvector computation rather than through the abstract spectrum.
-/

@[expose] public section

namespace Module.End

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Nielsen & Chuang, Exercise 2.23** (abstract form). Every eigenvalue `μ` of an idempotent
operator `T : Module.End 𝕜 E` (`T ∘ T = T`) is either `0` or `1`.

On an eigenvector `v ≠ 0` with `T v = μ • v`, applying `T` a second time gives
`μ² • v = T (T v) = T v = μ • v` (the middle equality is idempotence), so `(μ² - μ) • v = 0`; since
`v ≠ 0` this forces `μ² = μ`, i.e. `μ (μ - 1) = 0`, whence `μ = 0` or `μ = 1`. Only idempotence is
used — no self-adjointness, completeness, or finite dimensionality. -/
theorem HasEigenvalue.eq_zero_or_one_of_isIdempotentElem
    {T : Module.End 𝕜 E} {μ : 𝕜} (h : T.HasEigenvalue μ) (hT : IsIdempotentElem T) :
    μ = 0 ∨ μ = 1 := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have key : μ ^ 2 • v = μ • v := by
    calc μ ^ 2 • v = T (T v) := by
          rw [hv.apply_eq_smul, map_smul, hv.apply_eq_smul, smul_smul, ← pow_two]
      _ = T v := by rw [← mul_apply_eq_comp, hT.eq]
      _ = μ • v := hv.apply_eq_smul
  exact eq_zero_or_one_of_sq_eq_self (smul_left_injective 𝕜 hv.2 key)

end Module.End
