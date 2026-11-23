/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.RankOneProjector
import ToMathlib.LinearAlgebra.Eigenspace.Idempotent

/-!
# Nielsen & Chuang, Exercise 2.23 (Eigenvalues of a projector are `0` or `1`)

Show the eigenvalues of a projector P are all 0 or 1.

N&C's **projector** (eq. (2.35)) is `P ≡ ∑_{i=1}^{k} |i⟩⟨i|` for an orthonormal basis `|1⟩, …, |d⟩`
whose first `k` vectors span the subspace `W`. The only property of `P` the exercise uses is
idempotence, `P² = P` (Exercise 2.16): if `P|v⟩ = λ|v⟩` for `|v⟩ ≠ 0`, then applying `P` again gives
`λ²|v⟩ = P²|v⟩ = P|v⟩ = λ|v⟩`, so `λ² = λ` and hence `λ ∈ {0, 1}`.

Compare Exercise 2.16 (`P² = P`).

## The declarations

* In `ToMathlib/LinearAlgebra/Eigenspace/Idempotent.lean`:
  `Module.End.HasEigenvalue.eq_zero_or_one_of_isIdempotentElem` — the reusable core, and the
  elementary content the exercise asks to *show*: for any idempotent operator `T : Module.End 𝕜 E`
  and any eigenvalue `μ` of `T`, `μ = 0 ∨ μ = 1`. It isolates the sole property used (idempotence),
  so the projector case is a one-line specialization; it needs no self-adjointness, completeness, or
  finite dimensionality.
* In `ToMathlib/Analysis/InnerProductSpace/RankOneProjector.lean` (alongside Exercise 2.16's
  `orthonormalProjector`):
  * `InnerProductSpace.spectrum_orthonormalProjector_subset` — the spectrum form,
    `spectrum 𝕜 P ⊆ {0, 1}`, via the abstract `IsIdempotentElem.spectrum_subset`.
  * `InnerProductSpace.orthonormalProjector_hasEigenvalue_eq_zero_or_one` — the eigenvalue form:
    every eigenvalue `μ` of `P` satisfies `μ = 0 ∨ μ = 1`, via the reusable core above.

## N&C ↦ Mathlib dictionary and fidelity

* The **projector** `P ≡ ∑_{i=1}^{k} |i⟩⟨i|` is `InnerProductSpace.orthonormalProjector 𝕜 v s` for
  an orthonormal family `v` and finite index set `s` (Exercise 2.16). `V` is a finite-dimensional
  complex Hilbert space in N&C; the formalisation is over any inner product space `E` over `𝕜`
  (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`; N&C's `ℂ` is the special case). No dimension is fixed and no
  hypothesis beyond orthonormality of `v` (used only to secure idempotence) is added.
* An **eigenvalue** `λ` (with `P|v⟩ = λ|v⟩`, `|v⟩ ≠ 0`) is `Module.End.HasEigenvalue`; the projector
  is coerced from `E →L[𝕜] E` to `Module.End 𝕜 E = E →ₗ[𝕜] E`. The complementary spectrum form
  `spectrum 𝕜 P ⊆ {0, 1}` is in fact stronger (every spectral value, not only every eigenvalue, is
  `0` or `1`), so it is a faithful strengthening rather than a weakening.
* "eigenvalues all `0` or `1`" is `μ = 0 ∨ μ = 1`, exactly N&C's claim.

The abstract `IsIdempotentElem.spectrum_subset` (`spectrum 𝕜 p ⊆ {0, 1}` for an idempotent element
of any `𝕜`-algebra) already existed in Mathlib; the eigenvalue-predicate core
`Module.End.HasEigenvalue.eq_zero_or_one_of_isIdempotentElem` and the two projector specializations
are the new content, tying the exercise to N&C's actual projector object from Exercise 2.16.
-/
