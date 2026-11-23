/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# Nielsen & Chuang, Exercise 2.16 (A projector satisfies `P² = P`)

Show that any projector P satisfies P^2 = P.

N&C define a **projector** (eq. (2.35)) via an orthonormal basis: if `|1⟩, …, |d⟩` is an orthonormal
basis of `V` whose first `k` vectors span a subspace `W`, then `P ≡ ∑_{i=1}^{k} |i⟩⟨i|` is the
projector onto `W`. The exercise asks to show `P² = P` (idempotence); N&C also remark in the same
paragraph that `P` is Hermitian, `P† = P`.

The projector is `∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (v i) (v i)` for an orthonormal family `v`,
and `P² = P` is `IsIdempotentElem P`.

## The declarations

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/RankOneProjector.lean`:

* `InnerProductSpace.orthonormalProjector` — N&C's projector `∑ i ∈ s, |v i⟩⟨v i|`, for a family
  `v : ι → E` and a finite index set `s : Finset ι`.
* `InnerProductSpace.isIdempotentElem_orthonormalProjector` — **the exercise**: for an orthonormal
  family `v`, `IsIdempotentElem (orthonormalProjector 𝕜 v s)`, i.e. `P ∘ P = P` (`P² = P`).
* `InnerProductSpace.isSelfAdjoint_orthonormalProjector` — `P† = P` (N&C's remark that a projector
  is Hermitian); holds for any family, orthonormality unneeded.
* `InnerProductSpace.isStarProjection_orthonormalProjector` — for an orthonormal family, `P` is a
  self-adjoint idempotent (star projection), i.e. a genuine orthogonal projector.

## N&C ↦ Mathlib dictionary and fidelity

* `V` is a (finite-dimensional, complex) Hilbert space; the formalisation is over any inner product
  space `E` over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`; N&C's `ℂ` is the special case). Idempotence
  needs no completeness or finite dimensionality; self-adjointness (which uses the adjoint) adds
  `CompleteSpace E`, supplied in N&C's setting by finite dimensionality.
* The **projector** `P ≡ ∑_{i=1}^{k} |i⟩⟨i|` is `orthonormalProjector 𝕜 v s`, where the orthonormal
  `|i⟩` are `v` (`Orthonormal 𝕜 v`) and the range `1, …, k` is `s : Finset ι`. Summing over an
  arbitrary `Finset s` of an orthonormal family faithfully models the "first `k`" partial sum;
  taking `ι` to be the `k`-element index set and `s = univ` recovers the exact `∑_{i=1}^{k}`, so the
  formalisation is a faithful transcription rather than a weakening (it fixes no dimension and holds
  for every orthonormal family and index subset).
* **`P² = P`** is `IsIdempotentElem P` (`P * P = P`, where `*` on `E →L[𝕜] E` is composition), the
  standard Mathlib spelling of idempotence — exactly N&C's claim.
* The single-vector case (`k = 1`, `‖v i‖ = 1`) is the pre-existing
  `InnerProductSpace.isStarProjection_rankOne_self`; this item generalises it to the sum over an
  orthonormal family, which is the projector N&C's exercise is about.
-/
