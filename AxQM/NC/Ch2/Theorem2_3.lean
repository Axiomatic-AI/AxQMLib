/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PolarUnitary

/-!
# Nielsen & Chuang, Theorem 2.3 (Polar decomposition)

Polar decomposition: A=UJ=KU with J=sqrt(A^dagger A), K=sqrt(AA^dagger).

The statement is pure linear algebra: the polar decomposition of a square operator on a
finite-dimensional inner product space.

N&C's "vector space `V`" is a finite-dimensional complex inner product space (the statement uses
`A†`, unitarity and positivity), so the formalisation is over `E →L[𝕜] E` with `E` a finite-
dimensional inner product space over an `RCLike` field `𝕜` — a faithful generalisation covering
N&C's `𝕜 = ℂ` case.

## Relation to Mathlib's existing polar decomposition

Mathlib already carries `ContinuousLinearMap.polar_decomposition`
(`T = T.polarPart ∘L T.absoluteValue`), but its factor `T.polarPart` is only a **partial
isometry**, and it gives the left form alone. N&C Theorem 2.3 asserts more: for a *square*
operator there is a genuine **unitary** `U` realising *both* `A = UJ` and `A = KU`. The additional
content is exactly this upgrade — completing the partial isometry to a unitary (possible in the
square finite-dimensional case) — and it is what these declarations provide.

## The declarations

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/PolarUnitary.lean`:

* `ContinuousLinearMap.exists_unitary_isPositive_polar` — the theorem itself (existence): there is
  a unitary `U` and positive `J`, `K` with `A = U ∘L J`, `A = K ∘L U`, `J ∘L J = A† ∘L A` and
  `K ∘L K = A ∘L A†`. The last two identities identify `J` and `K` with the unique positive square
  roots `√(A†A)` and `√(AA†)` (N&C's defining equations for `J`, `K`).
* `ContinuousLinearMap.absoluteValue_eq_of_unitary_comp` — **uniqueness of `J`**: any positive `J'`
  with `A = U' ∘L J'` for a unitary `U'` equals `|A| = √(A†A)`.
* `ContinuousLinearMap.adjoint_absoluteValue_eq_of_comp_unitary` — **uniqueness of `K`**: any
  positive `K'` with `A = K' ∘L U'` for a unitary `U'` equals `|A†| = √(AA†)`.
* `ContinuousLinearMap.unitary_factor_unique_of_isUnit` — **uniqueness of `U`** for invertible `A`:
  the unitary factor of any unitary–positive factorisation of an invertible `A` is unique (N&C's
  "if `A` is invertible then `U` is unique").
* `ContinuousLinearMap.exists_mem_unitary_eq_comp_absoluteValue` — the core left decomposition
  `A = U ∘L |A|` with `U` unitary, from which the two-sided form is assembled.
* `ContinuousLinearMap.norm_apply_eq_norm_absoluteValue_apply` — the supporting isometry fact
  `‖A x‖ = ‖|A| x‖`.

Here `J = A.absoluteValue` is Mathlib's `|A| = √(A†A)`, and `K = U ∘L |A| ∘L U†`, positive as a
unitary conjugate of `|A|`. Together these declarations capture all of Theorem 2.3: existence of
the unitary–positive decomposition `A = UJ = KU`, uniqueness of the positive factors `J`, `K`, and
uniqueness of `U` in the invertible case.
-/
