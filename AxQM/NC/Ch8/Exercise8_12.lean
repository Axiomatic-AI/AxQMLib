/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochAffineDecomposition

/-!
# Nielsen & Chuang, Exercise 8.12 (why `O` can have determinant `1` in `M = O S`)

*(N&C p. 375.)*

Why can O have determinant 1 in the polar decomposition M=OS of the Bloch affine map.

Here (8.93) is the factorization `M = O S` of the real `3 × 3` matrix `M` of the Bloch affine map
`r ↦ M r + c` (N&C (8.89)) obtained from the polar decomposition of `M`, with `O` a real orthogonal
matrix (a *proper rotation* once `det O = 1`) and `S` a real symmetric matrix.

## The answer

An orthogonal matrix satisfies `(det O)² = det (Oᵀ O) = 1`, so `det O = ±1`: the polar factor `O`
is orthogonal but possibly improper. One recovers `det O = 1` by relaxing `S` from the positive
semidefinite polar factor `√(Mᵀ M)` to a merely *symmetric* matrix and negating both factors,
`M = (-O)(-S)`. The factor `-S` stays symmetric, and because the Bloch space has **odd** dimension
`3` the negation flips the determinant, `det (-O) = (-1)³ det O = -det O`, sending an improper `O`
to a proper one `-O ∈ SO(3)`. The cost — `S` need no longer be positive semidefinite — is exactly
the content of the companion Exercise 8.14.

The formal content of Exercise 8.12 is pure linear algebra about
the polar/`O S` factorization of a real `3 × 3` matrix, stated for `Matrix`,
`Matrix.orthogonalGroup`, `Matrix.specialOrthogonalGroup` and `det`. Compare Exercises 8.11 and 8.14
and Theorem 8.3.

The affine-map matrix `M` itself is not constructed: the exercise takes the factorization (8.93) as
given and asks only about the freedom in it, so the formalization quantifies over an arbitrary real
`3 × 3` matrix `M` presented as `M = O S`.

## The formalisation

The formalisation is in `AxQM/Concrete/BlochAffineDecomposition.lean`:

* `AxQM.Concrete.exists_mem_specialOrthogonalGroup_symmetric_factor` — **Exercise 8.12**:
  for any real `3 × 3` matrix `M = O S` with `O` orthogonal and `S` symmetric, there exist a
  proper rotation `O' ∈ SO(3)` and a symmetric `S'` with `M = O' S'` — the det-`1` normalization
  asked for.
* `AxQM.Concrete.det_eq_one_or_neg_one_of_mem_orthogonalGroup` — the supporting fact that
  an orthogonal matrix has determinant `±1`, the reason the polar factor `O` might be improper.

See the module docstring of `AxQM/Concrete/BlochAffineDecomposition.lean` for the full argument (the
odd-dimension negation trick and its link to Exercise 8.14).
-/
