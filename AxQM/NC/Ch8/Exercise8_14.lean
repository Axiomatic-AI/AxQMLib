/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochAffineDecomposition

/-!
# Nielsen & Chuang, Exercise 8.14 (`det S` need not be positive in `M = O S`)

*(N&C p. 375.)*

Show det(S) need not be positive in the Bloch affine map decomposition.

Here `S` is the real symmetric factor in the decomposition (8.93) `M = O S` of the real `3 × 3`
matrix `M` of the Bloch affine map `r ↦ M r + c` (N&C (8.89)), with `O` a *proper rotation*
(`O ∈ SO(3)`, `det O = 1`) obtained by the normalization of the companion Exercise 8.12.

## The answer

Forcing `det O = 1` (Exercise 8.12) pins the determinant of the remaining factor: since
`det M = det (O S) = det O · det S = det S`, one has `det S = det M`, so `det S` inherits the sign
of `det M` and is positive only for orientation-*preserving* Bloch maps. For an orientation-
reversing map (`det M < 0`) the proper-rotation factorization is therefore forced to have
`det S < 0`. Concretely, the reflection `M = diag(1, 1, -1)` (with `det M = -1`) — whose polar
factor `|M| = √(Mᵀ M) = I` is positive semidefinite with `det = +1` — normalizes (Exercise 8.12)
to `O = -M = diag(-1, -1, 1) ∈ SO(3)`, `S = -I`, and now `det S = det(-I) = -1 < 0`. So relaxing
`S` from *positive semidefinite* (the polar `|M|`) to merely *symmetric* — the price of `det O = 1`
— genuinely costs the positivity of `det S`.

## Fidelity (an arbitrary `M` is a faithful reading, not a weakening)

"Show that `det S` need not be positive" is a claim about the *freedom* in the decomposition (8.93),
and N&C derives (8.93) — via the polar decomposition — for an **arbitrary** real `3 × 3` matrix `M`,
not only for the Bloch matrix of one specific channel. So quantifying the witness theorem
`exists_specialOrthogonalGroup_symmetric_factor_det_neg` over *all* real `M` presented as `O S`
matches the exercise's own generality: it *generalises*, and never narrows — no hypothesis is added
and no dimension is specialized (beyond N&C's own `3`). "Need not be positive" is a non-universality
assertion, whose faithful form is the *existence* of one factorization of the form (8.93) with
`det S < 0` — exactly what is proved — with the companion
`det_right_eq_det_of_mem_specialOrthogonalGroup` supplying the underlying *reason*, `det S = det M`,
at full generality (any dimension `n`, any `O ∈ SO(n)`).

The conclusion is moreover not an artefact of the illustrative reflection witness `diag(1, 1, -1)`
(which is not itself a completely positive map): orientation-reversing Bloch maps (`det M < 0`) do
occur among genuine quantum operations — e.g. the extremal depolarizing channel
`ρ ↦ (2 (tr ρ) · I − ρ) / 3`, whose Bloch matrix is `M = -I/3` with `det M = (-1/3)³ = -1/27 < 0`
(its Choi operator has eigenvalues `2/3, 2/3, 2/3, 0 ≥ 0`, so it is completely positive). For any
such physical map the same `det S = det M` identity forces `det S < 0`; Exercise 8.14's conclusion
therefore holds for real channels as well and is in no way vacuous. (Constructing that channel and
its Bloch matrix is the apparatus (8.90)–(8.92), a separate development the exercise does not ask
for; the witness above is the minimal object that exhibits the freedom the exercise is about.)

## The formalisation

The formal content of Exercise 8.14 is pure linear algebra about the `O S` factorization of a real
`3 × 3` matrix, stated for `Matrix`, `Matrix.specialOrthogonalGroup` and `det`. Compare Exercise
8.12, which concerns the same development.

As with Exercise 8.12, the affine-map matrix `M` is not constructed: the exercise takes the
factorization (8.93) as given, so the formalization quantifies over an arbitrary real `3 × 3`
matrix `M = O S` and exhibits a concrete witness with `det S < 0`.

The formalisation is in `AxQM/Concrete/BlochAffineDecomposition.lean`:

* `AxQM.Concrete.exists_specialOrthogonalGroup_symmetric_factor_det_neg` —
  **Exercise 8.14**: there exist a real `3 × 3` matrix `M`, a proper rotation `O ∈ SO(3)`, and a
  symmetric `S` with `M = O S` and `det S < 0` — a witness showing `det S` need not be positive.
* `AxQM.Concrete.det_right_eq_det_of_mem_specialOrthogonalGroup` — the reason: for any
  `M = O S` with `O ∈ SO(n)`, `det S = det M`, so once `det O = 1` is imposed the sign of `det S`
  is forced to equal that of `det M`.

See the module docstring of `AxQM/Concrete/BlochAffineDecomposition.lean` for the full argument (the
polar-factor/`det O = 1` interplay), and Exercise 8.12 for the `det O = 1` normalization this uses.
-/
