/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Nielsen & Chuang, Exercise 2.5 (The standard inner product on `ℂⁿ`)

Verify that the defined (.,.) is an inner product on C^n.

Here `(·, ·)` is the map `Cⁿ × Cⁿ → C` of N&C eq. (2.14),
`((y₁, …, yₙ), (z₁, …, zₙ)) ≡ ∑ᵢ yᵢ* zᵢ`, and "an inner product" means it satisfies
the three defining requirements N&C list just above the exercise (p. 66):

1. **Linearity in the second argument** (eq. 2.13):
   `(|v⟩, ∑ᵢ λᵢ |wᵢ⟩) = ∑ᵢ λᵢ (|v⟩, |wᵢ⟩)`.
2. **Conjugate symmetry:** `(|v⟩, |w⟩) = (|w⟩, |v⟩)*`.
3. **Positive definiteness:** `(|v⟩, |v⟩) ≥ 0`, with equality iff `|v⟩ = 0`.

The statement is pure linear algebra: the standard Hermitian form on a finite-dimensional
complex coordinate space satisfies the inner-product axioms.

The result is *already present in Mathlib*: the exercise is discharged by the declarations
below, and this file records their correspondence with N&C's statement.

## The formalisation

N&C's `Cⁿ` (n-tuples of complex numbers) is `EuclideanSpace ℂ (Fin n)`
(`≡ PiLp 2 (fun _ : Fin n => ℂ)`), the finite-dimensional complex coordinate space. Mathlib
equips it with a canonical `InnerProductSpace ℂ` instance, and that *is* the content of the
exercise: producing the instance is exactly verifying that a specified form satisfies the
inner-product axioms. The following existing declarations, all in
`Mathlib/Analysis/InnerProductSpace/`, spell out the correspondence.

* **The formula is N&C's (2.14).** `PiLp.inner_apply` gives
  `inner ℂ x y = ∑ i, inner ℂ (x i) (y i)`, and on each coordinate `RCLike.inner_apply` gives
  `inner ℂ a b = b * conj a`; together `inner ℂ x y = ∑ i, conj (x i) * y i` — precisely the
  Hermitian form `∑ᵢ yᵢ* zᵢ` of eq. (2.14). (`EuclideanSpace.inner_eq_star_dotProduct` records
  the same fact as a conjugated dot product.) Note Mathlib's convention — conjugate-linear in
  the *first* slot, linear in the *second* — matches N&C's exactly, so the three axioms below
  read off without any relabelling.

* **Axiom 1 (linear in the second argument).** `inner_add_right` and `inner_smul_right`
  (`inner ℂ x (r • y) = r * inner ℂ x y`) give additivity and homogeneity; the exact
  finite-sum form of eq. (2.13), `inner ℂ x (∑ i ∈ s, l i • w i) = ∑ i ∈ s, l i * inner ℂ x (w i)`,
  follows by combining `inner_sum` with `inner_smul_right`.

* **Axiom 2 (conjugate symmetry).** `inner_conj_symm`: `conj (inner ℂ y x) = inner ℂ x y`,
  i.e. `(|v⟩, |w⟩) = (|w⟩, |v⟩)*`.

* **Axiom 3 (positive definiteness).** `inner_self_nonneg`: `0 ≤ RCLike.re (inner ℂ x x)`
  (the self-inner-product is a non-negative real), and `inner_self_eq_zero`:
  `inner ℂ x x = 0 ↔ x = 0` — the "with equality iff `|v⟩ = 0`" clause.

N&C's statement is the case `𝕜 = ℂ` of the general `RCLike` machinery (`ℝ` or `ℂ`) over an
arbitrary finite index type; the Mathlib declarations are strictly more general, so this is a
faithful generalisation, not a weakening.
-/
