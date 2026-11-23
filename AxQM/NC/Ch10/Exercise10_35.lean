/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroupNegOne

/-!
# Nielsen & Chuang, Exercise 10.35 — `-I ∉ S` implies `g² = I` and `g† = g`

*(N&C §10.5.1, p. 457.)*

For subgroup S of Gn with -I not in S, g^2=I for all g in S, thus g=g-dagger.

## What the exercise asks, and what is proved

In the stabilizer formalism (N&C §10.5.1), `S` is a subgroup of the `n`-qubit Pauli group `Gₙ`, and
a necessary condition for `S` to stabilize a non-trivial code space `V_S` is `-I ∉ S`. This exercise
extracts the two structural consequences of that hypothesis used throughout the chapter (in
particular in the proof of Proposition 10.3, which opens "note first that `gᵢ² = I` for all `i`"):

1. **`g² = I` for all `g ∈ S`.** Every element of the Pauli group squares to a phase-only element
   `±I` (a Pauli string squares to `I`, and the phase `iˢ` squares to `i²ˢ ∈ {1, -1}`). For `g ∈ S`
   the square `g²` lies in `S` by closure, and `g² = -I` is excluded because `-I ∉ S`; hence
   `g² = I`. So `S` is an elementary abelian `2`-group.
2. **`g† = g`.** Since `g² = I`, `g` is its own inverse (`g⁻¹ = g`); and the Pauli operators are
   unitary, so the adjoint (conjugate transpose) is the inverse, `g† = g⁻¹`. Combining, `g† = g` —
   every `g ∈ S` is **Hermitian**. Physically this is why stabilizer generators are genuine
   observables (self-adjoint, with `±1` eigenvalues by `g² = I`).

## Declarations

All in `AxQM/Concrete/PauliGroupNegOne.lean`, which also serves Exercise 10.30; namespace
`AxQM.Concrete.PauliGroup`, for the `n`-qubit Pauli group `PauliGroup n` and a subgroup
`S : Subgroup (PauliGroup n)` with hypothesis `negOne n ∉ S` (`-I ∉ S`):

* `mul_self_eq_one_or_negOne` — the ambient fact that **every** Pauli-group element squares to `±I`:
  `p * p = 1 ∨ p * p = negOne n`. (Supporting lemma; not itself restricted to `S`.)
* `sq_eq_one_of_negOne_notMem` — **`g² = I`**: for `p ∈ S`, `p ^ 2 = 1`. The square is `±I`
  (`mul_self_eq_one_or_negOne`), is in `S` by closure (`Subgroup.mul_mem`), and `-I ∉ S` excludes
  the `-I` case.
* `inv_eq_self_of_negOne_notMem` — **`g⁻¹ = g`** (the group form of `g† = g`): for `p ∈ S`,
  `p⁻¹ = p`, immediate from `g² = I`.
* `toMat_isHermitian_of_negOne_notMem` — **`g† = g`** (the operator form): for `p ∈ S`, the matrix
  `toMat p` is Hermitian, `(toMat p)ᴴ = toMat p`. Combines unitarity of the representation
  (`toMat_inv : (toMat p)ᴴ = toMat p⁻¹`) with `inv_eq_self_of_negOne_notMem`, so the conjugate
  transpose (`†`) equals `g` itself. This is N&C's `g† = g` at the level of the actual operator.

## Faithfulness

* **The exact statement, in full generality.** N&C's `S` is an arbitrary subgroup of `Gₙ`; every
  theorem quantifies over an arbitrary `S : Subgroup (PauliGroup n)` with the sole hypothesis
  `-I ∉ S` (`negOne n ∉ S`), for arbitrary `n`, and concludes exactly `g² = I` and `g† = g`. No
  dimension is specialised and no extra hypothesis is added.
* **`g† = g` is the operator equation, not a proxy.** N&C's `†` is the operator adjoint; the
  formalisation states it as `(toMat g)ᴴ = toMat g` (`Matrix.IsHermitian`, i.e. `conjTranspose`),
  the literal matrix identity — not merely the abstract group fact `g⁻¹ = g`. The unitarity that
  bridges the two (`toMat_inv`) is proved, not assumed.
* **Not a weakening.** The proof uses only subgroup closure and the group's phase arithmetic,
  exactly the argument in the text, and the representation `toMat` is faithful (injective), so the
  statement genuinely concerns the book's Pauli operators.
-/
