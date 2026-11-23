/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Nielsen & Chuang, Exercise 2.13 (Adjoint of an outer product)

Show (|w><v|)^dagger = |v><w|.

The **outer product** `|w⟩⟨v|` is the linear operator whose action is
`(|w⟩⟨v|)(|v'⟩) ≡ ⟨v|v'⟩ |w⟩` (N&C p. 67): the "bra" `⟨v|` contracts the input against `|v⟩` and
the resulting scalar scales the "ket" `|w⟩`. The **adjoint** `A†` is the unique operator satisfying
N&C's eq. (2.32), `(|v⟩, A|w⟩) = (A†|v⟩, |w⟩)`, for all `|v⟩, |w⟩`. The claim is that adjoining an
outer product simply swaps its ket and bra: `(|w⟩⟨v|)† = |v⟩⟨w|`.

The statement is pure linear algebra about a general inner-product space: the adjoint of a
rank-one map swaps its two vectors.

The result is *already present in Mathlib*: the exercise is discharged by the declaration below,
and the dictionary below records its correspondence with N&C's notation.

## The formalisation

`InnerProductSpace.adjoint_rankOne`, in `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`, states —
for `x : E`, `y : F` in complete inner-product spaces `E`, `F` over `𝕜` (`RCLike 𝕜`) — that
`ContinuousLinearMap.adjoint (rankOne 𝕜 x y) = rankOne 𝕜 y x`.
With `x := |w⟩` and `y := |v⟩` this is exactly `(|w⟩⟨v|)† = |v⟩⟨w|`.

## N&C ↦ Mathlib dictionary and fidelity

* `V` is a (finite-dimensional, complex) Hilbert space; Mathlib's lemma is over any complete
  inner-product space over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`), and even allows the ket and bra to
  live in *different* spaces `E`, `F`. N&C's `V = ℂ^d` is the instance `E = F = V`,
  `𝕜 = ℂ`; finite dimensionality supplies the completeness Mathlib requires. This is a faithful
  generalisation, not a weakening — the exercise's "any two vectors" is universally quantified over
  `x, y` here with no extra hypotheses.
* The **outer product** `|w⟩⟨v|` is `InnerProductSpace.rankOne 𝕜 w v`, whose action
  `z ↦ ⟪v, z⟫ • w` is exactly N&C's `(|w⟩⟨v|)(z) = ⟨v|z⟩ |w⟩`: Mathlib's sesquilinear convention
  (conjugate-linear in the first slot, linear in the second) makes `⟪v, z⟫` the bra-ket `⟨v|z⟩`.
* The **adjoint** `A†` is `ContinuousLinearMap.adjoint A`, whose defining property
  `ContinuousLinearMap.adjoint_inner_left`, `⟪A† y, x⟫ = ⟪y, A x⟫`, is precisely N&C's eq. (2.32)
  `(A†|v⟩, |w⟩) = (|v⟩, A|w⟩)` (both inner products conjugate-linear in the first argument).
* Under this dictionary `InnerProductSpace.adjoint_rankOne` reads
  `adjoint (rankOne 𝕜 w v) = rankOne 𝕜 v w`, i.e. `(|w⟩⟨v|)† = |v⟩⟨w|` — precisely the exercise's
  claim.
-/
