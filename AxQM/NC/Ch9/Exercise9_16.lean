/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.MaxEntVec

/-!
# Nielsen & Chuang, Exercise 9.16 (The Hilbert–Schmidt inner product and entanglement)

Show tr(A†B)=<m|(A⊗B)|m> for m=sum |i_R>|i_Q>, Hilbert-Schmidt inner product identity.

## A faithfulness note: `Aᵀ` versus `A†`

N&C write the right-hand side as `tr(A† B)` (with the adjoint / conjugate transpose). With the
standard adjoint that literal form is **off by a complex conjugation of `A`**: the always-true
identity is the **transpose** form
```
⟨m|(A ⊗ B)|m⟩ = tr(Aᵀ B),
```
the well-known "transpose trick" for the maximally entangled vector (the operator counterpart of
`(A ⊗ I)|m⟩ = (I ⊗ Aᵀ)|m⟩`). The two agree exactly when `A` has real matrix entries (`Aᵀ = A†`);
for a genuinely complex `A` they differ, so the literal N&C form is **false as stated** and is
refuted formally below (the `1 × 1` case `A = (i)`, `B = (1)` gives `tr(Aᵀ B) = i` but
`tr(A† B) = -i`). The exercise's namesake, the Hilbert–Schmidt inner product `tr(A† B)`, is
recovered by conjugating the left operator. N&C's own use of the exercise (in the proof of
Uhlmann's theorem, Eqs. (9.68)–(9.69)) is unaffected by the slip, because there the value is taken
in absolute value and the operator is post-multiplied by a freely chosen unitary. The
formalisation therefore states the
honest transpose identity, additionally exhibits the genuine Hilbert–Schmidt inner product, and
formally refutes the book's literal claim.

## The declarations

In `ToMathlib/LinearAlgebra/Matrix/MaxEntVec.lean`:

* `Matrix.maxEntVec` — the (unnormalised) maximally entangled vector `|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ : n × n → R`,
  defined as the vectorisation `(1 : Matrix n n R).vec` of the identity matrix.
* `Matrix.maxEntVec_apply` — its entries: `1` on the diagonal, `0` off it.
* `Matrix.star_maxEntVec_dotProduct_kronecker` — **Exercise 9.16 itself** in its honest form:
  `star (maxEntVec n R) ⬝ᵥ ((A ⊗ₖ B).mulVec (maxEntVec n R)) = (Aᵀ * B).trace`, i.e.
  `⟨m|(A ⊗ B)|m⟩ = tr(Aᵀ B)`, for `A B : Matrix n n R` over any commutative `StarRing` `R`.
* `Matrix.star_maxEntVec_dotProduct_map_star_kronecker` — the companion realising N&C's
  Hilbert–Schmidt inner product `tr(A† B)` by conjugating the left operator:
  `⟨m|((A.map star) ⊗ B)|m⟩ = tr(Aᴴ B)`.
* `Matrix.not_forall_trace_conjTranspose_mul_eq_star_maxEntVec_dotProduct_kronecker` — the formal
  **refutation** of N&C's literal `tr(A† B) = ⟨m|(A ⊗ B)|m⟩`: over `ℂ` it fails, witnessed by the
  `1 × 1` counterexample `A = (i)`, `B = (1)`.
-/
