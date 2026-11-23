/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Basic.Complex.Basic

/-! # The maximally entangled vector and the Hilbert–Schmidt pairing

Fix a finite index type `n` and a ring `R`. The **(unnormalised) maximally entangled vector**
`|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ`, indexed by `n × n`, is exactly the vectorisation `Matrix.vec` of the identity
matrix. This file records that vector as `Matrix.maxEntVec` and proves that the sesquilinear pairing
`⟨m| (A ⊗ B) |m⟩` of the identity applied to a Kronecker product collapses to a single trace.

## Main definitions

* `Matrix.maxEntVec n R` — the maximally entangled vector `∑ᵢ eᵢ ⊗ eᵢ : n × n → R`, defined as
  `(1 : Matrix n n R).vec`. Its entries are `1` on the diagonal `i = j` and `0` off it
  (`Matrix.maxEntVec_apply`).

## Main results

* `Matrix.star_maxEntVec_dotProduct_kronecker` — the identity
  `⟨m| (A ⊗ₖ B) |m⟩ = tr(Aᵀ * B)`, written as
  `star (maxEntVec n R) ⬝ᵥ ((A ⊗ₖ B).mulVec (maxEntVec n R)) = (Aᵀ * B).trace`. Here
  `star _ ⬝ᵥ _` is the standard sesquilinear pairing of vectors (the bra–ket `⟨·|·⟩`), so the left
  side is the expectation value of the operator `A ⊗ B` in the maximally entangled state `|m⟩`.
* `Matrix.star_maxEntVec_dotProduct_map_star_kronecker` — its companion recovering the genuine
  **Hilbert–Schmidt inner product** `tr(Aᴴ * B)`: one must conjugate the left factor,
  `⟨m| ((A.map star) ⊗ₖ B) |m⟩ = tr(Aᴴ * B)`.
* `Matrix.not_forall_trace_conjTranspose_mul_eq_star_maxEntVec_dotProduct_kronecker` — the sharpness
  counterexample: the literal Nielsen & Chuang form `tr(Aᴴ * B) = ⟨m|(A ⊗ B)|m⟩` (with the plain,
  unconjugated `A`) is **false** over `ℂ`. The `1 × 1` witness `A = (i)`, `B = (1)` gives
  `tr(Aᵀ B) = i` on the right but `tr(Aᴴ B) = -i` on the left.
* `Matrix.kronecker_mulVec_maxEntVec` — the **vector** face of the transpose trick, in Choi form:
  `(A ⊗ₖ B) |m⟩ = vec (B * Aᵀ)`.
* `Matrix.kronecker_one_mulVec_maxEntVec` — the **ricochet identity** `(A ⊗ I)|m⟩ = (I ⊗ Aᵀ)|m⟩`:
  an operator on one half of `|m⟩` moves, as its transpose, to the other half.
* `Matrix.kronecker_map_star_mulVec_maxEntVec_of_isHermitian_of_isIdempotent` and its companion
  `Matrix.star_kronecker_one_mulVec_maxEntVec_dotProduct_self_of_isHermitian_of_isIdempotent` — for
  an orthogonal projector `P`, projecting `|m⟩` on both halves equals projecting on one half, and
  the resulting vector has squared norm `tr P = dim (range P)`: the projected maximally entangled
  state is the maximally entangled state on `range P`.

## Relation to Nielsen & Chuang, Exercise 9.16

N&C, *Quantum Computation and Quantum Information* (Exercise 9.16, p. 411, "The Hilbert–Schmidt
inner product and entanglement"), state the identity as `tr(A† B) = ⟨m|(A ⊗ B)|m⟩` with
`|m⟩ = ∑ᵢ |i_R⟩|i_Q⟩`. With the standard adjoint (conjugate transpose) that literal form is off by a
complex conjugation of `A`: the honest, always-true identity is the **transpose** form
`⟨m|(A ⊗ B)|m⟩ = tr(Aᵀ B)` (`star_maxEntVec_dotProduct_kronecker`) — this is the well-known
"transpose trick" for the maximally entangled vector, the operator counterpart of
`(A ⊗ I)|m⟩ = (I ⊗ Aᵀ)|m⟩`. The two agree exactly when `A` has real matrix entries (then
`Aᵀ = Aᴴ`); for a genuinely complex `A` they differ, and the literal N&C form is refuted formally by
`not_forall_trace_conjTranspose_mul_eq_star_maxEntVec_dotProduct_kronecker` (the `1 × 1` witness
`A = (i)`, `B = (1)` gives `tr(Aᵀ B) = i` but `tr(Aᴴ B) = -i`). The exercise's namesake — the
Hilbert–Schmidt inner product `tr(Aᴴ B)` — is recovered by conjugating the left operator
(`star_maxEntVec_dotProduct_map_star_kronecker`). N&C's own use of the exercise (in the proof of
Uhlmann's theorem, Eqs. (9.68)–(9.69)) is unaffected by the slip, since there the value is taken in
absolute value and the operator is post-multiplied by a freely chosen unitary.
-/

@[expose] public section

open scoped Kronecker Matrix

namespace Matrix

variable {n : Type*} {R : Type*}

/-- The (unnormalised) **maximally entangled vector** `|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ` on `n × n`, defined as the
vectorisation `Matrix.vec` of the identity matrix `1 : Matrix n n R`. (Nielsen & Chuang,
Exercise 9.16, write this as `|m⟩ = ∑ᵢ |i_R⟩|i_Q⟩`.) -/
def maxEntVec (n R : Type*) [DecidableEq n] [Zero R] [One R] : n × n → R :=
  (1 : Matrix n n R).vec

@[simp]
theorem maxEntVec_apply [DecidableEq n] [Zero R] [One R] (i j : n) :
    maxEntVec n R (i, j) = if i = j then 1 else 0 := by
  simp [maxEntVec, Matrix.vec, Matrix.one_apply, eq_comm]

/-- **The Hilbert–Schmidt pairing via the maximally entangled vector** (Nielsen & Chuang,
Exercise 9.16, in its honest transpose form). The expectation value of a Kronecker product
`A ⊗ B` in the maximally entangled state `|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ` is the trace `tr(Aᵀ * B)`:
`⟨m| (A ⊗ₖ B) |m⟩ = tr(Aᵀ * B)`, where `star _ ⬝ᵥ _` is the standard sesquilinear (bra–ket)
pairing of vectors. (See the module docstring: N&C write the right side as `tr(Aᴴ * B)`, but with
the standard adjoint the always-true identity uses the transpose; the two coincide iff `A` is
real.) -/
theorem star_maxEntVec_dotProduct_kronecker [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    (A B : Matrix n n R) :
    star (maxEntVec n R) ⬝ᵥ ((A ⊗ₖ B).mulVec (maxEntVec n R)) = (Aᵀ * B).trace := by
  unfold maxEntVec
  rw [Matrix.kronecker_mulVec_vec B 1 A, Matrix.star_vec_dotProduct_vec,
    Matrix.conjTranspose_one, one_mul, mul_one, Matrix.trace_mul_comm]

/-- **The genuine Hilbert–Schmidt inner product via the maximally entangled vector.** To realise
`tr(Aᴴ * B)` — the Hilbert–Schmidt inner product `⟪A, B⟫` that names Nielsen & Chuang's
Exercise 9.16 — as an expectation value in the maximally entangled state, the left operator must be
conjugated (`A.map star` is the entrywise complex conjugate):
`⟨m| ((A.map star) ⊗ₖ B) |m⟩ = tr(Aᴴ * B)`. This is the corrected form of N&C's `tr(A† B)`. -/
theorem star_maxEntVec_dotProduct_map_star_kronecker [Fintype n] [DecidableEq n] [CommRing R]
    [StarRing R] (A B : Matrix n n R) :
    star (maxEntVec n R) ⬝ᵥ ((A.map star ⊗ₖ B).mulVec (maxEntVec n R)) = (Aᴴ * B).trace := by
  rw [star_maxEntVec_dotProduct_kronecker]; rfl

/-- **Sharpness: Nielsen & Chuang's literal `tr(A† B)` form is false.** N&C, Exercise 9.16, write
the identity as `tr(Aᴴ * B) = ⟨m|(A ⊗ B)|m⟩` with the plain, unconjugated `A`. Over `ℂ` that literal
claim fails: the always-true right-hand side is `tr(Aᵀ * B)`
(`star_maxEntVec_dotProduct_kronecker`), which differs from `tr(Aᴴ * B)` unless `A` is real. The
`1 × 1` witness `A = (i)`, `B = (1)` gives `tr(Aᵀ B) = i` but `tr(Aᴴ B) = -i`. -/
theorem not_forall_trace_conjTranspose_mul_eq_star_maxEntVec_dotProduct_kronecker :
    ¬ ∀ A B : Matrix (Fin 1) (Fin 1) ℂ,
      (Aᴴ * B).trace = star (maxEntVec (Fin 1) ℂ) ⬝ᵥ ((A ⊗ₖ B).mulVec (maxEntVec (Fin 1) ℂ)) := by
  intro h
  have H := h (Complex.I • 1) 1
  rw [star_maxEntVec_dotProduct_kronecker, mul_one, mul_one, Matrix.trace_conjTranspose,
    Matrix.trace_transpose] at H
  norm_num [Matrix.trace_smul, Matrix.trace_one, Complex.ext_iff] at H

/-! ### The transpose trick in vector form, and the entangled state of a projector

The pairing identity `star_maxEntVec_dotProduct_kronecker` above is the *operator* face of the
transpose trick. Its *vector* face is the **ricochet identity** `(A ⊗ I)|m⟩ = (I ⊗ Aᵀ)|m⟩`
(`kronecker_one_mulVec_maxEntVec`): an operator acting on one half of the maximally entangled state
can be moved, as its transpose, onto the other half. We record it here together with the general
Choi form `(A ⊗ B)|m⟩ = vec (B Aᵀ)` (`kronecker_mulVec_maxEntVec`) that it specialises.

Applied to a Hermitian idempotent `P` (an orthogonal projector) these describe the **entangled state
of a projector**: acting with `P` on one half equals acting with the conjugate `P.map star` on both
halves (`kronecker_map_star_mulVec_maxEntVec_of_isHermitian_of_isIdempotent`), and the resulting
vector `vec Pᵀ` has squared norm `tr P` — the rank of `P`, i.e. the dimension of its range
(`star_kronecker_one_mulVec_maxEntVec_dotProduct_self_of_isHermitian_of_isIdempotent`). This is the
linear-algebra core of *entanglement distillation by error-correction* (Nielsen & Chuang,
Exercise 12.34): the maximally entangled state of `n` EPR pairs, projected on both halves onto a
stabiliser code space `V_S = range P`, is the (unnormalised) maximally entangled state on
`V_S ⊗ V_S` — an encoded family of `dim V_S = 2^m` Bell pairs. -/

/-- **The transpose trick, Choi form.** The image of the maximally entangled vector
`|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ` under a Kronecker product `A ⊗ B` is the vectorisation of `B * Aᵀ`:
`(A ⊗ₖ B) |m⟩ = vec (B * Aᵀ)`. (The identity-matrix bookkeeping of `Matrix.kronecker_mulVec_vec`
collapses `∑ᵢ (B eᵢ) ⊗ (A eᵢ)` to a single vectorised product.) -/
theorem kronecker_mulVec_maxEntVec [Fintype n] [DecidableEq n] [CommRing R]
    (A B : Matrix n n R) :
    (A ⊗ₖ B).mulVec (maxEntVec n R) = (B * Aᵀ).vec := by
  unfold maxEntVec
  rw [Matrix.kronecker_mulVec_vec B 1 A, mul_one]

/-- **The transpose trick, ricochet form.** An operator `A` acting on the first (left) half of the
maximally entangled vector can be moved to the second (right) half as its transpose:
`(A ⊗ I)|m⟩ = (I ⊗ Aᵀ)|m⟩`. This is the vector counterpart of the operator-pairing form
`star_maxEntVec_dotProduct_kronecker` (`⟨m| A ⊗ B |m⟩ = tr(Aᵀ B)`), and the identity referenced in
the module docstring; both sides equal `vec Aᵀ`. -/
theorem kronecker_one_mulVec_maxEntVec [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) :
    (A ⊗ₖ (1 : Matrix n n R)).mulVec (maxEntVec n R)
      = ((1 : Matrix n n R) ⊗ₖ Aᵀ).mulVec (maxEntVec n R) := by
  rw [kronecker_mulVec_maxEntVec, kronecker_mulVec_maxEntVec, one_mul, transpose_one, mul_one]

/-- For a Hermitian matrix `P` (`Pᴴ = P`), the entrywise complex conjugate `P.map star` coincides
with the transpose `Pᵀ`. (In general `Aᴴ = Aᵀ.map star`; Hermiticity `Aᴴ = A` turns this into
`A.map star = Aᵀ`.) -/
theorem map_star_eq_transpose_of_isHermitian [Star R]
    {P : Matrix n n R} (hHerm : Pᴴ = P) : P.map star = Pᵀ := by
  rw [← Matrix.conjTranspose_transpose, hHerm]

/-- **Projecting both halves = projecting one half.** For an orthogonal projector `P` — Hermitian
(`Pᴴ = P`) and idempotent (`P * P = P`) — acting with `P` on the left half of the maximally
entangled vector and with its conjugate `P.map star` on the right half gives the same vector as
acting with `P` on the left half alone: `(P ⊗ P̄)|m⟩ = (P ⊗ I)|m⟩`. Physically: identical stabiliser
measurements on the two halves of a family of EPR pairs land both halves in the *same* code space,
so a single projection already captures the joint (both-halves-corrected) outcome. -/
theorem kronecker_map_star_mulVec_maxEntVec_of_isHermitian_of_isIdempotent [Fintype n]
    [DecidableEq n] [CommRing R] [StarRing R] {P : Matrix n n R} (hHerm : Pᴴ = P)
    (hIdem : P * P = P) :
    (P ⊗ₖ P.map star).mulVec (maxEntVec n R)
      = (P ⊗ₖ (1 : Matrix n n R)).mulVec (maxEntVec n R) := by
  rw [kronecker_mulVec_maxEntVec, kronecker_mulVec_maxEntVec, one_mul,
    map_star_eq_transpose_of_isHermitian hHerm, ← Matrix.transpose_mul, hIdem]

/-- **The projected maximally entangled vector has squared norm `tr P`.** For an orthogonal
projector `P` (Hermitian and idempotent), the vector `(P ⊗ I)|m⟩` obtained by projecting one half of
the maximally entangled state satisfies `⟨(P ⊗ I)m | (P ⊗ I)m⟩ = tr P`. Since `tr P = dim (range P)`
for a projector, this identifies `(P ⊗ I)|m⟩` as the (unnormalised) maximally entangled state on the
`tr P`-dimensional subspace `range P`: its squared norm equals that dimension. -/
theorem star_kronecker_one_mulVec_maxEntVec_dotProduct_self_of_isHermitian_of_isIdempotent
    [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] {P : Matrix n n R}
    (hHerm : Pᴴ = P) (hIdem : P * P = P) :
    star ((P ⊗ₖ (1 : Matrix n n R)).mulVec (maxEntVec n R)) ⬝ᵥ
        ((P ⊗ₖ (1 : Matrix n n R)).mulVec (maxEntVec n R)) = P.trace := by
  rw [kronecker_mulVec_maxEntVec, one_mul, Matrix.star_vec_dotProduct_vec,
    Matrix.transpose_conjTranspose, map_star_eq_transpose_of_isHermitian hHerm,
    ← Matrix.transpose_mul, hIdem, Matrix.trace_transpose]

end Matrix
