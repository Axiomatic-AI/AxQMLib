/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CHSH

/-!
# Nielsen & Chuang, Problem 2.3 (Tsirelson's inequality)

Tsirelson's inequality: (Q⊗S+R⊗S+R⊗T-Q⊗T)^2 = 4I+[Q,R]⊗[S,T]; bound 2sqrt2.

## What this file contains

`pauliObservable_chsh_expectation_le` below is **(2.234)**: the statement
that for unit vectors `q⃗, r⃗, s⃗, t⃗` and *any* pure state `ψ` of the two-qubit system, the CHSH
combination of expectation values `⟪Q⊗S⟫ + ⟪R⊗S⟫ + ⟪R⊗T⟫ - ⟪Q⊗T⟫` is at most `2√2`. It is
stated with `PureState.expectation`, `Observable.tmul` (`⊗`) and `pauliObservable`, and is
proved by applying `PureState.expectation_chsh_tmul_le`.

## Equation (2.233) and the proof

The operator identity **(2.233)** is a statement about operators (it squares the operator
`Q⊗S + R⊗S + R⊗T - Q⊗T` and names the commutator/tensor structure `[Q,R]⊗[S,T]`), so it is stated
with `Observable.op` and the tensor-product map `TensorProduct.mapL`. It is
`chsh_tmul_sq` in `AxQM/Postulates/API/CHSH.lean`, in its *general* form: for
any involutive observables `A₀, A₁` on one factor and `B₀, B₁` on the other,
`(A₀⊗B₀ + A₀⊗B₁ + A₁⊗B₀ - A₁⊗B₁)² = 4·I + ⁅A₁,A₀⁆ ⊗ ⁅B₀,B₁⁆` — N&C's (2.233) under the
dictionary `A₀=R, A₁=Q, B₀=S, B₁=T`, with the two-qubit Pauli case obtained by discharging the
involution hypotheses via `Concrete.pauliDot`'s `(n⃗·σ⃗)² = I` (`pauliObservable_op_mul_self`).

The supporting infrastructure (also in `AxQM/Postulates/API/`): `pauliObservable` (the observable
`n⃗·σ⃗` on the qubit), `Observable.tmul` and the operator-order → expectation bridge,
and the algebraic CHSH squaring identity `CHSH_sq` (`ToMathlib.Algebra.Star.CHSH`) and
`tsirelson_inequality` (`Mathlib.Algebra.Star.CHSH`).

**Proof route for (2.234).** N&C suggests deriving (2.234) *from* (2.233) (the square is
`4I + [Q,R]⊗[S,T] ≼ 8I`, so the operator is `≼ 2√2 · I`). We instead descend Mathlib's
`tsirelson_inequality` — whose algebraic sum-of-squares proof gives the operator bound
`Q⊗S + R⊗S + R⊗T - Q⊗T ≤ √2³ · I` directly — through the operator-order → expectation bridge.
Both routes prove the same statement honestly; (2.233) is formalised on its own as `chsh_tmul_sq`.
-/

open scoped InnerProductSpace

namespace AxQM

/-- **Nielsen & Chuang (2.234): Tsirelson's bound on the CHSH quantity.** For real unit vectors
`q⃗, r⃗, s⃗, t⃗` — giving the two-qubit Pauli observables `Q = q⃗·σ⃗`, `R = r⃗·σ⃗`, `S = s⃗·σ⃗`,
`T = t⃗·σ⃗` — and any pure state `ψ` of the two-qubit system,
`⟪Q⊗S⟫_ψ + ⟪R⊗S⟫_ψ + ⟪R⊗T⟫_ψ - ⟪Q⊗T⟫_ψ ≤ 2√2`.

Since the classical (local-hidden-variable) CHSH bound is `2` and `2√2 > 2`, this shows the
quantum violation is bounded — the value `2√2` is the maximum possible in quantum mechanics.

Proved by `PureState.expectation_chsh_tmul_le`
(dictionary `A₀=R, A₁=Q, B₀=S, B₁=T`), whose four involution hypotheses are supplied by
`pauliObservable_op_mul_self`; the terms are reassociated to N&C's order by `linarith`. -/
theorem pauliObservable_chsh_expectation_le (ψ : PureState (qubit ⊗ qubit))
    {q r s t : Fin 3 → ℝ}
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 = 1) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1)
    (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1) (ht : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 = 1) :
    ψ.expectation (pauliObservable q ⊗ pauliObservable s)
      + ψ.expectation (pauliObservable r ⊗ pauliObservable s)
      + ψ.expectation (pauliObservable r ⊗ pauliObservable t)
      - ψ.expectation (pauliObservable q ⊗ pauliObservable t) ≤ 2 * Real.sqrt 2 := by
  have h := ψ.expectation_chsh_tmul_le (pauliObservable r) (pauliObservable q)
    (pauliObservable s) (pauliObservable t)
    (pauliObservable_op_mul_self hr) (pauliObservable_op_mul_self hq)
    (pauliObservable_op_mul_self hs) (pauliObservable_op_mul_self ht)
  linarith

end AxQM
