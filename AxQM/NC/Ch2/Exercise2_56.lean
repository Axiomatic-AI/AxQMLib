/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.CStarAlgebra.Unitary.Exp

/-!
# Nielsen & Chuang, Exercise 2.56

Show K=-i log(U) is Hermitian for any unitary U, so U=exp(iK).

The formalisation is in `ToMathlib/Analysis/CStarAlgebra/Unitary/Exp.lean`, working in the
C⋆-algebra
`CStarMatrix n n ℂ` of `n × n` complex matrices under the operator norm. The exercise's
`K = -i log U` is Mathlib's `Unitary.argSelfAdjoint U = cfc Complex.arg U`, and `U = exp (i K)` is
`selfAdjoint.expUnitary K = exp (i • K)` (`selfAdjoint.expUnitary_coe`), where a selfadjoint matrix
is a Hermitian one:

* `expUnitary_argSelfAdjoint_of_continuousOn_arg` — the general C⋆-algebra engine: dropping the
  `‖u - 1‖ < 2` hypothesis of `expUnitary_argSelfAdjoint` down to its sole used consequence,
  continuity of `Complex.arg` on `spectrum ℂ u`.
* `CStarMatrix.finite_spectrum` — a square C⋆-matrix has finite spectrum (so `arg` is continuous on
  it, unconditionally).
* `CStarMatrix.expUnitary_argSelfAdjoint` — `exp (i • argSelfAdjoint u) = u` for every unitary
  matrix `u`, i.e. `U = exp(i · (-i log U))`.
* `CStarMatrix.expUnitary_surjective`, `CStarMatrix.exists_expUnitary_eq_of_mem_unitary` — the
  exercise: every unitary matrix is `exp (i K)` for some Hermitian `K`.

**Fidelity note.** N&C's suggested route diagonalises the *normal* operator `U` and reads off real
phases `θⱼ` with `λⱼ = e^{i θⱼ}`. The continuous functional calculus `Unitary.argSelfAdjoint`
packages exactly this spectral construction (`K = arg U` acts as `θⱼ` on each spectral projection),
so the statement proved — `U = exp(i K)` with `K` Hermitian — is the exercise's conclusion at full
generality (all `n`, all unitary `U`, including `-1 ∈ spectrum`).
-/
