/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Nielsen & Chuang, Exercise 2.30 (Tensor product of two Hermitian operators is Hermitian)

Show the tensor product of two Hermitian operators is Hermitian.

For operators presented as matrices, N&C's *tensor product* is the **Kronecker product** `A ⊗ B`
(the matrix representation of Eq. 2.50, p. 74). An operator is **Hermitian** when it equals its
own adjoint, `A† = A`. Exercise 2.28 established that the adjoint distributes over the tensor
product, `(A ⊗ B)† = A† ⊗ B†` (Eq. 2.53). Hence if `A` and `B` are Hermitian, `A† = A` and
`B† = B`, then `(A ⊗ B)† = A† ⊗ B† = A ⊗ B`, so `A ⊗ B` is Hermitian.

## The declaration

In `ToMathlib/LinearAlgebra/Matrix/Hermitian.lean`:

* `Matrix.IsHermitian.kronecker` — for `A : Matrix m m α` and `B : Matrix n n α` over a type `α`
  with `[CommMagma α] [StarMul α]`, if `A.IsHermitian` and `B.IsHermitian` then
  `(A ⊗ₖ B).IsHermitian`.

It sits alongside the other Hermitian-closure lemmas `Matrix.IsHermitian.add` / `.sub` / `.smul`,
matching the Mathlib convention that the `_.kronecker` closure lemma for a matrix predicate lives
in that predicate's file (cf. `Matrix.IsDiag.kronecker`, `Matrix.PosSemidef.kronecker`,
`Matrix.IsUnit.kronecker`).

## N&C ↦ Mathlib dictionary and fidelity

* The **tensor product of operators** `A ⊗ B` is the Kronecker product
  `A ⊗ₖ B = Matrix.kroneckerMap (· * ·) A B` (`Mathlib/LinearAlgebra/Matrix/Kronecker.lean`),
  whose `(i₁, i₂) (j₁, j₂)` entry is `A i₁ j₁ * B i₂ j₂` — exactly N&C's block form (Eq. 2.50).
  The two factors need not be square of the same size: `A` is `m × m` and `B` is `n × n`, so
  `A ⊗ₖ B` is `(m × n) × (m × n)`.
* **Hermitian** `A† = A` is `Matrix.IsHermitian A`, defined as `Aᴴ = A` with `ᴴ` the conjugate
  transpose. The proof rewrites with `Matrix.conjTranspose_kronecker` (`(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`,
  the formal content of Exercise 2.28) and then the two hypotheses.
* **Generality, not weakening.** N&C's operators are finite complex matrices; the
  statement holds over any `[CommMagma α] [StarMul α]` (of which `ℂ` is an instance), with no
  dimension fixed and no hypothesis beyond Hermiticity of the factors. Commutativity of the
  entries is genuinely required — `star` is an anti-homomorphism, so
  `star (A j₁ i₁ * B j₂ i₂) = star (B j₂ i₂) * star (A j₁ i₁)` matches `Aᴴ ⊗ₖ Bᴴ` only when the
  entries commute — and `ℂ` supplies it. This is a faithful generalisation of the exercise.
-/
