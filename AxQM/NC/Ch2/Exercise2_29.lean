/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.TensorProduct
import ToMathlib.LinearAlgebra.UnitaryGroup

/-!
# Nielsen & Chuang, Exercise 2.29 (Tensor product of unitary operators)

Show the tensor product of two unitary operators is unitary.

For operators `A` on `V` and `B` on `W`, the **tensor product** `A ⊗ B` is the operator
on `V ⊗ W` acting by `(A ⊗ B)(|v⟩ ⊗ |w⟩) = A|v⟩ ⊗ B|w⟩` (N&C §2.1.7), whose matrix
representation is the **Kronecker product** of the matrices of `A` and `B` (eq. 2.52). An
operator `A` is **unitary** when `A† A = I` (N&C §2.1.6). The claim is that if `A` and `B`
are unitary then so is `A ⊗ B`, because — using `(A ⊗ B)† = A† ⊗ B†` (Exercise 2.28) and
`(A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD)` —
`(A ⊗ B)† (A ⊗ B) = (A† ⊗ B†)(A ⊗ B) = (A† A) ⊗ (B† B) = I ⊗ I = I`.

The result is already present in `ToMathlib/`: the exercise is discharged by the
existing declarations below, whose correspondence with N&C's notation is recorded here.

## The declarations

Two faithful renderings, matching N&C's own operator / matrix duality (an operator and its
Kronecker matrix representation):

* **Operator level.** `TensorProduct.mapL_mem_unitary`, in
  `ToMathlib/Analysis/InnerProductSpace/TensorProduct.lean`, states — for continuous linear
  operators `f : E →L[𝕜] E` and `g : F →L[𝕜] F` on finite-dimensional inner-product spaces
  `E`, `F` over `𝕜` (`RCLike 𝕜`) — that if `f ∈ unitary (E →L[𝕜] E)` and
  `g ∈ unitary (F →L[𝕜] F)` then `mapL f g ∈ unitary (E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F)`. The
  operator `TensorProduct.mapL f g`, acting by `(mapL f g)(x ⊗ y) = f x ⊗ g y`, is exactly
  N&C's `f ⊗ g`; and `unitary (E →L[𝕜] E)` unfolds (`unitary.mem_iff`) to
  `star f * f = 1 ∧ f * star f = 1`, i.e. `f† f = I` and `f f† = I` (`star` is the adjoint,
  `*` composition, `1` the identity) — N&C's unitarity. Its proof is precisely the algebra
  above: `mapL_adjoint` (Exercise 2.28), `mapL_mul`, and `mapL_one`.

* **Matrix level.** `Matrix.kronecker_mem_unitary`, in
  `Mathlib/LinearAlgebra/UnitaryGroup.lean`, states — for `U₁ : Matrix n n R`,
  `U₂ : Matrix m m R` over a star ring `R` — that if `U₁ ∈ unitary (Matrix n n R)` and
  `U₂ ∈ unitary (Matrix m m R)` then `U₁ ⊗ₖ U₂ ∈ unitary (Matrix (n × m) (n × m) R)`. Here
  `U₁ ⊗ₖ U₂` (`Matrix.kroneckerMap (· * ·)`) is N&C's Kronecker product (eq. 2.52), and
  `unitary (Matrix n n R)` unfolds to `star U * U = 1 ∧ U * star U = 1` with `star U = Uᴴ`,
  i.e. N&C's `U† U = I` (and `U U† = I`). This is the matrix representation of the operator
  statement above.

## Fidelity

N&C work with finite-dimensional complex Hilbert spaces `V`, `W`. The operator lemma is
over any finite-dimensional inner-product space over `𝕜 = ℝ` or `ℂ`, recovering N&C's case
as `E = V`, `F = W`, `𝕜 = ℂ` (finite dimensionality supplies the completeness Mathlib
requires); the matrix lemma holds over an arbitrary star ring `R`, recovering N&C's
`R = ℂ`. Both are faithful generalisations, not weakenings: the only hypotheses are "both
factors unitary", with no dimension or commutativity restriction added. N&C's defining
`U† U = I` is delivered in full — `unitary` bundles both `U† U = I` and `U U† = I`, which in
finite dimensions are equivalent.
-/
