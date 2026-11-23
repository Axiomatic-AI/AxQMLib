/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Algebra.Star.Commutator

/-!
# Nielsen & Chuang, Exercise 2.47 (`i[A, B]` is Hermitian)

If A,B Hermitian, show i[A,B] is Hermitian.

Here `[A, B] ≡ AB − BA` is the commutator (eq. 2.66) of two operators (§2.1.9), `†` is the adjoint,
and an operator is *Hermitian* (self-adjoint) when it equals its own adjoint. The computation is
`(i[A, B])† = -i [A, B]† = -i ((AB)† − (BA)†) = -i (B†A† − A†B†) = -i (BA − AB) = i (AB − BA)
= i[A, B]`, using `A† = A` and `B† = B`. Structurally: the commutator of two Hermitian operators is
*anti*-Hermitian (`[A, B]† = −[A, B]`), and multiplying an anti-Hermitian operator by `i` restores
Hermiticity.

This is pure star-ring algebra — the antisymmetric part `AB − BA` of a product of two
self-adjoint elements is skew-adjoint, and a skew-adjoint scalar times a skew-adjoint element is
self-adjoint.

Compare the commutator exercises 2.42, 2.44 and 2.46.

## The formalisation

Both are in `ToMathlib/Algebra/Star/Commutator.lean`:

* `IsSelfAdjoint.commutator_mem_skewAdjoint` — the structural core: the commutator of two
  self-adjoint elements of a star ring is skew-adjoint, `⁅A, B⁆ ∈ skewAdjoint R`. This is
  `[A, B]† = −[A, B]` (the commutator of two Hermitian operators is anti-Hermitian).
* `isSelfAdjoint_smul_commutator` — the exercise's conclusion shape: scaling `⁅A, B⁆` by a
  skew-adjoint scalar `s` gives a self-adjoint element, `IsSelfAdjoint (s • ⁅A, B⁆)`. It is
  `isSelfAdjoint_smul_of_mem_skewAdjoint` (skew-adjoint scalar · skew-adjoint element ⇒
  self-adjoint, already in `Mathlib/Algebra/Star/SelfAdjoint.lean`) applied to the commutator lemma
  above.

## N&C ↦ Mathlib dictionary and the `i` instantiation

* An **operator** `A` on a complex Hilbert space is an element of a star ring — concretely
  `Matrix n n ℂ` or `End ℂ V` — with **product** `AB` the ring multiplication and **adjoint** `A†`
  the `star`. N&C's **commutator** `[A, B] = AB − BA` (eq. 2.66) is Mathlib's ring Lie bracket
  `⁅A, B⁆` (`Ring.lie_def`). "`A` is **Hermitian**" is `IsSelfAdjoint A` (`star A = A`).
* The exercise's `i[A, B]` is the scalar `Complex.I` acting on `⁅A, B⁆`. Since
  `conj I = -I` (`Complex.conj_I`), the imaginary unit satisfies `Complex.I ∈ skewAdjoint ℂ`, so
  `isSelfAdjoint_smul_commutator Complex.conj_I hA hB : IsSelfAdjoint (Complex.I • ⁅A, B⁆)` is
  exactly "`i[A, B]` is Hermitian". Any star ring `R` that is also a `Module ℂ R` with
  `StarModule ℂ R` — in particular `Matrix n n ℂ` and the bounded/continuous endomorphisms of a
  complex Hilbert space — is a valid instance.
* **Generality, not weakening.** `commutator_mem_skewAdjoint` holds in *any* star ring
  (`NonUnitalNonAssocRing R` + `StarRing R`), and `isSelfAdjoint_smul_commutator` for *any*
  skew-adjoint scalar over *any* star module — no dimension fixed and no hypothesis beyond `A`, `B`
  self-adjoint. `Complex.I` is one skew-adjoint scalar among many, so the statements are a
  faithful generalisation of the exercise, never a specialisation of it. Following the sibling
  `Exercise2_42` (`mul_eq_invOf_two_smul_lie_add_anticommutator`), generalising the scalar keeps the
  result in the general-algebra layer without a dependency on `ℂ`, while the `Complex.I` instance
  above recovers N&C's statement verbatim.
-/
