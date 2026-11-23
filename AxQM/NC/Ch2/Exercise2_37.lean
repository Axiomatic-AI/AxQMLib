/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Trace
import ToMathlib.LinearAlgebra.Matrix.Trace

/-!
# Nielsen & Chuang, Exercise 2.37 (Cyclic property of the trace)

Show tr(AB) = tr(BA) (cyclic property of trace).

For linear operators `A`, `B` on a (finite-dimensional) space, the trace of a product is
unchanged when the factors are commuted. Written out over an orthonormal basis (N&C's defining
formula `tr(C) = Σᵢ ⟨i|C|i⟩`, Eq. 2.60), this is the double-sum rearrangement
`tr(AB) = Σᵢ Σⱼ Aᵢⱼ Bⱼᵢ = Σⱼ Σᵢ Bⱼᵢ Aᵢⱼ = tr(BA)`, i.e. Fubini for a finite double sum together
with commutativity of the scalar product. It is the workhorse behind the trace's basis
independence (`tr(U A U⁻¹) = tr(A)`) and, in Chapter 2, behind `tr(A|ψ⟩⟨ψ|) = ⟨ψ|A|ψ⟩` (Eq. 2.61).

The statement is pure linear algebra about the trace of a product of operators/matrices — a
finite double-sum reindexing.

Like Exercises 2.25 and 2.29, this result was already present in Mathlib.

## The formalisation

The result already exists in Mathlib in two complementary forms — the operator form matching
N&C's "linear operators" phrasing, and the matrix form matching a fixed-basis representation:

* `LinearMap.trace_mul_comm` (`Mathlib/LinearAlgebra/Trace.lean`) — the **operator form**, the
  direct rendering of the exercise: for endomorphisms `f g : M →ₗ[R] M` of an `R`-module `M`,
  `LinearMap.trace R M (f * g) = LinearMap.trace R M (g * f)` (here `*` is composition). This is
  exactly "`A`, `B` linear operators ⇒ `tr(AB) = tr(BA)`".
* `Matrix.trace_mul_comm` (`Mathlib/LinearAlgebra/Matrix/Trace.lean`) — the **matrix face**: for
  `A : Matrix m n R` and `B : Matrix n m R`, `(A * B).trace = (B * A).trace`. In a fixed
  orthonormal basis an operator is its matrix and the trace is the sum of diagonal entries, so
  this is the same exercise at the matrix level.
* `Matrix.trace_mul_cycle` (`Mathlib/LinearAlgebra/Matrix/Trace.lean`) — the **general cyclic
  form** `(A * B * C).trace = (C * A * B).trace`, the three-factor cyclic permutation from which
  the two-factor statement follows by taking the middle factor to be the identity: with `B = 1`,
  `(A * 1 * C).trace = (C * A * 1).trace` reduces to `(A * C).trace = (C * A).trace`. This is the
  "cyclic property" the exercise's title names in full generality.

## N&C ↦ Mathlib dictionary and fidelity

* A **linear operator** `A` on a space `V` is an endomorphism `A : V →ₗ[R] V`; the **trace**
  `tr(A)` is `LinearMap.trace R V A`, the basis-independent trace of an endomorphism (which for a
  finite free module agrees with N&C's `Σᵢ ⟨i|A|i⟩`). Operator **product** `AB` is composition,
  written multiplicatively `f * g` on `Module.End R V`.
* **Generality, not weakening.** N&C's operators are finite complex matrices / endomorphisms of a
  finite-dimensional complex Hilbert space; `LinearMap.trace_mul_comm` holds for endomorphisms of
  *any* module over *any* commutative semiring `R` (of which `ℂ`-vector spaces are an instance),
  with no dimension fixed and no hypothesis beyond `A`, `B` being operators on the same space.
  The matrix form is more general still: `A` may be `m × n` and `B` may be `n × m` (rectangular,
  possibly non-square), whereas N&C tacitly takes both square on the same space — so both
  statements are faithful generalisations of the exercise, never specialisations of it.
  Commutativity of the scalars (`CommSemiring R` / `CommMagma R`) is genuinely used: the diagonal
  of `AB` is `Σⱼ Aᵢⱼ Bⱼᵢ` and matching it against that of `BA` needs `Aᵢⱼ Bⱼᵢ = Bⱼᵢ Aᵢⱼ`, and `ℂ`
  supplies it.
-/
