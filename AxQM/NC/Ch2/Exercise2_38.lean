/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.Trace
import ToMathlib.LinearAlgebra.Trace

/-!
# Nielsen & Chuang, Exercise 2.38 (Linearity of the trace)

Show tr(A+B)=tr(A)+tr(B) and tr(zA)=z tr(A) (linearity of trace).

The result is *already present in Mathlib* — the trace, in both its operator and matrix
forms, is packaged there as a genuine `LinearMap`, from which additivity (2.63) and complex
homogeneity (2.64) are the two components `map_add` / `map_smul`. So
nothing new is introduced: the exercise is discharged by the existing
declarations below, which correspond to N&C's notation as explained here.

## The declarations

**Operator form (most faithful to N&C's "linear operators").** In
`Mathlib/LinearAlgebra/Trace.lean`,

* `LinearMap.trace R M : (M →ₗ[R] M) →ₗ[R] R`

is the trace *as an `R`-linear map* from operators `M →ₗ[R] M` to the scalar ring `R`. Being a
`LinearMap`, its structural lemmas give the exercise directly, writing `τ := LinearMap.trace R M`,
for `A B : M →ₗ[R] M` and `z : R`:

* `map_add τ A B : τ (A + B) = τ A + τ B` — this is (2.63);
* `map_smul τ z A : τ (z • A) = z • τ A` — this is (2.64).

N&C's complex case is the instance `R = ℂ`; the Mathlib map is over an arbitrary commutative
(semi)ring `R`, so this is a faithful generalisation, not a weakening.

**Matrix form (the convention used throughout this chapter, e.g. Exercise 2.36).** In
`Mathlib/LinearAlgebra/Matrix/Trace.lean`, for `A B : Matrix n n R` (`n` finite) and a scalar `z`,

* `Matrix.trace_add A B : (A + B).trace = A.trace + B.trace` — (2.63);
* `Matrix.trace_smul z A : (z • A).trace = z • A.trace` — (2.64).

Over `R = ℂ` the scalar action is multiplication (`z • A.trace = z * A.trace`, `smul_eq_mul`), so
`Matrix.trace_smul` reads exactly `tr(zA) = z · tr(A)`. Both facts are likewise bundled there as the
maps `Matrix.traceAddMonoidHom n R : Matrix n n R →+ R` and
`Matrix.traceLinearMap n α R : Matrix n n R →ₗ[α] R`, the matrix-level counterparts of
`LinearMap.trace`.

The operator and matrix forms agree: under a choice of (finite orthonormal) basis, the trace of an
operator is the `Matrix.trace` of its matrix representation, and linearity of the representation map
transports either statement to the other. Either lemma family is the faithful Lean rendering of
N&C's equations (2.63)–(2.64).
-/
