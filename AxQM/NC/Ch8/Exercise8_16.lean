/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.NonTracePreservingBlochExample

/-!
# Nielsen & Chuang, Exercise 8.16 (a non-trace-preserving operation with no affine Bloch picture)

*(N&C p. 378.)*

Find a non-trace-preserving operation not expressible as Bloch deformation+rotation+displacement.

## The answer

For a *trace-preserving* single-qubit operation, N&C (§8.3.2, eq. 8.89) shows the induced action on
the Bloch representation `ρ = ½(I + r·σ)` is an affine map `r ↦ M r + c` — a deformation of the
Bloch sphere along the principal axes of the symmetric factor `S` of `M = O S`, followed by the
proper rotation `O`, followed by the displacement `c` (the pictures of Figures 8.8–8.11). This
affine map is a self-map of the trace-one density matrices, so it can only describe operations that
*preserve the trace*.

The explicit counterexample is the single-Kraus operation

`E(ρ) = P₀ ρ P₀†`,   `P₀ = |0⟩⟨0|`,

a computational-basis projective measurement keeping only the outcome `0`. It is a genuine quantum
operation (an operator sum with one operation element, hence completely positive and
positivity-preserving) but is **not** trace-preserving (`P₀† P₀ = P₀ ≠ I`; equivalently
`tr E(ρ_r) = ½(1 + r₂)`, the outcome-`0` probability, `≠ 1` in general). Because every Bloch matrix
has trace one while `E` sends the pure state `|1⟩⟨1|` (Bloch vector `r = (0, 0, -1)`) to `0` (trace
`0`), no affine `(M, c)` can reproduce `E` on the Bloch sphere.

## The formalisation

The formal content of Exercise 8.16 is pure linear algebra about a `2 × 2` matrix map and the Bloch
matrices (`Matrix`, `Concrete.blochMatrix`, `Matrix.trace`, `Matrix.PosSemidef`). Compare the
operator-sum Exercises 8.4 and 8.12.

The formalisation is in `AxQM/Concrete/NonTracePreservingBlochExample.lean`:

* `AxQM.Concrete.projZero` — the operation element `P₀ = |0⟩⟨0|`.
* `AxQM.Concrete.projZeroOp` — the quantum operation `E(ρ) = P₀ ρ P₀†` (single-Kraus
  operator sum: computational-basis measurement post-selected on outcome `0`).
* `AxQM.Concrete.projZeroOp_posSemidef` — `E` is positivity-preserving (a legitimate
  quantum operation).
* `AxQM.Concrete.projZero_adjoint_mul_self_ne_one` — non-trace-preservation, operator-sum
  form: `∑ Eᵢ† Eᵢ = P₀ ≠ I`.
* `AxQM.Concrete.projZeroOp_blochMatrix_trace` — `tr E(ρ_r) = ½(1 + r₂)`, the outcome-`0`
  probability.
* `AxQM.Concrete.projZeroOp_not_tracePreserving` — non-trace-preservation, physical form:
  `tr E(ρ) = tr ρ` fails for some state.
* `AxQM.Concrete.projZeroOp_not_blochAffine` — **Exercise 8.16 (the answer):** no affine
  map `(M, c)` describes `E` on the Bloch sphere (deformation + rotation + displacement).

See the module docstring of `AxQM/Concrete/NonTracePreservingBlochExample.lean` for the full
argument.
-/
