/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.LiebConcavityTrace

/-!
# Nielsen & Chuang, Theorem 11.11 (Lieb's theorem)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.11, p. 520.

Lieb's theorem: f(A,B)=tr(X† A^t X B^(1-t)) is jointly concave in positive matrices A,B.

Here "jointly concave" is N&C's eq. (11.96): `f` is jointly concave when
`f(λ A₁ + (1-λ) A₂, λ B₁ + (1-λ) B₂) ≥ λ f(A₁, B₁) + (1-λ) f(A₂, B₂)` for all `0 ≤ λ ≤ 1`.
Lieb's theorem is the deep matrix-analysis input to N&C's proof of the joint convexity of the
relative entropy (Theorem 11.12) and, through it, strong subadditivity (Theorem 11.14); N&C defers
its proof to Appendix 6 (the self-contained development follows Carlen, *Trace Inequalities and
Quantum Entropy*, §6.1).

Lieb's concavity theorem is a statement of pure matrix analysis: the joint concavity of a trace
functional of fractional operator powers. Its formalisation is in `ToMathlib/`, alongside the
general Lieb development it specialises.

## Formalisation

The full Lieb development lives in `ToMathlib/Analysis/InnerProductSpace/`. Operators are modelled
as continuous linear maps on finite-dimensional complex inner product spaces, `X = K` a linear map
`EuclideanSpace ℂ ι →L[ℂ] E` (an `n`-column, `m`-row matrix), `A : E →L[ℂ] E` and
`B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι` the positive operators, `Aᵗ`/`B¹⁻ᵗ` the operator
`rpow` (continuous functional calculus), and `f(A,B) = re Tr(K† Aᵗ K B¹⁻ᵗ)`. In N&C's convention
"positive matrix" means positive **semidefinite** (`0 ≤ ·`); the formalisation states the theorem at
that full generality.

**Theorem 11.11 itself** — the single-parameter `(t, 1-t)` form, for positive semidefinite `A`, `B`
exactly as N&C states — is, in `ToMathlib/Analysis/InnerProductSpace/LiebConcavityTrace.lean`:

* `TensorProduct.concaveAt_trace_one_sub_isPositive` — **Theorem 11.11**: for `t ∈ [0,1]` and
  positive semidefinite `A₁, A₂, B₁, B₂` (`0 ≤ ·`, N&C's "positive matrices"), `f(A,B)` satisfies
  the joint-concavity inequality (11.96) verbatim
  (`a • f(A₁,B₁) + b • f(A₂,B₂) ≤ f(a•A₁+b•A₂, a•B₁+b•B₂)`, `a,b ≥ 0`, `a+b=1`).
* `TensorProduct.concaveOn_trace_one_sub_isPositive` — the same result bundled as the idiomatic
  `ConcaveOn ℝ` predicate over the (convex) product of the two positive-semidefinite cones: "`f` is
  jointly concave" as a single statement about the function.

These are specialisations, at the exponent pair `(t, 1-t)` on the upper edge `q + r = 1` of the Lieb
simplex, of the general two-exponent positive-semidefinite form, also in that file:

* `TensorProduct.concaveAt_trace_isPositive` — Lieb's Theorem 1, trace form, for positive
  semidefinite operators: joint concavity of `(A,B) ↦ re Tr(K† A^q K B^r)` for every `(q, r)` in the
  Lieb simplex `0 ≤ q, 0 ≤ r, q + r ≤ 1` (a strict generalisation of N&C's `r = 1 - t`).

**The strictly-positive engine and the boundary of the cone.** N&C's own Appendix 6 proof (Lemma
A6.2) proves the invertible case in full and remarks that the singular (non-invertible) case needs
only "minor technical modifications … left as an exercise"; the formalisation follows suit. The
engine is the strictly-positive (positive-definite, `IsStrictlyPositive`) form,

* `TensorProduct.concaveAt_trace` / `concaveAt_trace_one_sub` / `concaveOn_trace_one_sub`,

built through the Choi–Jamiołkowski bridge from the operator-level Lieb T1
`ContinuousLinearMap.LiebTensor.concaveAt_of_mem_simplex` (in `LiebConcavityRpow.lean`). The
positive-semidefinite statements above then discharge N&C's "left as an exercise" singular case by
the standard regularization limit `A, B ⤳ A + εI, B + εI`, `ε → 0⁺`
(`CFC.tendsto_rpow_add_smul_one` — continuity of the operator `rpow` along the regularizing path —
plus `tendsto_reTrace_comp` and `le_of_tendsto_of_tendsto`), recovering the full statement over the
closed positive cone. This is the same perturbation-and-limit device by which the rest of the
Chapter-11 entropy development removes its faithfulness hypotheses (e.g.
`AxQM.State.vonNeumannEntropy_add_le_add'`).
-/
