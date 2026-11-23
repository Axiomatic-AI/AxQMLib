/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.OperatorSumComplement

/-!
# Nielsen & Chuang, Exercise 8.8 (Non-trace-preserving quantum operations)

*(N&C p. 365.)*

Explain construction of unitary for system-environment model of a non-trace-preserving operation.

## Content

Exercise 8.8 is, at its formal core, a statement of **operator/Hilbert-space linear algebra**. In
the preceding text N&C shows that a *trace-preserving* family `{Eₖ}` (`Σₖ Eₖ† Eₖ = I`) assembles
into an isometry `V ψ = Σₖ Eₖ ψ ⊗ eₖ` that extends to a unitary system–environment model
(Eqs. (8.36)–(8.41), formalised in `ToMathlib/Analysis/InnerProductSpace/OperatorSumDilation.lean`).
This exercise handles a *non-trace-preserving* family,
`Σₖ Eₖ† Eₖ ≤ I`: the
construction is repaired by **adjoining one extra operation element** `E∞ = √(I − Σₖ Eₖ† Eₖ)` (the
operator square root of the positive defect), so that the augmented family is complete
(`Σₖ Eₖ† Eₖ = I` including `k = ∞`) and the trace-preserving construction applies; the original
operation is recovered by post-selecting the environment off the `∞` outcome.

Its statement concerns operators `H →L[ℂ] H` / `H →ₗ[ℂ] H`, their adjoints, the CFC operator square
root `cfc Real.sqrt`, the Loewner order `Σₖ Eₖ† Eₖ ≤ 1`, the partial trace, and orthonormal-basis
rank-one projectors, over a *general* finite-dimensional complex space `H`. Compare **Theorem 8.2**,
**Theorem 8.3**, **Exercise 8.6** and the trace-preserving construction **Exercise 8.8 (1/2)** in
`ToMathlib/Analysis/InnerProductSpace/OperatorSumDilation.lean`.

## The formalisation

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/OperatorSumComplement.lean`.

For a family `E : ι → H →L[ℂ] H` of operation elements of a non-trace-preserving operation
(`∑ₖ Eₖ† Eₖ ≤ 1`):

* `ContinuousLinearMap.krausComplement E` — **the extra operation element** `E∞`, defined as the CFC
  operator square root `cfc Real.sqrt (1 − ∑ₖ Eₖ† Eₖ)` of the positive defect.
* `ContinuousLinearMap.adjoint_krausComplement_comp_self` — `E∞† E∞ = 1 − ∑ₖ Eₖ† Eₖ`.
* `ContinuousLinearMap.krausAugment E` — the augmented family (`Option ι → H →L[ℂ] H`), `Eₖ`
  together with `E∞`.
* `ContinuousLinearMap.sum_adjoint_krausAugment_comp_self` — **the exercise's answer:** the
  augmented family is complete, `∑ⱼ Fⱼ† Fⱼ = 1`, i.e. N&C's `∑ₖ Eₖ† Eₖ = I` *including* `k = ∞`.
* `LinearMap.krausComplementProj` — the environment post-selection projector
  `P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)` (N&C's projector `P` of Eq. (8.36)).
* `LinearMap.partialTraceRight_krausComplementProj_conj` — the recovery identity
  **(N&C Eq. (8.36))**: `tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = ∑ₖ Eₖ ρ Eₖ†`, for any `U` intertwining with
  the augmented dilation.
* `LinearMap.exists_unitary_proj_krausComplement` — **the model:** there is a **unitary** `U` on the
  joint space `H ⊗ F` with `tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = ∑ₖ Eₖ ρ Eₖ†` for all `ρ`, obtained by
  applying the trace-preserving construction (`LinearMap.exists_unitary_krausDilation`) to the
  completed family and post-selecting off the `∞` outcome.

See the module docstring of `ToMathlib/Analysis/InnerProductSpace/OperatorSumComplement.lean` for
the full argument (the `Option ι` augmented index and the CFC/Loewner-order machinery).
-/
