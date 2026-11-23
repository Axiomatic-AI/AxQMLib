/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.OperatorSumComposition

/-!
# Nielsen & Chuang, Exercise 8.6 (Composition of quantum operations)

*(N&C p. 362.)*

Show composition F∘E of quantum operations is a quantum operation; extend to differing spaces.

## Content

Exercise 8.6 is, at its formal core, a statement of **operator/Hilbert-space linear algebra** about
the operator-sum (Kraus) map `ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` (`ContinuousLinearMap.krausSumₗ`): the composite of
two such maps is again such a map, with operation elements the products `{Fⱼ Eᵢ}`, and the composite
family inherits the trace condition `Σ (Fⱼ Eᵢ)† (Fⱼ Eᵢ) ≤ 1`. Its statement concerns operators
`H →L[ℂ] G`, their adjoints and compositions, and the operator-sum map, over general spaces `H`,
`G`, `K`. Compare its section-8.2 siblings **Theorem 8.2**
(`ContinuousLinearMap.krausSumₗ_eq_iff_exists_mem_unitaryGroup`, in
`ToMathlib/Analysis/InnerProductSpace/OperatorSum.lean`) and **Theorem 8.3**
(`ToMathlib/Analysis/InnerProductSpace/MinimalOperatorSum.lean`).

The extension to differing input/output spaces N&C asks for is not a separate statement: the
operator-sum map `krausSumₗ` already carries independent input and output spaces
(`E : ι → H →L[ℂ] G` sends operators on `H` to operators on `G`), so the general (space-changing)
theorem below subsumes the "same quantum system" case as the specialisation `H = G = K`.

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/OperatorSumComposition.lean`:

* `ContinuousLinearMap.krausSumₗ_comp` — the composite of two operator-sum maps is the operator-sum
  map of the product family: `(krausSumₗ F).comp (krausSumₗ E) = krausSumₗ (fun (j, i) ↦ Fⱼ ∘ Eᵢ)`.
* `ContinuousLinearMap.sum_adjoint_comp_comp_le_one` — the composite family inherits the trace
  condition: `Σᵢ Eᵢ† Eᵢ ≤ 1` and `Σⱼ Fⱼ† Fⱼ ≤ 1` imply `Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) ≤ 1`.
* `ContinuousLinearMap.IsOperatorSum.comp` — **the exercise:** if `Φ` and `Ψ` have operator-sum
  representations (`IsOperatorSum E Φ`, `IsOperatorSum F Ψ`), then the composite `Ψ ∘ Φ` has the
  operator-sum representation given by the product family `{Fⱼ Eᵢ}`.
* `ContinuousLinearMap.IsOperatorSum.comp_satisfiesAxioms` — the physical upshot: the composite is a
  quantum operation, `SatisfiesOperationAxioms (Ψ ∘ Φ)` (via the forward direction of Theorem 8.1,
  `IsOperatorSum.satisfiesAxioms`).
-/
