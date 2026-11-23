/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# The partial trace is invariant under a local operator-sum channel on the traced factor

For finite-dim inner product spaces `E`, `F` over `RCLike 𝕜`, an orthonormal basis `b` on the
traced-out factor `F`, and a finite family of operators `M, N : κ → F →ₗ[𝕜] F` on that factor
satisfying the completeness relation `∑ᵢ Nᵢ ∘ₗ Mᵢ = 1`, tracing out `F` is unchanged by conjugating
by the local operator sum:

  `Tr_F(∑ᵢ (1_E ⊗ Mᵢ) T (1_E ⊗ Nᵢ)) = Tr_F(T)`.

Taking `Nᵢ = Mᵢ†`, the completeness relation is `∑ᵢ Mᵢ† Mᵢ = 1` — the hypothesis that
`ρ ↦ ∑ᵢ (1 ⊗ Mᵢ) ρ (1 ⊗ Mᵢ†)` is a trace-preserving quantum channel acting on the second factor
— and the identity says a **non-selective measurement (or any trace-preserving operation) on one
subsystem does not affect the reduced state of the other subsystem** (Nielsen–Chuang §2.4,
Exercise 4.32; the general no-signalling content). It is the operator-sum generalization of
`LinearMap.partialTraceRight_conjIsometry` (a *single* unitary/isometry conjugation `1 ⊗ U`): a full
Kraus channel with several operation elements, tied together by the completeness relation.

## Main results

* `LinearMap.trace_tensorMap_id_comp_sum_conj_map_id` — the trace-pairing form: for every `V` on the
  kept factor `E`, `tr((V ⊗ 1)(∑ᵢ (1 ⊗ Mᵢ) T (1 ⊗ Nᵢ))) = tr((V ⊗ 1) T)`.
* `LinearMap.partialTraceRight_sum_conj_map_id` — the marginal is preserved:
  `Tr_F(∑ᵢ (1 ⊗ Mᵢ) T (1 ⊗ Nᵢ)) = Tr_F(T)`.

## Implementation notes

The trace-pairing lemma is pure cyclicity: `(V ⊗ 1)(1 ⊗ Mᵢ) = V ⊗ Mᵢ` and, after rotating
`1 ⊗ Nᵢ` to the front, `(1 ⊗ Nᵢ)(V ⊗ Mᵢ) = V ⊗ (Nᵢ Mᵢ)` (`TensorProduct.map_comp` +
`LinearMap.trace_comp_comm'`), so summing collapses the `F`-factor to `∑ᵢ Nᵢ Mᵢ = 1`. The operator
identity then follows from the trace-pairing lemma by the non-degeneracy of the Hilbert–Schmidt
pairing (`LinearMap.eq_zero_of_trace_adjoint_comp_self_eq_zero`) applied to the difference of the
two marginals, exactly as in `LinearMap.partialTraceRight_eq_of_basis`, via the partial-trace
duality `LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι₂ : Type*} [Fintype ι₂] {κ : Type*} [Fintype κ]

/-- **Trace-pairing invariance under a local operator sum on the traced factor.** For any `V` on the
kept factor `E`, operators `M, N : κ → F →ₗ[𝕜] F` on the traced factor with `∑ᵢ Nᵢ ∘ₗ Mᵢ = 1`, and
any `T : E ⊗ F →ₗ E ⊗ F`,

  `tr((V ⊗ 1) ∑ᵢ (1 ⊗ Mᵢ) T (1 ⊗ Nᵢ)) = tr((V ⊗ 1) T)`.

Per summand: `(V ⊗ 1)(1 ⊗ Mᵢ) = V ⊗ Mᵢ` (`TensorProduct.map_comp`); rotating `1 ⊗ Nᵢ` cyclically to
the front (`trace_comp_comm'`) and combining `(1 ⊗ Nᵢ)(V ⊗ Mᵢ) = V ⊗ (Nᵢ Mᵢ)` reduces the summand
to `tr((V ⊗ Nᵢ Mᵢ) T)`; summing pulls the `F`-factor to `∑ᵢ Nᵢ Mᵢ = 1`. -/
theorem trace_tensorMap_id_comp_sum_conj_map_id (V : E →ₗ[𝕜] E) (M N : κ → F →ₗ[𝕜] F)
    (hMN : ∑ i, N i ∘ₗ M i = (LinearMap.id : F →ₗ[𝕜] F))
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    LinearMap.trace 𝕜 _ (TensorProduct.map V LinearMap.id ∘ₗ
        ∑ i, TensorProduct.map LinearMap.id (M i) ∘ₗ T ∘ₗ TensorProduct.map LinearMap.id (N i))
      = LinearMap.trace 𝕜 _ (TensorProduct.map V LinearMap.id ∘ₗ T) := by
  have hcs : TensorProduct.map V LinearMap.id ∘ₗ
        (∑ i, TensorProduct.map LinearMap.id (M i) ∘ₗ T ∘ₗ TensorProduct.map LinearMap.id (N i))
      = ∑ i, TensorProduct.map V LinearMap.id ∘ₗ
        (TensorProduct.map LinearMap.id (M i) ∘ₗ T ∘ₗ TensorProduct.map LinearMap.id (N i)) := by
    ext x; simp [LinearMap.sum_apply, map_sum]
  have hsc : (∑ i, TensorProduct.map V (N i ∘ₗ M i)) ∘ₗ T
      = ∑ i, TensorProduct.map V (N i ∘ₗ M i) ∘ₗ T := by
    ext x; simp [LinearMap.sum_apply]
  have hmapsum : (∑ i, TensorProduct.map V (N i ∘ₗ M i))
      = TensorProduct.map V (∑ i, N i ∘ₗ M i) := by
    refine TensorProduct.ext' fun u v => ?_
    simp [TensorProduct.map_tmul, LinearMap.sum_apply, TensorProduct.tmul_sum]
  calc LinearMap.trace 𝕜 _ (TensorProduct.map V LinearMap.id ∘ₗ
          ∑ i, TensorProduct.map LinearMap.id (M i) ∘ₗ T ∘ₗ TensorProduct.map LinearMap.id (N i))
      = ∑ i, LinearMap.trace 𝕜 _ (TensorProduct.map V LinearMap.id ∘ₗ
          (TensorProduct.map LinearMap.id (M i) ∘ₗ T ∘ₗ TensorProduct.map LinearMap.id (N i))) := by
        rw [hcs, map_sum]
    _ = ∑ i, LinearMap.trace 𝕜 _ (TensorProduct.map V (N i ∘ₗ M i) ∘ₗ T) :=
        Finset.sum_congr rfl fun i _ => by
          have h1 : TensorProduct.map V LinearMap.id ∘ₗ TensorProduct.map LinearMap.id (M i)
              = TensorProduct.map V (M i) := by
            rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
          have h2 : TensorProduct.map LinearMap.id (N i) ∘ₗ TensorProduct.map V (M i)
              = TensorProduct.map V (N i ∘ₗ M i) := by
            rw [← TensorProduct.map_comp, LinearMap.id_comp]
          simp only [← LinearMap.comp_assoc]
          rw [h1, LinearMap.trace_comp_comm' (TensorProduct.map LinearMap.id (N i))
            (TensorProduct.map V (M i) ∘ₗ T), ← LinearMap.comp_assoc, h2]
    _ = LinearMap.trace 𝕜 _ ((∑ i, TensorProduct.map V (N i ∘ₗ M i)) ∘ₗ T) := by
        rw [hsc, map_sum]
    _ = LinearMap.trace 𝕜 _ (TensorProduct.map V LinearMap.id ∘ₗ T) := by
        rw [hmapsum, hMN]

/-- **The right partial trace is invariant under a local operator-sum channel on the traced
factor.** For operators `M, N : κ → F →ₗ[𝕜] F` on the traced factor `F` with the completeness
relation
`∑ᵢ Nᵢ ∘ₗ Mᵢ = 1`, and any `T : E ⊗ F →ₗ E ⊗ F`,

  `Tr_F(∑ᵢ (1_E ⊗ Mᵢ) T (1_E ⊗ Nᵢ)) = Tr_F(T)`.

With `Nᵢ = Mᵢ†` (so `∑ᵢ Mᵢ† Mᵢ = 1`), this says a trace-preserving operation on the traced-out
subsystem leaves the marginal on the kept subsystem unchanged — the operator-sum generalization of
`partialTraceRight_conjIsometry` (single-unitary case). The proof mirrors
`partialTraceRight_eq_of_basis`: the difference `Δ` of the two marginals has `tr(Δ† ∘ Δ) = 0` by the
trace-pairing invariance `trace_tensorMap_id_comp_sum_conj_map_id` (at `V = Δ†`) combined with the
partial-trace duality, so `Δ = 0` by non-degeneracy of the Hilbert–Schmidt pairing. -/
theorem partialTraceRight_sum_conj_map_id (b : OrthonormalBasis ι₂ 𝕜 F) (M N : κ → F →ₗ[𝕜] F)
    (hMN : ∑ i, N i ∘ₗ M i = (LinearMap.id : F →ₗ[𝕜] F))
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRight b (∑ i, TensorProduct.map LinearMap.id (M i) ∘ₗ T ∘ₗ
        TensorProduct.map LinearMap.id (N i)) = partialTraceRight b T := by
  refine sub_eq_zero.mp <| eq_zero_of_trace_adjoint_comp_self_eq_zero _ ?_
  rw [LinearMap.comp_sub, map_sub, sub_eq_zero,
    (trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight b _ _).symm,
    (trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight b _ T).symm]
  exact trace_tensorMap_id_comp_sum_conj_map_id _ M N hMN T

end LinearMap
