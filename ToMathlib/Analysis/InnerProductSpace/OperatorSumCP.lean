/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import Mathlib.LinearAlgebra.Contraction
public import ToMathlib.Analysis.InnerProductSpace.Positive
-- `TensorProduct` is re-imported LAST on purpose: it re-asserts the inner-product-space
-- normed structure on `E ⊗[𝕜] F` as the resolution-priority `AddCommMonoid`/`Module` instance
-- over the bare algebraic `TensorProduct.instModule`. Without this, a tensor operator built with
-- `homTensorHomEquiv`/`TensorProduct.map` (algebraic module) fails to unify with the normed module
-- that `ContinuousLinearMap`/`LinearMap.IsPositive` require, even though the two are defeq.
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Complete positivity and the forward direction of the operator-sum theorem

The **ampliation** of a superoperator `Φ` (a linear map on operators) by a reference space `R` is
the map `id_{B(R)} ⊗ Φ` acting on operators of `R ⊗ H`, characterised by
`(id_{B(R)} ⊗ Φ)(B ⊗ M) = B ⊗ Φ(M)`. A superoperator is **completely positive** when every such
ampliation preserves positivity — Nielsen–Chuang's axiom **A3** (*Quantum Computation and Quantum
Information*, §8.2.4). This file introduces the ampliation and complete positivity for operators on
finite-dimensional inner product spaces, packages the three N&C axioms into
`SatisfiesOperationAxioms`, and proves the **forward direction of the operator-sum representation
theorem (N&C Theorem 8.1)**: an operator-sum (Kraus) map `krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` with
`Σᵢ Eᵢ† Eᵢ ≤ 1` satisfies axioms A1, A2, A3.

## Main definitions

* `ContinuousLinearMap.superopAmpliationₗ R Φ` — the **ampliation** `id_{B(R)} ⊗ Φ` of a
  `LinearMap`-superoperator `Φ : (H →ₗ[𝕜] H) →ₗ[𝕜] (G →ₗ[𝕜] G)`, built from `homTensorHomEquiv`
  and `LinearMap.lTensor`. Its defining property is `superopAmpliationₗ_map`. (The `ₗ` subscript
  marks the bundled-`LinearMap` form, matching `krausSumₗ`.)
* `ContinuousLinearMap.toLMSuperop Φ` — a `ContinuousLinearMap`-superoperator
  `Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)` reinterpreted on the underlying linear maps, so that its
  ampliation and complete positivity are expressible.
* `ContinuousLinearMap.IsCompletelyPositive Φ` — **complete positivity** (N&C axiom A3): for every
  finite-dimensional reference space `R`, the ampliation `id_{B(R)} ⊗ Φ` sends positive operators
  on `R ⊗ H` to positive operators on `R ⊗ G`.
* `ContinuousLinearMap.IsTraceNonIncreasing Φ` — **axiom A1**: `re tr(Φ ρ) ≤ re tr ρ` for every
  positive `ρ` (the scaling-invariant form of `tr[Φ ρ] ≤ 1` on states).
* `ContinuousLinearMap.SatisfiesOperationAxioms Φ` — the **three axioms A1, A2, A3** bundled:
  completely positive and trace-non-increasing (A2 is subsumed by `Φ` being a linear map).
* `ContinuousLinearMap.IsOperatorSum E Φ` — `Φ` has the **operator-sum form** `Φ = krausSumₗ E`
  with `Σᵢ Eᵢ† Eᵢ ≤ 1` (the right-hand side of Theorem 8.1).

## Main results

* `ContinuousLinearMap.superopAmpliationₗ_map` — the ampliation acts on product operators by
  `(id_{B(R)} ⊗ Φ)(B ⊗ M) = B ⊗ Φ(M)`.
* `ContinuousLinearMap.superopAmpliationₗ_krausSumₗ` — the ampliation of the operator-sum map is the
  finite sum of conjugations by the ampliated Kraus operators,
  `(id_{B(R)} ⊗ krausSumₗ E)(A) = Σᵢ (1_R ⊗ Eᵢ) A (1_R ⊗ Eᵢ)†` (N&C eqs 8.51–8.53).
* `ContinuousLinearMap.krausSumₗ_isCompletelyPositive` — the operator-sum map `krausSumₗ E` is
  completely positive (axiom A3). Each ampliated summand `(1_R ⊗ Eᵢ) A (1_R ⊗ Eᵢ)†` is positive for
  positive `A` (`krausSumₗ_isPositive` on the ampliated Kraus operators `1_R ⊗ Eᵢ`), so the sum is
  too.
* `ContinuousLinearMap.IsOperatorSum.satisfiesAxioms` — **N&C Theorem 8.1, forward direction
  (`⇐`):** a superoperator with an operator-sum representation `IsOperatorSum E Φ` satisfies the
  operation axioms `SatisfiesOperationAxioms Φ`, combining `krausSumₗ_isCompletelyPositive` (A3) and
  `krausSumₗ_isTraceNonIncreasing` (A1, from `re_trace_krausSumₗ_le`).

## Relation to `CompletelyPositiveMap`

Mathlib already has complete positivity for C*-algebras — `CompletelyPositiveMap` /
`CompletelyPositiveMapClass`, defined by entrywise positivity of the `CStarMatrix (Fin k) (Fin k)`
(i.e. `M_k`) ampliations — and `H →L[ℂ] H` is a `CStarAlgebra`
(`instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace`), so
`CompletelyPositiveMap (H →L[ℂ] H) (G →L[ℂ] G)` is type-applicable. `IsCompletelyPositive` here is
the *same notion* in a different encoding: the reference-Hilbert-space tensor ampliation
`id_{B(R)} ⊗ Φ` in place of the `M_k`-matrix ampliation. The tensor form is used deliberately —
(i) it is Nielsen–Chuang's axiom A3 verbatim (a reference system `R` of arbitrary dimension), and
(ii) the reverse direction of Theorem 8.1 forms the Choi operator `σ = (id_R ⊗ Φ)(|α⟩⟨α|)` on a
maximally entangled state, which lives in exactly this reference-tensor ampliation and not the
matrix one. A bridge `IsCompletelyPositive Φ ↔ CompletelyPositiveMapClass …` — the standard
equivalence of the two CP characterisations — is not formalised here; it is not needed
for Theorem 8.1.

## Implementation notes

The complete-positivity predicate quantifies over reference spaces `R : Type` (universe `0`). This
is not a weakening of N&C's "reference system of arbitrary dimension": complete positivity depends
only on the *dimension* of the reference, every finite dimension is realised by a space in `Type 0`
(e.g. `EuclideanSpace 𝕜 (Fin n)`), and positivity is preserved under isometric isomorphism.

Positivity of operators on `R ⊗ G` is stated with `LinearMap.IsPositive` on the underlying linear
maps (equivalently `ContinuousLinearMap.IsPositive`, by `isPositive_toLinearMap_iff`).

The general ampliation, its computation rule, and the complete-positivity predicate are stated over
a general `RCLike` field `𝕜`; the operator-sum results specialise to `ℂ` (inherited from
`krausSumₗ`).
-/

open scoped TensorProduct
open ContinuousLinearMap

noncomputable section

@[expose] public section

namespace ContinuousLinearMap

section General

variable {𝕜 H G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] [CompleteSpace G]

/-- A **`ContinuousLinearMap`-superoperator** `Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)` reinterpreted as a
`LinearMap`-superoperator on the underlying linear maps, via the finite-dimensional identification
`LinearMap.toContinuousLinearMap`. This is the form on which the ampliation `superopAmpliationₗ`
(hence complete positivity) is stated. -/
def toLMSuperop (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : (H →ₗ[𝕜] H) →ₗ[𝕜] (G →ₗ[𝕜] G) :=
  (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := G)).symm.toLinearMap ∘ₗ Φ ∘ₗ
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := H)).toLinearMap

omit [CompleteSpace H] [CompleteSpace G] in
@[simp]
theorem toLMSuperop_apply (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) (M : H →ₗ[𝕜] H) :
    toLMSuperop Φ M = (Φ (LinearMap.toContinuousLinearMap M) : G →ₗ[𝕜] G) := rfl

/-- The **ampliation** `id_{B(R)} ⊗ Φ` of a `LinearMap`-superoperator `Φ` by a reference space `R`:
the linear map on operators sending `A : R ⊗ H →ₗ[𝕜] R ⊗ H` to the operator on `R ⊗ G` that applies
`Φ` to the `H`-factor while leaving the `R`-factor untouched. Built from the operator–tensor
identification `homTensorHomEquiv` and `LinearMap.lTensor`; its characterising action on product
operators is `superopAmpliationₗ_map`. The `ₗ` subscript marks the bundled-`LinearMap` form. -/
def superopAmpliationₗ (R : Type*) [NormedAddCommGroup R] [InnerProductSpace 𝕜 R]
    [FiniteDimensional 𝕜 R]
    (Φ : (H →ₗ[𝕜] H) →ₗ[𝕜] (G →ₗ[𝕜] G)) :
    (R ⊗[𝕜] H →ₗ[𝕜] R ⊗[𝕜] H) →ₗ[𝕜] (R ⊗[𝕜] G →ₗ[𝕜] R ⊗[𝕜] G) :=
  (homTensorHomEquiv 𝕜 R G R G).toLinearMap ∘ₗ
    (LinearMap.lTensor (R →ₗ[𝕜] R) Φ) ∘ₗ
    (homTensorHomEquiv 𝕜 R H R H).symm.toLinearMap

omit [CompleteSpace H] [CompleteSpace G] in
/-- **The ampliation acts on product operators factor-wise:** `(id_{B(R)} ⊗ Φ)(B ⊗ M) = B ⊗ Φ(M)`.
This is the defining property that pins down `superopAmpliationₗ`. -/
theorem superopAmpliationₗ_map (R : Type*) [NormedAddCommGroup R] [InnerProductSpace 𝕜 R]
    [FiniteDimensional 𝕜 R]
    (Φ : (H →ₗ[𝕜] H) →ₗ[𝕜] (G →ₗ[𝕜] G)) (B : R →ₗ[𝕜] R) (M : H →ₗ[𝕜] H) :
    superopAmpliationₗ R Φ (TensorProduct.map B M) = TensorProduct.map B (Φ M) := by
  have hrw : TensorProduct.map B M = homTensorHomEquiv 𝕜 R H R H (B ⊗ₜ[𝕜] M) := by
    rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
  simp only [superopAmpliationₗ, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hrw, (homTensorHomEquiv 𝕜 R H R H).symm_apply_apply, LinearMap.lTensor_tmul,
    homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]

/-- **Complete positivity of a superoperator `Φ` (Nielsen–Chuang axiom A3).** For every
finite-dimensional reference space `R`, the ampliation `id_{B(R)} ⊗ Φ` sends positive
operators on `R ⊗ H` to positive operators on `R ⊗ G`. (The reference ranges over `Type 0`; see the
module implementation notes on why this captures "arbitrary dimension".) -/
def IsCompletelyPositive (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : Prop :=
  ∀ (R : Type) [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
    (A : R ⊗[𝕜] H →ₗ[𝕜] R ⊗[𝕜] H), A.IsPositive →
      (superopAmpliationₗ R (toLMSuperop Φ) A).IsPositive

/-- **Trace-non-increasing — Nielsen–Chuang axiom A1.** A superoperator `Φ` is
*trace-non-increasing* when `re tr(Φ ρ) ≤ re tr ρ` for every positive operator `ρ`. For a state
`ρ` (trace one), this reads `tr[Φ ρ] ≤ 1`; the scaling-invariant form over all positive `ρ` is
equivalent and is exactly N&C's requirement that `tr[E(ρ)]` be a probability, `0 ≤ tr[E(ρ)] ≤ 1`
(the lower bound `0 ≤ re tr(Φ ρ)` being a consequence of positivity, hence of axiom A3). The trace
is taken via the underlying `LinearMap`; positivity makes it real, so `RCLike.re` extracts its
value. -/
def IsTraceNonIncreasing (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : Prop :=
  ∀ ρ : H →L[𝕜] H, 0 ≤ ρ →
    RCLike.re (LinearMap.trace 𝕜 G ((Φ ρ : G →L[𝕜] G) : G →ₗ[𝕜] G))
      ≤ RCLike.re (LinearMap.trace 𝕜 H ((ρ : H →L[𝕜] H) : H →ₗ[𝕜] H))

/-- **A quantum operation (the Nielsen–Chuang axioms A1, A2, A3).** A superoperator `Φ` satisfies
the operation axioms when it is completely positive (axiom A3, `IsCompletelyPositive`) and
trace-non-increasing (axiom A1, `IsTraceNonIncreasing`). Axiom A2 (convex-linearity on density
operators) is *subsumed by the type*: `Φ` is modelled as a genuine `𝕜`-linear map on operators, the
unique linear extension of a convex-linear map on density operators (which spans the operator
space), so linearity — hence convex-linearity — holds by construction. This bundled predicate is
the left-hand side of the operator-sum representation theorem (N&C Theorem 8.1). -/
def SatisfiesOperationAxioms (Φ : (H →L[𝕜] H) →ₗ[𝕜] (G →L[𝕜] G)) : Prop :=
  IsCompletelyPositive Φ ∧ IsTraceNonIncreasing Φ

end General

section Complex

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **The ampliation of the operator-sum map is the sum of conjugations by the ampliated Kraus
operators** (N&C eqs 8.51–8.53). For the operator-sum map `krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†`, the
ampliation `id_{B(R)} ⊗ krausSumₗ E` applied to `A : R ⊗ H →ₗ[ℂ] R ⊗ H` equals
`Σᵢ (1_R ⊗ Eᵢ) A (1_R ⊗ Eᵢ)†`. Proved by reducing to product operators `B ⊗ M` (via
`homTensorHomEquiv` and `TensorProduct.induction_on`), where it follows from
`superopAmpliationₗ_map` and bilinearity of the tensor. -/
theorem superopAmpliationₗ_krausSumₗ (R : Type*) [NormedAddCommGroup R] [InnerProductSpace ℂ R]
    [FiniteDimensional ℂ R] [CompleteSpace R] {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G)
    (A : R ⊗[ℂ] H →ₗ[ℂ] R ⊗[ℂ] H) :
    superopAmpliationₗ R (toLMSuperop (krausSumₗ E)) A
      = ∑ i, (TensorProduct.map LinearMap.id (↑(E i) : H →ₗ[ℂ] G)) ∘ₗ A ∘ₗ
          (TensorProduct.map LinearMap.id (↑(adjoint (E i)) : G →ₗ[ℂ] H)) := by
  obtain ⟨X, rfl⟩ := (homTensorHomEquiv ℂ R H R H).surjective A
  induction X using TensorProduct.inductionOn with
  | tmul B M =>
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply, superopAmpliationₗ_map]
      simp only [toLMSuperop_apply, krausSumₗ_apply, ContinuousLinearMap.toLinearMap_sum,
        ]
      rw [← TensorProduct.mapBilinear_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.mapBilinear_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
      simp
  | add X Y ihX ihY =>
      simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, Finset.sum_add_distrib, ihX, ihY]

/-- **The operator-sum (Kraus) map is completely positive** — Nielsen–Chuang Theorem 8.1, forward
direction (axiom A3). For any finite family `E : ι → (H →L[ℂ] G)`, the operator-sum map
`krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` is completely positive: for a positive operator `A` on `R ⊗ H`, the
ampliation `Σᵢ (1_R ⊗ Eᵢ) A (1_R ⊗ Eᵢ)†` is a finite sum of the positive operators
`(1_R ⊗ Eᵢ) A (1_R ⊗ Eᵢ)†` — the operator-sum map of the ampliated Kraus operators `1_R ⊗ Eᵢ`
applied to `A` — hence positive (`krausSumₗ_isPositive`). -/
theorem krausSumₗ_isCompletelyPositive {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G) :
    IsCompletelyPositive (krausSumₗ E) := by
  intro R _ _ _ A hA
  have : CompleteSpace R := FiniteDimensional.completeSpace ℂ R
  rw [superopAmpliationₗ_krausSumₗ]
  -- Recast the ampliated sum `Σᵢ (1_R ⊗ Eᵢ) A (1_R ⊗ Eᵢ)†` as the operator-sum map of the
  -- ampliated Kraus operators `1_R ⊗ Eᵢ` applied to `A`; positivity is `krausSumₗ_isPositive`.
  have hadj1 : ContinuousLinearMap.adjoint (1 : R →L[ℂ] R) = 1 := by
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]
  have key : (∑ i, TensorProduct.map LinearMap.id (↑(E i) : H →ₗ[ℂ] G) ∘ₗ A ∘ₗ
        TensorProduct.map LinearMap.id (↑(adjoint (E i)) : G →ₗ[ℂ] H))
      = (krausSumₗ (fun i => TensorProduct.mapL (1 : R →L[ℂ] R) (E i))
          (LinearMap.toContinuousLinearMap A)).toLinearMap := by
    rw [krausSumₗ_apply, ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (TensorProduct.map LinearMap.id (↑(E i) : H →ₗ[ℂ] G))
        = (TensorProduct.mapL (1 : R →L[ℂ] R) (E i)).toLinearMap := by
      rw [TensorProduct.toLinearMap_mapL, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id]
    have e2 : (TensorProduct.map LinearMap.id (↑(adjoint (E i)) : G →ₗ[ℂ] H))
        = (ContinuousLinearMap.adjoint (TensorProduct.mapL (1 : R →L[ℂ] R) (E i))).toLinearMap := by
      rw [TensorProduct.adjoint_mapL, hadj1, TensorProduct.toLinearMap_mapL,
        ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id]
    rw [e1, e2, ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.coe_toContinuousLinearMap]
  rw [key]
  refine (krausSumₗ_isPositive _ ?_).toLinearMap
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, LinearMap.coe_toContinuousLinearMap]
  exact hA

/-- **An operator-sum (Kraus) representation of a superoperator `Φ`.** A family of operation
elements `E : ι → H →L[ℂ] G` represents `Φ` when `Φ` *is* the operator-sum map of `E`,
`Φ = krausSumₗ E` (i.e. `Φ ρ = Σᵢ Eᵢ ρ Eᵢ†` for all `ρ`), and the operation elements obey the trace
condition `Σᵢ Eᵢ† Eᵢ ≤ 1`. This is the right-hand side of the operator-sum representation theorem
(N&C Theorem 8.1): `Φ` satisfies the operation axioms iff some finite family `E` gives
`IsOperatorSum E Φ`. -/
def IsOperatorSum {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G)
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)) : Prop :=
  Φ = krausSumₗ E ∧ ∑ i, adjoint (E i) ∘L E i ≤ 1

/-- **The operator-sum map is trace-non-increasing (axiom A1)** under the trace condition
`Σᵢ Eᵢ† Eᵢ ≤ 1`. Immediate from `re_trace_krausSumₗ_le`. -/
theorem krausSumₗ_isTraceNonIncreasing {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G)
    (hE : ∑ i, adjoint (E i) ∘L E i ≤ 1) :
    IsTraceNonIncreasing (krausSumₗ E) :=
  fun _ hρ => re_trace_krausSumₗ_le E hρ hE

/-- **The operator-sum map satisfies the operation axioms (N&C Theorem 8.1, forward direction).**
Under the trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`, the map `krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` is completely
positive (axiom A3, `krausSumₗ_isCompletelyPositive`) and trace-non-increasing (axiom A1,
`krausSumₗ_isTraceNonIncreasing`); axiom A2 holds as `krausSumₗ E` is a linear map. -/
theorem krausSumₗ_satisfiesOperationAxioms {ι : Type*} [Fintype ι] (E : ι → H →L[ℂ] G)
    (hE : ∑ i, adjoint (E i) ∘L E i ≤ 1) :
    SatisfiesOperationAxioms (krausSumₗ E) :=
  ⟨krausSumₗ_isCompletelyPositive E, krausSumₗ_isTraceNonIncreasing E hE⟩

/-- **Theorem 8.1, forward direction (`⇐`): an operator-sum map is a quantum operation.** If a
superoperator `Φ` has an operator-sum representation `IsOperatorSum E Φ` — i.e. `Φ = krausSumₗ E`
with `Σᵢ Eᵢ† Eᵢ ≤ 1` — then `Φ` satisfies the operation axioms A1, A2, A3
(`SatisfiesOperationAxioms`). Rewriting `Φ` as `krausSumₗ E`, this is
`krausSumₗ_satisfiesOperationAxioms`. -/
theorem IsOperatorSum.satisfiesAxioms {ι : Type*} [Fintype ι] {E : ι → H →L[ℂ] G}
    {Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)} (h : IsOperatorSum E Φ) :
    SatisfiesOperationAxioms Φ := by
  obtain ⟨hΦ, hE⟩ := h
  rw [hΦ]
  exact krausSumₗ_satisfiesOperationAxioms E hE

end Complex

end ContinuousLinearMap
