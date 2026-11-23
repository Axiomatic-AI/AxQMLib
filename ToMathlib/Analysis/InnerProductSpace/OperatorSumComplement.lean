/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# System–environment models for non-trace-preserving operations (N&C Exercise 8.8)

`OperatorSumDilation.lean` builds the **converse** system–environment construction for a
*trace-preserving* operation: given a **complete** Kraus family `{Eₖ}` (`Σₖ Eₖ† Eₖ = 1`), assemble
the dilation `V ψ = Σₖ Eₖ ψ ⊗ eₖ`, which is an isometry and hence extends to a unitary `U` on the
joint space, realising `ρ ↦ Σₖ Eₖ ρ Eₖ†` (Nielsen–Chuang Eqs. (8.36)–(8.41)).

This file supplies the **non-trace-preserving** case — Nielsen–Chuang **Exercise 8.8**: a family of
operation elements `E : ι → H →L H` for a *non-trace-preserving* operation satisfies only the
sub-completeness relation `Σₖ Eₖ† Eₖ ≤ 1`, so `V` is *not* an isometry and does not extend to a
unitary directly. The exercise's fix is to **introduce one extra operation element** `E∞`, chosen so
that the *augmented* family `{Eₖ} ∪ {E∞}` is complete:

  `Σₖ Eₖ† Eₖ + E∞† E∞ = 1`   (N&C's `Σₖ Eₖ† Eₖ = 1` including `k = ∞`).

The unique positive such `E∞` is the operator square root of the "defect" `1 − Σₖ Eₖ† Eₖ` (a
positive operator, since `Σₖ Eₖ† Eₖ ≤ 1`). The completed family is trace preserving, so the
trace-preserving construction applies and produces a unitary `U`; the *original*
non-trace-preserving operation `ρ ↦ Σₖ Eₖ ρ Eₖ†` is then recovered by **projecting the environment
off the `∞` outcome** after the interaction, `E(ρ) = tr_F(P U(ρ ⊗ |ω⟩⟨ω|) U† P)` with
`P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)` (N&C Eq. (8.36), post-selecting on the environment not landing in `e∞`).

## Main definitions and results

* `ContinuousLinearMap.krausComplement E` — the extra operation element
  `E∞ = √(1 − Σₖ Eₖ† Eₖ)`, the CFC square root of the defect.
* `ContinuousLinearMap.adjoint_krausComplement_comp_self` — `E∞† E∞ = 1 − Σₖ Eₖ† Eₖ`.
* `ContinuousLinearMap.krausAugment E` — the augmented family `Option ι → H →L H`
  (`some k ↦ Eₖ`, `none ↦ E∞`).
* `ContinuousLinearMap.sum_adjoint_krausAugment_comp_self` — **the exercise's answer:** the
  augmented family is complete, `Σⱼ Fⱼ† Fⱼ = 1` (`Σₖ Eₖ† Eₖ = 1` including `k = ∞`).
* `LinearMap.krausComplementProj b` — the environment post-selection projector
  `P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)` (N&C's projector `P` of Eq. (8.36), with `e∞ = b none`).
* `LinearMap.partialTraceRight_krausComplementProj_conj` — the recovery identity **(N&C
  Eq. (8.36))**: for a joint map `U` with `U(ψ ⊗ ω) = V ψ` (the augmented dilation), projecting off
  `e∞` and discarding the environment returns the *original* operation,
  `tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = Σₖ Eₖ ρ Eₖ†`.
* `LinearMap.exists_unitary_proj_krausComplement` — **the model:** for any non-trace-preserving
  family (`Σₖ Eₖ† Eₖ ≤ 1`) and unit environment state `ω`, there is a **unitary** `U` on the joint
  space with `tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = Σₖ Eₖ ρ Eₖ†` for all `ρ`.

## Design notes

Following the governing plan decision, the extra element `E∞` and the completeness relation are
stated at `ContinuousLinearMap` (`→L`), because both the operator square root (`cfc Real.sqrt`) and
the Loewner order `Σₖ Eₖ† Eₖ ≤ 1` — matching the trace condition of a non-trace-preserving
operation — live there (`H →L[ℂ] H` is a `StarOrderedRing` on the Loewner order, `StarOrder.lean`).
The dilation-side results reuse `OperatorSumDilation.lean`, which is stated at `LinearMap` (`→ₗ`) to
plug into the existing `krausOp` infrastructure; the `→ₗ`/`→L` seam is bridged by `toLinearMap` in
finite dimensions. The augmented index is `Option ι` (`some k ↦ Eₖ`, `none ↦ E∞`), the canonical
"adjoin one distinguished `∞` element" shape, so completeness sums split via `Fintype.sum_option`.

Like the rest of §8.2's operator-sum development, the content is operator/Hilbert-space linear
algebra over `H →L[ℂ] H` / `H →ₗ[ℂ] H`. The statement of Exercise 8.8 is in
`AxQM/NC/Ch8/Exercise8_8.lean`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (System–environment models; Box 8.1; Exercise 8.8).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] {ι : Type*} [Fintype ι]

/-- **The extra operation element `E∞` of Nielsen–Chuang Exercise 8.8.** For a family
`E : ι → H →L H` of operation elements of a *non-trace-preserving* operation
(`Σₖ Eₖ† Eₖ ≤ 1`), the defect `1 − Σₖ Eₖ† Eₖ` is a positive operator; `krausComplement E` is its
operator square root `E∞ = √(1 − Σₖ Eₖ† Eₖ)` (via the continuous functional calculus). Adjoining it
to `{Eₖ}` produces a *complete* family (`sum_adjoint_krausAugment_comp_self`). -/
noncomputable def krausComplement (E : ι → H →L[ℂ] H) : H →L[ℂ] H :=
  cfc Real.sqrt (1 - ∑ k, adjoint (E k) ∘L E k)

omit [FiniteDimensional ℂ H] in
/-- **The extra element completes the trace condition** (Nielsen–Chuang Exercise 8.8): for a
non-trace-preserving family (`Σₖ Eₖ† Eₖ ≤ 1`), the extra element `E∞ = krausComplement E` satisfies
`E∞† E∞ = 1 − Σₖ Eₖ† Eₖ`. Because the defect `1 − Σₖ Eₖ† Eₖ` is positive, its CFC square root `E∞`
is self-adjoint (`cfc_predicate`) with `E∞ * E∞ = 1 − Σₖ Eₖ† Eₖ`
(`cfc_real_sqrt_mul_self_of_nonneg`). -/
theorem adjoint_krausComplement_comp_self (E : ι → H →L[ℂ] H)
    (hE : ∑ k, adjoint (E k) ∘L E k ≤ 1) :
    adjoint (krausComplement E) ∘L krausComplement E = 1 - ∑ k, adjoint (E k) ∘L E k := by
  have hsa : IsSelfAdjoint (krausComplement E) := cfc_predicate Real.sqrt _
  rw [hsa.adjoint_eq]
  exact cfc_real_sqrt_mul_self_of_nonneg (sub_nonneg.mpr hE)

/-- **The augmented family** of Nielsen–Chuang Exercise 8.8: `{Eₖ}` together with the extra element
`E∞`, indexed by `Option ι` (`some k ↦ Eₖ`, `none ↦ E∞ = krausComplement E`). It is a *complete*
Kraus family (`sum_adjoint_krausAugment_comp_self`), so the trace-preserving system–environment
construction of `OperatorSumDilation.lean` applies to it. -/
noncomputable def krausAugment (E : ι → H →L[ℂ] H) : Option ι → H →L[ℂ] H :=
  fun j => j.elim (krausComplement E) E

omit [FiniteDimensional ℂ H] in
/-- **The augmented family is complete — the answer to Nielsen–Chuang Exercise 8.8.** Adjoining the
extra element `E∞ = krausComplement E` to a non-trace-preserving family `{Eₖ}` (`Σₖ Eₖ† Eₖ ≤ 1`)
yields the completeness relation

  `Σⱼ Fⱼ† Fⱼ = 1`   (over `j : Option ι`),

i.e. N&C's `Σₖ Eₖ† Eₖ = 1` where the sum ranges over the complete set of `k` *including* `k = ∞`.
Splitting the sum over `Option ι` with `Fintype.sum_option`, the `none` term is
`E∞† E∞ = 1 − Σₖ Eₖ† Eₖ` (`adjoint_krausComplement_comp_self`) and the `some` terms are
`Σₖ Eₖ† Eₖ`, which add to `1`. -/
theorem sum_adjoint_krausAugment_comp_self (E : ι → H →L[ℂ] H)
    (hE : ∑ k, adjoint (E k) ∘L E k ≤ 1) :
    ∑ j : Option ι, adjoint (krausAugment E j) ∘L krausAugment E j = 1 := by
  rw [Fintype.sum_option]
  simp only [krausAugment, Option.elim]
  rw [adjoint_krausComplement_comp_self E hE]
  abel

end ContinuousLinearMap

namespace LinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [CompleteSpace F]

omit [FiniteDimensional ℂ H] [CompleteSpace H] [FiniteDimensional ℂ F] [CompleteSpace F] in
/-- **The environment post-selection projector of Nielsen–Chuang Eq. (8.36)** for Exercise 8.8:
`P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)`, the orthogonal projector onto the subspace where the environment is
*not* in the extra state `e∞ = b none`. Post-selecting the joint state onto `P` after the
system–environment interaction discards exactly the `∞`-outcome term, recovering the original
non-trace-preserving operation (`partialTraceRight_krausComplementProj_conj`). -/
noncomputable def krausComplementProj (b : OrthonormalBasis (Option ι) ℂ F) :
    (H ⊗[ℂ] F) →ₗ[ℂ] (H ⊗[ℂ] F) :=
  TensorProduct.map LinearMap.id
    ((LinearMap.id : F →ₗ[ℂ] F) - (InnerProductSpace.rankOne ℂ (b none) (b none)).toLinearMap)

omit [CompleteSpace H] in
set_option linter.unusedSectionVars false in
-- The proof needs `[CompleteSpace F]` to form the adjoint, though the final term does not mention
-- it.
/-- The environment post-selection projector `P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)` is self-adjoint: both
tensor factors are self-adjoint (the identity, and the rank-one projector complement
`1 − |e∞⟩⟨e∞|`). -/
theorem adjoint_krausComplementProj (b : OrthonormalBasis (Option ι) ℂ F) :
    LinearMap.adjoint (krausComplementProj b)
      = (krausComplementProj b : (H ⊗[ℂ] F) →ₗ[ℂ] (H ⊗[ℂ] F)) := by
  rw [← LinearMap.isSelfAdjoint_iff', krausComplementProj]
  refine IsSelfAdjoint.tensorMap (LinearMap.isSelfAdjoint_iff'.mpr LinearMap.adjoint_id) ?_
  refine LinearMap.isSelfAdjoint_iff'.mpr ?_
  rw [map_sub, LinearMap.adjoint_id, ContinuousLinearMap.adjoint_toLinearMap,
    InnerProductSpace.adjoint_rankOne]

omit [FiniteDimensional ℂ H] [CompleteSpace H] [FiniteDimensional ℂ F] [CompleteSpace F] in
/-- Contracting a *kept* environment basis vector `b (some k)` (`k ≠ ∞`) against the post-selection
projector `P` leaves the contraction unchanged: `⟨b (some k)| P = ⟨b (some k)|`. The projector acts
as the identity on `e∞`'s orthogonal complement, which contains every `b (some k)`. -/
theorem restrictRight_comp_krausComplementProj_some (b : OrthonormalBasis (Option ι) ℂ F) (k : ι) :
    (restrictRight b (some k) : H ⊗[ℂ] F →ₗ[ℂ] H) ∘ₗ krausComplementProj b
      = restrictRight b (some k) := by
  classical
  apply TensorProduct.ext'
  intro x y
  simp only [krausComplementProj, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    restrictRight_tmul, inner_sub_right, inner_smul_right, b.inner_eq_ite]
  simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] [FiniteDimensional ℂ F] [CompleteSpace F] in
/-- Contracting the *removed* environment basis vector `b none = e∞` against the post-selection
projector `P` annihilates it: `⟨e∞| P = 0`. The projector `1_H ⊗ (1 − |e∞⟩⟨e∞|)` kills the `e∞`
component, which is exactly the `∞`-outcome that post-selection discards. -/
theorem restrictRight_comp_krausComplementProj_none (b : OrthonormalBasis (Option ι) ℂ F) :
    (restrictRight b (none : Option ι) : H ⊗[ℂ] F →ₗ[ℂ] H) ∘ₗ krausComplementProj b = 0 := by
  classical
  apply TensorProduct.ext'
  intro x y
  simp only [krausComplementProj, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    restrictRight_tmul, inner_sub_right, inner_smul_right, b.inner_eq_ite]
  simp

/-- **The system–environment model recovers the non-trace-preserving operation** (Nielsen–Chuang
Eq. (8.36), Exercise 8.8). If a joint map `U` intertwines the ancilla embedding with the dilation of
the *augmented* family — `U (ψ ⊗ ω) = Σⱼ Fⱼ ψ ⊗ eⱼ` — then post-selecting the environment onto the
projector `P = krausComplementProj b` (dropping the `∞` outcome `e∞ = b none`) and discarding the
environment returns the *original* operator sum over `ι` alone:

  `tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = Σₖ Eₖ ρ Eₖ†`.

Folding `P · U(ρ ⊗ |ω⟩⟨ω|)U† · P` into `(P ∘ U) (ρ ⊗ |ω⟩⟨ω|) (P ∘ U)†` (using `P† = P`,
`adjoint_krausComplementProj`) and applying the environment-model recovery
`partialTraceRight_conj_map_rankOne_eq_sum_krausOp`, the operation elements of `P ∘ U` are
`⟨eⱼ| P V`; the projector turns these into `Eₖ` on the kept indices `j = some k`
(`restrictRight_comp_krausComplementProj_some` + `krausOp_krausDilation`) and into `0` on the
removed index `j = none` (`restrictRight_comp_krausComplementProj_none`), so only the
`Σₖ Eₖ ρ Eₖ†` terms survive. -/
theorem partialTraceRight_krausComplementProj_conj (b : OrthonormalBasis (Option ι) ℂ F)
    (E : ι → H →L[ℂ] H) (U : (H ⊗[ℂ] F) →ₗ[ℂ] (H ⊗[ℂ] F)) {ω : F}
    (hU : U ∘ₗ tmulRightVec ω
      = krausDilation b (fun j => (ContinuousLinearMap.krausAugment E j).toLinearMap))
    (ρ : H →ₗ[ℂ] H) :
    partialTraceRight b (krausComplementProj b ∘ₗ
        (U ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne ℂ ω ω).toLinearMap ∘ₗ adjoint U)
        ∘ₗ krausComplementProj b)
      = ∑ k, (E k : H →ₗ[ℂ] H) ∘ₗ ρ ∘ₗ LinearMap.adjoint ((E k : H →ₗ[ℂ] H)) := by
  have hfold : krausComplementProj b ∘ₗ
      (U ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne ℂ ω ω).toLinearMap ∘ₗ adjoint U)
        ∘ₗ krausComplementProj b
      = (krausComplementProj b ∘ₗ U) ∘ₗ
          TensorProduct.map ρ (InnerProductSpace.rankOne ℂ ω ω).toLinearMap
          ∘ₗ adjoint (krausComplementProj b ∘ₗ U) := by
    rw [LinearMap.adjoint_comp, adjoint_krausComplementProj]
    simp only [LinearMap.comp_assoc]
  have hW : (krausComplementProj b ∘ₗ U) ∘ₗ tmulRightVec ω
      = krausComplementProj b
        ∘ₗ krausDilation b (fun j => (ContinuousLinearMap.krausAugment E j).toLinearMap) := by
    rw [LinearMap.comp_assoc, hU]
  have hkrausE : ∀ k, krausOp b ((krausComplementProj b ∘ₗ U) ∘ₗ tmulRightVec ω) (some k)
      = (E k : H →ₗ[ℂ] H) := by
    intro k
    rw [krausOp, hW, ← LinearMap.comp_assoc, restrictRight_comp_krausComplementProj_some]
    exact krausOp_krausDilation b _ (some k)
  have hkraus0 : krausOp b ((krausComplementProj b ∘ₗ U) ∘ₗ tmulRightVec ω) none = 0 := by
    rw [krausOp, hW, ← LinearMap.comp_assoc, restrictRight_comp_krausComplementProj_none,
      LinearMap.zero_comp]
  rw [hfold, partialTraceRight_conj_map_rankOne_eq_sum_krausOp, Fintype.sum_option, hkraus0]
  simp only [map_zero, LinearMap.comp_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hkrausE k]

/-- **A unitary system–environment model for a non-trace-preserving operation** (Nielsen–Chuang
Exercise 8.8, Eq. (8.36)). Given a family `E : ι → H →L H` of operation elements for a
*non-trace-preserving* operation (`Σₖ Eₖ† Eₖ ≤ 1`), an environment `F` with an orthonormal basis
indexed by `Option ι` (dimension one more than the number of operation elements — the extra
dimension is `e∞`), and a **unit** environment state `ω`, there is a **unitary** `U` on the joint
space `H ⊗ F` such that post-selecting the environment onto `P = 1_H ⊗ (1 − |e∞⟩⟨e∞|)` and
discarding it recovers the operation:

  `tr_F(P (U (ρ ⊗ |ω⟩⟨ω|) U†) P) = Σₖ Eₖ ρ Eₖ†`   for all `ρ`.

This is the construction the exercise asks for: adjoin the extra element `E∞ = krausComplement E`,
so the augmented family is complete (`sum_adjoint_krausAugment_comp_self`); apply the
trace-preserving converse `exists_unitary_krausDilation` to that complete family to obtain the
unitary `U`; then the projector `P` post-selects on the environment avoiding `e∞`, discarding the
`E∞` term and leaving the original operation (`partialTraceRight_krausComplementProj_conj`). -/
theorem exists_unitary_proj_krausComplement (b : OrthonormalBasis (Option ι) ℂ F)
    (E : ι → H →L[ℂ] H) (hE : ∑ k, ContinuousLinearMap.adjoint (E k) ∘L E k ≤ 1)
    {ω : F} (hω : ‖ω‖ = 1) :
    ∃ U : (H ⊗[ℂ] F) ≃ₗᵢ[ℂ] (H ⊗[ℂ] F),
      ∀ ρ : H →ₗ[ℂ] H,
        partialTraceRight b (krausComplementProj b ∘ₗ
            (U.toLinearMap ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne ℂ ω ω).toLinearMap
              ∘ₗ adjoint U.toLinearMap)
            ∘ₗ krausComplementProj b)
          = ∑ k, (E k : H →ₗ[ℂ] H) ∘ₗ ρ ∘ₗ LinearMap.adjoint ((E k : H →ₗ[ℂ] H)) := by
  have hbridge : ∑ j : Option ι,
      LinearMap.adjoint ((ContinuousLinearMap.krausAugment E j).toLinearMap)
        ∘ₗ (ContinuousLinearMap.krausAugment E j).toLinearMap = LinearMap.id := by
    have hcoe : (∑ j : Option ι,
          LinearMap.adjoint ((ContinuousLinearMap.krausAugment E j).toLinearMap)
            ∘ₗ (ContinuousLinearMap.krausAugment E j).toLinearMap)
        = ((∑ j, ContinuousLinearMap.adjoint (ContinuousLinearMap.krausAugment E j)
            ∘L ContinuousLinearMap.krausAugment E j : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [ContinuousLinearMap.toLinearMap_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.adjoint_toLinearMap]
    rw [hcoe, ContinuousLinearMap.sum_adjoint_krausAugment_comp_self E hE]
    rfl
  obtain ⟨U, hU⟩ := exists_unitary_krausDilation b
    (fun j => (ContinuousLinearMap.krausAugment E j).toLinearMap) hbridge hω
  refine ⟨U, fun ρ => ?_⟩
  have hUlm : U.toLinearMap ∘ₗ tmulRightVec ω
      = krausDilation b (fun j => (ContinuousLinearMap.krausAugment E j).toLinearMap) := by
    refine LinearMap.ext fun ψ => ?_
    rw [LinearMap.comp_apply, tmulRightVec_apply]
    exact hU ψ
  exact partialTraceRight_krausComplementProj_conj b E U.toLinearMap hUlm ρ

end LinearMap
