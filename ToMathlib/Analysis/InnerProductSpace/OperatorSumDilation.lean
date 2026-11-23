/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.InnerProductSpace.UnitaryExtension

/-!
# The converse system–environment construction: a unitary dilation from a Kraus family

The file `OperatorSum.lean` builds the **forward** system–environment story: from a dilation
`V : Hin →ₗ E ⊗ F` (physically, a joint unitary acting on the principal system tensored with an
environment prepared in a fixed pure state), tracing out the environment factor `F` produces the
operator sum `ρ ↦ Σₖ Eₖ ρ Eₖ†` with operation elements `Eₖ = krausOp b V k` (Nielsen–Chuang
Eqs. (8.9)–(8.10)), and the elements are complete (`Σₖ Eₖ† Eₖ = 1`) exactly when `V` is an
isometry (Eq. (8.14)).

This file supplies the **converse** — Nielsen–Chuang §8.2, "System–environment models for any
operator-sum representation" (Eqs. (8.36)–(8.41)): **given** a finite family of operation elements
`E : ι → Hin →ₗ Eout`, assemble the dilation
`V |ψ⟩ = Σₖ Eₖ |ψ⟩ ⊗ |eₖ⟩`   (Eq. (8.37))
whose operation elements *are* the `Eₖ`, so `ρ ↦ tr_F(V ρ V†)` realises the operator sum, and — when
the family is **complete** (`Σₖ Eₖ† Eₖ = 1`) — `V` is an isometry that **extends to a unitary** `U`
on the joint space with `U(ψ ⊗ ω) = V ψ` (Eq. (8.36)). This is the construction N&C uses to show
that *any* operator-sum representation arises from a reasonable environmental model, and the
starting point for Exercise 8.8 (its non-trace-preserving extension) and Exercise 8.9 (its
measurement-model extension).

## Main definitions and results

* `LinearMap.krausDilation b E` — the dilation `V = Σₖ embedRight b k ∘ₗ Eₖ`, i.e.
  `V ψ = Σₖ Eₖ ψ ⊗ b k` (Eq. (8.37)).
* `LinearMap.krausOp_krausDilation` — the assembled dilation has the prescribed operation elements:
  `krausOp b (krausDilation b E) k = Eₖ` (Eq. (8.41), the block-column reading of `U`).
* `LinearMap.adjoint_krausDilation_comp_self` — `V† V = Σₖ Eₖ† Eₖ`; hence `V` is an isometry **iff**
  the family is complete (`Σₖ Eₖ† Eₖ = 1`, Eq. (8.38)).
* `LinearMap.partialTraceRight_krausDilation_conj` — the operator-sum recovery (Eq. (8.39)):
  `tr_F(V ρ V†) = Σₖ Eₖ ρ Eₖ†`.
* `LinearMap.exists_unitary_krausDilation` — **the unitary (Eq. (8.36))**: for a complete family and
  a unit environment state `ω`, there is a unitary `U : (H ⊗ F) ≃ₗᵢ (H ⊗ F)` with
  `U (ψ ⊗ ω) = krausDilation b E ψ`, obtained by extending the isometry `V` (N&C Exercise 2.67,
  `LinearMap.unitaryExtend`).
* `LinearMap.partialTraceRight_conj_tmulRightVec_krausDilation` — the model realises the operation:
  `tr_F(U (ρ ⊗ |ω⟩⟨ω|) U†) = Σₖ Eₖ ρ Eₖ†`.

## Design notes

The construction is stated at the `LinearMap` (`→ₗ`) level, matching the existing `krausOp` dilation
API (`OperatorSum.lean`): `krausOp_krausDilation` is then the exact inverse of the forward theorem
`sum_adjoint_krausOp_comp_krausOp`, and the recovery `partialTraceRight_krausDilation_conj` is a
one-line corollary of `partialTraceRight_conj_eq_sum_krausOp` composed with it. The dilation and its
Kraus-recovery keep the input space `Hin` and output space `Eout` distinct (as `krausOp` does), so
the algebra is reusable for space-changing operations; the *unitary* results specialise to the
physical square case `Hin = Eout = H`, since a unitary on the joint space acts on one space `H ⊗ F`
and its input `ψ ⊗ ω` must live there too.

The unitary is produced by `LinearMap.unitaryExtend` (N&C Exercise 2.67): the isometry `V`
restricted to the subspace `{ψ ⊗ ω}` of `H ⊗ F` is inner-product preserving, and any such map on a
subspace of
a finite-dimensional space extends to a unitary of the whole space. The determination of `U` off the
`ψ ⊗ ω` subspace is exactly the "the rest of the block matrix is our choice" freedom of N&C's
Box 8.1.

Like the rest of §8.2's operator-sum development, the content is operator/Hilbert-space linear
algebra over `H →ₗ[𝕜] G`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (System–environment models; Box 8.1; Exercises 8.8, 8.9).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace LinearMap

section KrausDilation

variable {𝕜 Hin Eout F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Hin] [InnerProductSpace 𝕜 Hin] [FiniteDimensional 𝕜 Hin]
  [NormedAddCommGroup Eout] [InnerProductSpace 𝕜 Eout] [FiniteDimensional 𝕜 Eout]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- The **dilation assembled from a Kraus family** `E : ι → Hin →ₗ Eout` relative to an orthonormal
basis `b` of the environment factor `F`: `V = Σₖ embedRight b k ∘ₗ Eₖ`, that is
`V ψ = Σₖ Eₖ ψ ⊗ b k` (Nielsen–Chuang Eq. (8.37)). This is the map whose operation elements
(`krausOp`) are exactly the `Eₖ` (`krausOp_krausDilation`). -/
noncomputable def krausDilation (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) :
    Hin →ₗ[𝕜] Eout ⊗[𝕜] F :=
  ∑ k, embedRight b k ∘ₗ E k

omit [FiniteDimensional 𝕜 Hin] [FiniteDimensional 𝕜 Eout] [FiniteDimensional 𝕜 F] in
/-- The assembled dilation acts by `V ψ = Σₖ Eₖ ψ ⊗ b k` (Nielsen–Chuang Eq. (8.37)). -/
theorem krausDilation_apply (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) (x : Hin) :
    krausDilation b E x = ∑ k, E k x ⊗ₜ[𝕜] b k := by
  simp only [krausDilation, LinearMap.sum_apply, LinearMap.comp_apply, embedRight_apply]

omit [FiniteDimensional 𝕜 Hin] [FiniteDimensional 𝕜 Eout] [FiniteDimensional 𝕜 F] in
/-- **The assembled dilation recovers the operation elements** (Nielsen–Chuang Eq. (8.41)): the
`k`-th Kraus operator of `krausDilation b E` is `Eₖ`. By delta-orthogonality of the embed/restrict
maps (`restrictRight_comp_embedRight`), contracting `V = Σⱼ embedRight b j ∘ₗ Eⱼ` against `b k`
keeps only the `j = k` term. -/
theorem krausOp_krausDilation (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) (k : ι) :
    krausOp b (krausDilation b E) k = E k := by
  classical
  ext x
  simp only [krausOp, LinearMap.comp_apply, krausDilation, LinearMap.sum_apply, map_sum,
    embedRight_apply, restrictRight_tmul, b.inner_eq_ite]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [ite_eq_right (Ne.symm hjk), zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The adjoint of the assembled dilation: `V† = Σₖ Eₖ† ∘ₗ restrictRight b k`. Distributes the
adjoint over the sum and uses `adjoint_embedRight` (`(embedRight b k)† = restrictRight b k`). -/
theorem adjoint_krausDilation (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) :
    adjoint (krausDilation b E) = ∑ k, adjoint (E k) ∘ₗ restrictRight b k := by
  rw [krausDilation, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adjoint_comp, adjoint_embedRight]

/-- **General Kraus identity**: for *any* dilation `V`,
`Σₖ (krausOp b V k)† (krausOp b V k) = V† V`.
Writing `Eₖ† Eₖ = V† ∘ₗ (embedRight b k ∘ₗ restrictRight b k) ∘ₗ V` and summing, the resolution of
identity `Σₖ embedRight b k ∘ₗ restrictRight b k = 1` collapses the middle factor. Specialising to a
`V` with `V† V = 1` recovers the completeness relation `sum_adjoint_krausOp_comp_krausOp`. -/
theorem sum_adjoint_krausOp_comp_krausOp_eq (b : OrthonormalBasis ι 𝕜 F)
    (V : Hin →ₗ[𝕜] Eout ⊗[𝕜] F) :
    ∑ k, adjoint (krausOp b V k) ∘ₗ krausOp b V k = adjoint V ∘ₗ V := by
  ext x
  simp only [LinearMap.sum_apply, krausOp, adjoint_comp, adjoint_restrictRight,
    LinearMap.comp_apply]
  rw [← map_sum]
  congr 1
  calc ∑ k, embedRight b k (restrictRight b k (V x))
      = (∑ k, embedRight b k ∘ₗ restrictRight b k) (V x) := by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    _ = V x := by rw [sum_embedRight_comp_restrictRight, LinearMap.id_apply]

/-- **`V† V = Σₖ Eₖ† Eₖ`** for the assembled dilation `V = krausDilation b E`. Consequently `V` is
an **isometry** (`V† V = 1`) **iff** the family is **complete** (`Σₖ Eₖ† Eₖ = 1`) — Nielsen–Chuang
Eq. (8.38). Immediate from `sum_adjoint_krausOp_comp_krausOp_eq` and `krausOp_krausDilation`. -/
theorem adjoint_krausDilation_comp_self (b : OrthonormalBasis ι 𝕜 F) (E : ι → Hin →ₗ[𝕜] Eout) :
    adjoint (krausDilation b E) ∘ₗ krausDilation b E = ∑ k, adjoint (E k) ∘ₗ E k := by
  rw [← sum_adjoint_krausOp_comp_krausOp_eq b (krausDilation b E)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [krausOp_krausDilation]

/-- **The assembled dilation is an isometry when the family is complete** (`Σₖ Eₖ† Eₖ = 1`): then
`V† V = 1`. This is the hypothesis that lets `V` extend to a unitary
(`exists_unitary_krausDilation`). -/
theorem adjoint_krausDilation_comp_self_eq_id (b : OrthonormalBasis ι 𝕜 F)
    (E : ι → Hin →ₗ[𝕜] Eout) (hE : ∑ k, adjoint (E k) ∘ₗ E k = LinearMap.id) :
    adjoint (krausDilation b E) ∘ₗ krausDilation b E = LinearMap.id := by
  rw [adjoint_krausDilation_comp_self, hE]

/-- **Operator-sum recovery from the assembled dilation** (Nielsen–Chuang Eq. (8.39)): tracing out
the environment factor from the conjugation `V ρ V†` returns the operator sum with the prescribed
operation elements, `tr_F(V ρ V†) = Σₖ Eₖ ρ Eₖ†`. No completeness hypothesis is needed. Combines the
forward theorem `partialTraceRight_conj_eq_sum_krausOp` with `krausOp_krausDilation`. -/
theorem partialTraceRight_krausDilation_conj (b : OrthonormalBasis ι 𝕜 F)
    (E : ι → Hin →ₗ[𝕜] Eout) (ρ : Hin →ₗ[𝕜] Hin) :
    partialTraceRight b (krausDilation b E ∘ₗ ρ ∘ₗ adjoint (krausDilation b E)) =
      ∑ k, E k ∘ₗ ρ ∘ₗ adjoint (E k) := by
  rw [partialTraceRight_conj_eq_sum_krausOp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [krausOp_krausDilation]

/-- **The system–environment model realises the operation** (Nielsen–Chuang Eq. (8.36), the
recovery identity). If a joint map `U` intertwines the ancilla embedding with the dilation —
`U ∘ₗ tmulRightVec ω = krausDilation b E`, i.e. `U (ψ ⊗ ω) = V ψ` — then discarding the environment
factor from the conjugation of `ρ ⊗ |ω⟩⟨ω|` by `U` returns the operator sum,
`tr_F(U (ρ ⊗ |ω⟩⟨ω|) U†) = Σₖ Eₖ ρ Eₖ†`. The recovery needs no unitarity of `U`; the *physical*
model additionally takes `U` unitary (`exists_unitary_krausDilation`). Reuses the environment-model
recovery `partialTraceRight_conj_map_rankOne_eq_sum_krausOp` (with the joint map `W = U`), whose
operation elements `krausOp b (U ∘ₗ tmulRightVec ω) k` become the `Eₖ` after rewriting by `hU` and
`krausOp_krausDilation`. -/
theorem partialTraceRight_conj_tmulRightVec_krausDilation (b : OrthonormalBasis ι 𝕜 F)
    (E : ι → Hin →ₗ[𝕜] Eout) (U : Hin ⊗[𝕜] F →ₗ[𝕜] Eout ⊗[𝕜] F) {ω : F}
    (hU : U ∘ₗ tmulRightVec ω = krausDilation b E) (ρ : Hin →ₗ[𝕜] Hin) :
    partialTraceRight b
        (U ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne 𝕜 ω ω).toLinearMap ∘ₗ adjoint U)
      = ∑ k, E k ∘ₗ ρ ∘ₗ adjoint (E k) := by
  rw [partialTraceRight_conj_map_rankOne_eq_sum_krausOp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hU, krausOp_krausDilation]

end KrausDilation

section Unitary

variable {𝕜 H F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- **The system–environment unitary** (Nielsen–Chuang Eq. (8.36)). For a **complete** family
`E : ι → H →ₗ H` (`Σₖ Eₖ† Eₖ = 1`) and a **unit** environment state `ω`, the assembled dilation
`V = krausDilation b E : H →ₗ H ⊗ F` — an isometry — **extends to a unitary** `U` on the joint space
`H ⊗ F`, agreeing with `V` on the input subspace: `U (ψ ⊗ ω) = V ψ` for every `ψ`. This is N&C's
statement that "the operator `U` can be extended to a unitary operator acting on the entire joint
state space" — the construction of Box 8.1, whose remaining block-matrix entries are our free
choice. Built from `LinearMap.unitaryExtend` (N&C Exercise 2.67) applied to the subspace
`{ψ ⊗ ω} = range (tmulRightVec ω)`: the map `ψ ⊗ ω ↦ V ψ` there is inner-product preserving because
`V` is an isometry (`adjoint_krausDilation_comp_self_eq_id`) and `ω` is a unit vector. -/
theorem exists_unitary_krausDilation (b : OrthonormalBasis ι 𝕜 F) (E : ι → H →ₗ[𝕜] H)
    (hE : ∑ k, adjoint (E k) ∘ₗ E k = LinearMap.id) {ω : F} (hω : ‖ω‖ = 1) :
    ∃ U : (H ⊗[𝕜] F) ≃ₗᵢ[𝕜] (H ⊗[𝕜] F), ∀ ψ : H, U (ψ ⊗ₜ[𝕜] ω) = krausDilation b E ψ := by
  set V := krausDilation b E with hVdef
  have hViso : ∀ x y : H, ⟪V x, V y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
    intro x y
    rw [← adjoint_inner_right, ← LinearMap.comp_apply,
      adjoint_krausDilation_comp_self_eq_id b E hE, LinearMap.id_apply]
  have hωω : ⟪ω, ω⟫_𝕜 = 1 := by rw [inner_self_eq_norm_sq_to_K, hω]; simp
  set W : Submodule 𝕜 (H ⊗[𝕜] F) := LinearMap.range (tmulRightVec ω) with hWdef
  set g₀ : (H ⊗[𝕜] F) →ₗ[𝕜] (H ⊗[𝕜] F) := V ∘ₗ contractRightVec ω with hg₀def
  have hg₀ : ∀ ψ : H, g₀ (ψ ⊗ₜ[𝕜] ω) = V ψ := by
    intro ψ
    simp only [hg₀def, LinearMap.comp_apply, contractRightVec_tmul, hωω, one_smul]
  set g : ↥W →ₗ[𝕜] (H ⊗[𝕜] F) := g₀.domRestrict W with hgdef
  have hg : ∀ w₁ w₂ : ↥W, ⟪g w₁, g w₂⟫_𝕜 = ⟪w₁, w₂⟫_𝕜 := by
    intro w₁ w₂
    obtain ⟨ψ₁, hψ₁⟩ := LinearMap.mem_range.mp w₁.2
    obtain ⟨ψ₂, hψ₂⟩ := LinearMap.mem_range.mp w₂.2
    have e₁ : (↑w₁ : H ⊗[𝕜] F) = ψ₁ ⊗ₜ[𝕜] ω := by rw [← hψ₁, tmulRightVec_apply]
    have e₂ : (↑w₂ : H ⊗[𝕜] F) = ψ₂ ⊗ₜ[𝕜] ω := by rw [← hψ₂, tmulRightVec_apply]
    rw [hgdef, LinearMap.domRestrict_apply, LinearMap.domRestrict_apply, e₁, e₂, hg₀, hg₀, hViso,
      Submodule.coe_inner, e₁, e₂, TensorProduct.inner_tmul, hωω, mul_one]
  refine ⟨g.unitaryExtend hg, fun ψ => ?_⟩
  have hmem : ψ ⊗ₜ[𝕜] ω ∈ W := LinearMap.mem_range.mpr ⟨ψ, tmulRightVec_apply ω ψ⟩
  calc (g.unitaryExtend hg) (ψ ⊗ₜ[𝕜] ω)
      = g ⟨ψ ⊗ₜ[𝕜] ω, hmem⟩ := g.unitaryExtend_apply hg ⟨ψ ⊗ₜ[𝕜] ω, hmem⟩
    _ = g₀ (ψ ⊗ₜ[𝕜] ω) := by rw [hgdef, LinearMap.domRestrict_apply]
    _ = V ψ := hg₀ ψ

end Unitary

end LinearMap

namespace ContinuousLinearMap

-- Both instance families are load-bearing; neither is redundant here. `ContinuousLinearMap.adjoint`
-- (in the hypothesis) needs `[CompleteSpace _]`, which is *not* synthesized from
-- `[FiniteDimensional ℂ _]` in this module: `FiniteDimensional.completeSpace` is deliberately not a
-- global instance (`Normed/Module/FiniteDimension.lean`), so dropping `[CompleteSpace _]` fails
-- elaboration with a `CompleteSpace` synthesis error. `LinearMap.adjoint` (in the conclusion)
-- needs `[FiniteDimensional ℂ _]`. The explicit `[CompleteSpace _]` matches the sibling
-- `ContinuousLinearMap.sum_adjoint_comp_comp_le_one`.
variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]
  {ι : Type*} [Fintype ι]

/-- **The `LinearMap`-level completeness relation from the `ContinuousLinearMap` one.** For an
operator family `E : ι → H →L[ℂ] G`, the completeness relation `∑ᵢ Eᵢ† Eᵢ = 1` (in the
`ContinuousLinearMap` algebra) transports along the `→ₗ` coercion to the `LinearMap` form
`∑ᵢ (Eᵢ†)ₗ ∘ₗ (Eᵢ)ₗ = 1ₗ`. This is the bridge that lets a caller holding the physical
`ContinuousLinearMap` completeness relation feed the `LinearMap`-stated dilation API
(`LinearMap.krausDilation`, `LinearMap.exists_unitary_krausDilation`), whose isometry hypothesis is
`∑ₖ (Eₖ)ₗ† ∘ₗ (Eₖ)ₗ = LinearMap.id`. Termwise: `↑(Eᵢ† ∘ Eᵢ) = (Eᵢ†)ₗ ∘ₗ (Eᵢ)ₗ` via `coe_comp` and
`adjoint_toLinearMap`. -/
theorem sum_adjoint_comp_toLinearMap_eq_id (E : ι → H →L[ℂ] G)
    (hE : ∑ i, adjoint (E i) ∘L E i = 1) :
    ∑ i, LinearMap.adjoint ((E i).toLinearMap) ∘ₗ (E i).toLinearMap = LinearMap.id := by
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => T x) hE
  simpa only [toLinearMap_sum, sum_apply, comp_apply, one_apply_eq_self, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.comp_apply, coe_coe, adjoint_toLinearMap,
    LinearMap.id_apply] using h

end ContinuousLinearMap
