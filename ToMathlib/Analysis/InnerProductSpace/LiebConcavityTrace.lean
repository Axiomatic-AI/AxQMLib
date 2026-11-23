/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.LiebConcavityRpow
public import ToMathlib.Analysis.InnerProductSpace.Transpose
public import ToMathlib.Analysis.InnerProductSpace.Matricization

/-!
# Lieb's Theorem 1, trace form (Choi–Jamiołkowski bridge)

The trace-form Lieb T1 `(A, B) ↦ re Tr(K† A^q K B^r)` is jointly concave on the Lieb simplex
(`concaveAt_trace`), derived from the v-form (`concaveAt_inner_mapL`) via the Choi–Jamiołkowski
bridge. The Choi vector is `TensorProduct.matricize.symm` and the inner-product↔trace bridge is
`matricize_inner_eq_hsPairing` + `hsPairing_eq` (both pre-existing). The crux is `matricize_mapL`
— how `mapL` acts on a matricized tensor — where γ.2.b.₁'s `EuclideanSpace.transposeOp` enters.

## Main results

- `TensorProduct.matricize_mapL`: `matricize (mapL A B Ψ) = A ∘L matricize Ψ ∘L transposeOp B`.
- `TensorProduct.inner_mapL_matricize_symm`: the Choi–Jamiołkowski trace bridge.
- `TensorProduct.transposeOp_rpow`: `(transposeOp B) ^ r = transposeOp (B ^ r)`.
- `TensorProduct.concaveAt_trace`: Lieb's Theorem 1, trace form (strictly positive operators).
- `CFC.tendsto_rpow_add_smul_one` (in `…ContinuousFunctionalCalculus/Rpow/Isometric.lean`): the
  regularization limit `(a + ε • 1) ^ p → a ^ p` (`ε → 0⁺`) — the analytic input for the PSD case.
- `TensorProduct.concaveAt_trace_isPositive`: Lieb's Theorem 1, trace form, for **positive
  semidefinite** operators — the full-generality statement, obtained from `concaveAt_trace` by the
  regularization limit.
- `TensorProduct.concaveAt_trace_one_sub`, `concaveAt_trace_one_sub_isPositive`,
  `concaveOn_trace_one_sub_isPositive`: the single-parameter `(t, 1 - t)` N&C form (Theorem 11.11),
  for strictly positive and for positive semidefinite operators, the latter both pointwise and
  bundled as `ConcaveOn`.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace TensorProduct

variable {ι : Type*} [Fintype ι]

local notation "𝒞" => EuclideanSpace.conjVec
local notation "e!" => EuclideanSpace.basisFun ι ℂ

/-- The matricize bilinear coefficient as a `conjVec`-inner product:
`∑ k, ⟪eₖ, x⟫ * ⟪eₖ, y⟫ = ⟪conjVec x, y⟫` in the canonical basis of `EuclideanSpace ℂ ι`. -/
theorem sum_inner_basisFun_mul (x y : EuclideanSpace ℂ ι) :
    ∑ k, ⟪e! k, x⟫_ℂ * ⟪e! k, y⟫_ℂ = ⟪𝒞 x, y⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner, RCLike.inner_apply,
    EuclideanSpace.conjVec_apply, starRingEnd_apply, star_star]
  ring

/-- Conjugation intertwines `transposeOp` with the adjoint:
`conjVec (transposeOp B φ) = B† (conjVec φ)` (from `transposeOp = conjVec ∘ star ∘ conjVec`). -/
theorem conjVec_transposeOp (B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ : EuclideanSpace ℂ ι) : 𝒞 (EuclideanSpace.transposeOp B φ) = star B (𝒞 φ) := by
  rw [EuclideanSpace.transposeOp_apply, EuclideanSpace.conjVec_conjVec]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- **The action of `mapL` on a matricized tensor** (the Choi-bridge crux): `mapL A B` acts on
`matricize Ψ : EuclideanSpace ℂ ι →L E` by post-composing with `A` and pre-composing with the
**transpose** `EuclideanSpace.transposeOp B` (NOT `B` — the transpose is intrinsic to the Choi
pairing). `matricize (mapL A B Ψ) = A ∘L (matricize Ψ) ∘L transposeOp B`. -/
theorem matricize_mapL (A : E →L[ℂ] E) (B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (Ψ : E ⊗[ℂ] EuclideanSpace ℂ ι) :
    matricize e! (mapL A B Ψ) = A ∘L matricize e! Ψ ∘L EuclideanSpace.transposeOp B := by
  induction Ψ using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  | tmul f g =>
    ext φ
    rw [mapL_tmul, matricize_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, matricize_apply]
    simp only [LinearMap.restrictRight_tmul, smul_smul, ← Finset.sum_smul, map_smul]
    congr 1
    rw [sum_inner_basisFun_mul, sum_inner_basisFun_mul, conjVec_transposeOp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

variable [CompleteSpace E]

/-- **Choi–Jamiołkowski trace bridge**: pairing the Choi vector `matricize.symm K` through
`mapL A B` is the Frobenius/Hadamard trace `Tr(K† A K · transposeOp B)`. Assembled from
`matricize_inner_eq_hsPairing` (inner product = HS pairing), `matricize_mapL` (the `mapL` action),
and `hsPairing_eq` (HS pairing = trace of adjoint-composition). -/
theorem inner_mapL_matricize_symm (A : E →L[ℂ] E)
    (B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (K : EuclideanSpace ℂ ι →L[ℂ] E) :
    ⟪(matricize e!).symm K, mapL A B ((matricize e!).symm K)⟫_ℂ =
      LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L A ∘L K ∘L EuclideanSpace.transposeOp B) := by
  rw [matricize_inner_eq_hsPairing e!, matricize_mapL, LinearEquiv.apply_symm_apply,
    ContinuousLinearMap.hsPairing_eq]

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` (instance-search) budget, NOT the general `maxHeartbeats`: synthesizing the CFC
-- `rpow` `Pow` instance + `NonnegSpectrumClass` on the `EuclideanSpace ℂ ι →L …` operator algebra
-- (derived PiLp → C⋆-algebra chain) exceeds the 20000 default. Near-minimal: 40000 still times out.
/-- **`transposeOp` commutes with operator `rpow`** on strictly positive operators:
`(transposeOp B) ^ r = transposeOp (B ^ r)` — the rpow specialization of `cfc_transposeOp`. -/
theorem transposeOp_rpow {B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB : IsStrictlyPositive B) (r : ℝ) :
    EuclideanSpace.transposeOp B ^ r = EuclideanSpace.transposeOp (B ^ r) := by
  rw [CFC.rpow_eq_cfc_real (EuclideanSpace.transposeOp_nonneg hB.nonneg),
    CFC.rpow_eq_cfc_real hB.nonneg]
  refine EuclideanSpace.cfc_transposeOp hB.nonneg.isSelfAdjoint fun x hx ↦ ?_
  refine (Real.continuousAt_rpow_const x r (Or.inl ?_)).continuousWithinAt
  rintro rfl
  exact spectrum.not_isUnit_of_zero_mem ℝ hx hB.isUnit

/-- `transposeOp` is ℝ-linear under scalar multiplication (via the `ℂ`-linearity + coercion). -/
theorem transposeOp_smul_real (t : ℝ) (X : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace.transposeOp (t • X) = t • EuclideanSpace.transposeOp X := by
  rw [← Complex.coe_smul, EuclideanSpace.transposeOp_smul, Complex.coe_smul]

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the EuclideanSpace operator-algebra CFC.rpow / NonnegSpectrumClass
-- chain (see `transposeOp_rpow`); near-minimal (40000 times out).
/-- **Lieb's Theorem 1, trace form** (Carlen §6.1): for `K : EuclideanSpace ℂ ι →L E`, strictly
positive `Aᵢ, Bᵢ`, and `(q, r)` in the Lieb simplex, `(A, B) ↦ re Tr(K† A^q K B^r)` is jointly
concave. Derived from the v-form `concaveAt_inner_mapL` at `v = matricize.symm K`, reparametrized
along `B ↦ transposeOp B`: the Choi pairing `⟨v, mapL(A^q, (transposeOp B)^r) v⟩` equals
`Tr(K† A^q K · transposeOp((transposeOp B)^r)) = Tr(K† A^q K B^r)` (`inner_mapL_matricize_symm`
+ `transposeOp_rpow` + involution). -/
theorem concaveAt_trace (K : EuclideanSpace ℂ ι →L[ℂ] E) {q r : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1)
    {A₁ A₂ : E →L[ℂ] E} (hA₁ : IsStrictlyPositive A₁) (hA₂ : IsStrictlyPositive A₂)
    {B₁ B₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB₁ : IsStrictlyPositive B₁) (hB₂ : IsStrictlyPositive B₂)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    t • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₁ ^ q) ∘L K ∘L (B₁ ^ r))) +
        s • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₂ ^ q) ∘L K ∘L (B₂ ^ r))) ≤
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L ((t • A₁ + s • A₂) ^ q) ∘L K ∘L
          ((t • B₁ + s • B₂) ^ r))) := by
  have key := ContinuousLinearMap.LiebTensor.concaveAt_inner_mapL ((matricize e!).symm K)
    hq hr hqr hA₁ hA₂ (EuclideanSpace.transposeOp_isStrictlyPositive hB₁)
    (EuclideanSpace.transposeOp_isStrictlyPositive hB₂) ht hs hts
  rw [inner_mapL_matricize_symm, inner_mapL_matricize_symm, inner_mapL_matricize_symm,
    transposeOp_rpow hB₁, EuclideanSpace.transposeOp_transposeOp,
    transposeOp_rpow hB₂, EuclideanSpace.transposeOp_transposeOp,
    ← transposeOp_smul_real, ← transposeOp_smul_real, ← EuclideanSpace.transposeOp_add,
    transposeOp_rpow (convex_isStrictlyPositive hB₁ hB₂ ht hs hts),
    EuclideanSpace.transposeOp_transposeOp] at key
  exact key

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the `E →L E` / `EuclideanSpace` operator-algebra CFC.rpow chain
-- (same reason as `concaveAt_trace`; the default 20000 times out synthesizing `A ^ t` /
-- `B ^ (1-t)`).
/-- **Lieb's Theorem (Nielsen & Chuang, Theorem 11.11), trace form.** For a matrix
`K : EuclideanSpace ℂ ι →L E` and an exponent `t ∈ [0, 1]`, the function
`f(A, B) = re Tr(K† Aᵗ K B¹⁻ᵗ)` is jointly concave in the strictly positive operators `A, B`.
This is the single-parameter `(t, 1 - t)` special case of the general two-exponent
`concaveAt_trace` (the point `(t, 1 - t)` lies on the upper edge `q + r = 1` of the Lieb simplex),
stated in the exact shape of N&C's definition of joint concavity (11.96). -/
theorem concaveAt_trace_one_sub (K : EuclideanSpace ℂ ι →L[ℂ] E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {A₁ A₂ : E →L[ℂ] E} (hA₁ : IsStrictlyPositive A₁) (hA₂ : IsStrictlyPositive A₂)
    {B₁ B₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB₁ : IsStrictlyPositive B₁) (hB₂ : IsStrictlyPositive B₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₁ ^ t) ∘L K ∘L (B₁ ^ (1 - t)))) +
        b • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₂ ^ t) ∘L K ∘L (B₂ ^ (1 - t)))) ≤
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L ((a • A₁ + b • A₂) ^ t) ∘L K ∘L
          ((a • B₁ + b • B₂) ^ (1 - t)))) :=
  concaveAt_trace K ht0 (by linarith) (by linarith) hA₁ hA₂ hB₁ hB₂ ha hb hab

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the `E →L E` / `EuclideanSpace` operator-algebra CFC.rpow chain
-- (same reason as `concaveAt_trace`; the default 20000 times out synthesizing `X.1 ^ t` /
-- `X.2 ^ (1-t)`).
/-- **Lieb's Theorem (N&C Theorem 11.11), packaged as `ConcaveOn`.** The trace form
`f(A, B) = re Tr(K† Aᵗ K B¹⁻ᵗ)` (`t ∈ [0, 1]`) is jointly concave on the product of the two cones
of strictly positive operators. This is `concaveAt_trace_one_sub` bundled as the idiomatic
`ConcaveOn` predicate: joint concavity in the sense of N&C (11.96) is exactly `ConcaveOn ℝ`
over the (convex, by `convex_isStrictlyPositive`) domain of strictly positive `(A, B)`. -/
theorem concaveOn_trace_one_sub (K : EuclideanSpace ℂ ι →L[ℂ] E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ConcaveOn ℝ ({A : E →L[ℂ] E | IsStrictlyPositive A} ×ˢ
        {B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι | IsStrictlyPositive B})
      (fun X => RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L (X.1 ^ t) ∘L K ∘L (X.2 ^ (1 - t))))) := by
  refine ⟨convex_isStrictlyPositive.prod convex_isStrictlyPositive, ?_⟩
  rintro ⟨A₁, B₁⟩ ⟨hA₁, hB₁⟩ ⟨A₂, B₂⟩ ⟨hA₂, hB₂⟩ a b ha hb hab
  exact concaveAt_trace_one_sub K ht0 ht1 hA₁ hA₂ hB₁ hB₂ ha hb hab

end TensorProduct

/-! ## Extension to positive semidefinite operators (Nielsen & Chuang's full statement)

Nielsen & Chuang state Theorem 11.11 for **positive** — i.e. positive semidefinite — matrices `A`,
`B`; their Appendix 6 proof (Lemma A6.2) assumes the operators invertible "for convenience" and
leaves the singular case as a "minor technical modification … left as an exercise". The
strictly-positive results above (`concaveAt_trace`, `concaveAt_trace_one_sub`) are the operative
engine; the statements in this section discharge that singular case and recover N&C's full
generality, by the standard regularization limit `A ↦ A + ε • 1`, `ε → 0⁺`. This is the same
perturbation-and-limit device by which the rest of the Chapter-11 entropy development removes its
faithfulness hypotheses (e.g. `AxQM.State.vonNeumannEntropy_add_le_add'`). The analytic
input is the continuity of the operator real power along the regularizing path,
`CFC.tendsto_rpow_add_smul_one` (a general C⋆-algebra CFC-continuity lemma, in
`ToMathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Isometric.lean`, extending
the upstream file that holds the strictly-positive `CFC.continuousOn_rpow`). -/

open Filter Topology

namespace TensorProduct

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
/-- **Joint continuity of the Lieb trace functional.** If `P x → P₀` and `Q x → Q₀` along a filter,
then `re Tr(K† (P x) K (Q x)) → re Tr(K† P₀ K Q₀)`: the map `(P, Q) ↦ re Tr(K† P K Q)` is jointly
continuous, being `ContinuousLinearMap.continuous_trace` (finite dimensions) composed with the
continuous operator composition. This is the vehicle by which the strictly-positive Lieb inequality
passes to the regularization limit `ε → 0⁺`. -/
theorem tendsto_reTrace_comp {X : Type*} {l : Filter X} (K : EuclideanSpace ℂ ι →L[ℂ] E)
    {P : X → (E →L[ℂ] E)} {P₀ : E →L[ℂ] E} (hP : Tendsto P l (𝓝 P₀))
    {Q : X → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)}
    {Q₀ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} (hQ : Tendsto Q l (𝓝 Q₀)) :
    Tendsto (fun x => RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L P x ∘L K ∘L Q x))) l
      (𝓝 (RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L P₀ ∘L K ∘L Q₀)))) := by
  have hFcont : Continuous (fun pq : (E →L[ℂ] E) × (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =>
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L pq.1 ∘L K ∘L pq.2))) :=
    RCLike.continuous_re.comp (ContinuousLinearMap.continuous_trace.comp
      (continuous_const.clm_comp
        (continuous_fst.clm_comp (continuous_const.clm_comp continuous_snd))))
  -- The natural type of the composite is `re Tr` applied to a pair; `congr` folds the
  -- `Prod.fst`/`Prod.snd` projections pointwise (a cheap `rfl` each) rather than forcing the
  -- unifier to `whnf` the trace against the ascription.
  exact ((hFcont.tendsto (P₀, Q₀)).comp (hP.prodMk_nhds hQ)).congr (fun _ => rfl)

set_option maxHeartbeats 2000000 in
-- The regularization argument assembles six operator `rpow`s over `+`-sums (`(Aᵢ + ε•1) ^ q`, and
-- the convex-combination bases), each a heavy CFC elaboration on the `E →L[ℂ] E` / `EuclideanSpace`
-- operator algebra; the combined proof exceeds the default `maxHeartbeats`.
set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` `Pow` / `NonnegSpectrumClass` instance chain, as in the
-- strictly-positive `concaveAt_trace` above (the default 20000 times out synthesizing `A ^ q`).
/-- **Lieb's Theorem 1, trace form, for positive semidefinite operators** — the full-generality form
of `concaveAt_trace`. For `K : EuclideanSpace ℂ ι →L E`, `(q, r)` in the Lieb simplex, and merely
**positive** (positive semidefinite, `0 ≤ ·`) operators `Aᵢ, Bᵢ`, the map
`(A, B) ↦ re Tr(K† A^q K B^r)` satisfies the joint-concavity inequality. Proof: apply the
strictly-positive `concaveAt_trace` to the regularizations `Aᵢ + ε • 1`, `Bᵢ + ε • 1` (strictly
positive by `isStrictlyPositive_add_smul_one`), then let `ε → 0⁺`; both sides converge by
`tendsto_reTrace_comp` fed with `CFC.tendsto_rpow_add_smul_one`, and the inequality is preserved
in the limit (`le_of_tendsto_of_tendsto`). The convex combination `t • (Aᵢ + ε•1) + s • (Aⱼ + ε•1)`
on the right equals `(t • Aᵢ + s • Aⱼ) + ε • 1` because `t + s = 1` (`baseA`/`baseB`). -/
theorem concaveAt_trace_isPositive (K : EuclideanSpace ℂ ι →L[ℂ] E) {q r : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1)
    {A₁ A₂ : E →L[ℂ] E} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {B₁ B₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    t • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₁ ^ q) ∘L K ∘L (B₁ ^ r))) +
        s • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₂ ^ q) ∘L K ∘L (B₂ ^ r))) ≤
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L ((t • A₁ + s • A₂) ^ q) ∘L K ∘L
          ((t • B₁ + s • B₂) ^ r))) := by
  have hAsum : 0 ≤ t • A₁ + s • A₂ := add_nonneg (smul_nonneg ht hA₁) (smul_nonneg hs hA₂)
  have hBsum : 0 ≤ t • B₁ + s • B₂ := add_nonneg (smul_nonneg ht hB₁) (smul_nonneg hs hB₂)
  have baseA : ∀ ε : ℝ, t • A₁ + s • A₂ + ε • 1 = t • (A₁ + ε • 1) + s • (A₂ + ε • 1) := by
    intro ε
    have expand : t • (A₁ + ε • 1) + s • (A₂ + ε • 1)
        = t • A₁ + s • A₂ + (t + s) • (ε • (1 : E →L[ℂ] E)) := by module
    rw [expand, hts, one_smul]
  have baseB : ∀ ε : ℝ, t • B₁ + s • B₂ + ε • 1 = t • (B₁ + ε • 1) + s • (B₂ + ε • 1) := by
    intro ε
    have expand : t • (B₁ + ε • 1) + s • (B₂ + ε • 1)
        = t • B₁ + s • B₂ + (t + s) • (ε • (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) := by
      module
    rw [expand, hts, one_smul]
  -- Regularized joint-concavity inequality (strictly-positive `concaveAt_trace` at `Aᵢ + ε • 1`).
  have hstep : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      t • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L ((A₁ + ε • 1) ^ q) ∘L K ∘L ((B₁ + ε • 1) ^ r))) +
        s • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L ((A₂ + ε • 1) ^ q) ∘L K ∘L ((B₂ + ε • 1) ^ r))) ≤
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L ((t • (A₁ + ε • 1) + s • (A₂ + ε • 1)) ^ q) ∘L K ∘L
          ((t • (B₁ + ε • 1) + s • (B₂ + ε • 1)) ^ r))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact concaveAt_trace K hq hr hqr (isStrictlyPositive_add_smul_one hA₁ hε)
      (isStrictlyPositive_add_smul_one hA₂ hε) (isStrictlyPositive_add_smul_one hB₁ hε)
      (isStrictlyPositive_add_smul_one hB₂ hε) ht hs hts
  -- Both sides converge as `ε → 0⁺`; the right-hand base is rewritten via `baseA`/`baseB`.
  have hL := ((tendsto_reTrace_comp K (CFC.tendsto_rpow_add_smul_one hA₁ hq)
        (CFC.tendsto_rpow_add_smul_one hB₁ hr)).const_smul t).add
      ((tendsto_reTrace_comp K (CFC.tendsto_rpow_add_smul_one hA₂ hq)
        (CFC.tendsto_rpow_add_smul_one hB₂ hr)).const_smul s)
  have hR := tendsto_reTrace_comp K
      ((CFC.tendsto_rpow_add_smul_one hAsum hq).congr (fun ε => congrArg (· ^ q) (baseA ε)))
      ((CFC.tendsto_rpow_add_smul_one hBsum hr).congr (fun ε => congrArg (· ^ r) (baseB ε)))
  exact le_of_tendsto_of_tendsto hL hR hstep

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` instance chain synthesizing `A ^ t` / `B ^ (1 - t)`
-- (same reason as `concaveAt_trace_one_sub` above).
/-- **Lieb's Theorem (Nielsen & Chuang, Theorem 11.11), trace form, for positive matrices.** For a
matrix `K : EuclideanSpace ℂ ι →L E` and exponent `t ∈ [0, 1]`, the function
`f(A, B) = re Tr(K† Aᵗ K B¹⁻ᵗ)` is jointly concave in the **positive semidefinite** operators
`A, B` — N&C's statement verbatim, stated in the exact shape of N&C's definition of joint concavity
(11.96). The single-parameter `(t, 1 - t)` special case of `concaveAt_trace_isPositive`; unlike
`concaveAt_trace_one_sub`, it requires no strict-positivity hypothesis. -/
theorem concaveAt_trace_one_sub_isPositive (K : EuclideanSpace ℂ ι →L[ℂ] E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {A₁ A₂ : E →L[ℂ] E} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {B₁ B₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₁ ^ t) ∘L K ∘L (B₁ ^ (1 - t)))) +
        b • RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          (ContinuousLinearMap.adjoint K ∘L (A₂ ^ t) ∘L K ∘L (B₂ ^ (1 - t)))) ≤
      RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L ((a • A₁ + b • A₂) ^ t) ∘L K ∘L
          ((a • B₁ + b • B₂) ^ (1 - t)))) :=
  concaveAt_trace_isPositive K ht0 (by linarith) (by linarith) hA₁ hA₂ hB₁ hB₂ ha hb hab

set_option synthInstance.maxHeartbeats 80000 in
-- `synthInstance` budget for the CFC `rpow` instance chain synthesizing `X.1 ^ t` / `X.2 ^ (1 - t)`
-- (same reason as `concaveOn_trace_one_sub` above).
/-- **Lieb's Theorem (N&C Theorem 11.11), positive matrices, packaged as `ConcaveOn`.** The trace
form `f(A, B) = re Tr(K† Aᵗ K B¹⁻ᵗ)` (`t ∈ [0, 1]`) is jointly concave on the product of the two
**positive semidefinite** cones — the positive-matrices sharpening of `concaveOn_trace_one_sub`.
Pointwise concavity is `concaveAt_trace_one_sub_isPositive`; the domain is convex because the
positive cone is closed under nonnegative combinations. (`convex_Ici 0` would state the latter, but
it is not usable here: matching its `Set.Ici 0` against `{· | 0 ≤ ·}` on the
`EuclideanSpace ℂ ι →L …` operator algebra sends the elaborator into a `whnf` timeout on the
`ℝ`-module instance diamond, so the cone convexity is discharged directly.) -/
theorem concaveOn_trace_one_sub_isPositive (K : EuclideanSpace ℂ ι →L[ℂ] E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ConcaveOn ℝ ({A : E →L[ℂ] E | 0 ≤ A} ×ˢ
        {B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι | 0 ≤ B})
      (fun X => RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (ContinuousLinearMap.adjoint K ∘L (X.1 ^ t) ∘L K ∘L (X.2 ^ (1 - t))))) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨A₁, B₁⟩ ⟨hA₁, hB₁⟩ ⟨A₂, B₂⟩ ⟨hA₂, hB₂⟩ a b ha hb -
    simp only [Set.mem_ofPred_eq] at hA₁ hB₁ hA₂ hB₂
    exact ⟨add_nonneg (smul_nonneg ha hA₁) (smul_nonneg hb hA₂),
      add_nonneg (smul_nonneg ha hB₁) (smul_nonneg hb hB₂)⟩
  · rintro ⟨A₁, B₁⟩ ⟨hA₁, hB₁⟩ ⟨A₂, B₂⟩ ⟨hA₂, hB₂⟩ a b ha hb hab
    exact concaveAt_trace_one_sub_isPositive K ht0 ht1 hA₁ hA₂ hB₁ hB₂ ha hb hab

end TensorProduct
