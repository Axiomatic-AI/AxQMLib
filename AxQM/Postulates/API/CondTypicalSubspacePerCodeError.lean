/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspaceDecoder
import AxQM.Postulates.API.CondTypicalSubspacePerCode
import ToMathlib.Analysis.InnerProductSpace.GramSquareRoot
import ToMathlib.Analysis.InnerProductSpace.RankOneSum

/-!
# The √Γ identification of the pretty-good decoding overlap (N&C Thm 12.8, Box 12.5)

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability), the per-message decoder-error bound
(`State.one_sub_re_trace_prettyGood_le`, N&C eq. (12.88)) keeps the pretty-good decoding overlap in
the **physical form** `re⟪Ẽ^M_κ, S⁻¹ᐟ² E^M_κ⟫`, where `Ẽ^M_κ = P|E^M_κ⟩` is the compressed
codeword eigenvector, `E^M_κ = State.piTensorEigenbasis (σ M) κ`, and
`S⁻¹ᐟ² = (∑_{M'} P P_{M'} P).genInvSqrt` is the generalized inverse square root of the pretty-good
total operator.  The per-code spur bound
(`State.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_codebook_le_re_trace`, N&C eq. (12.94)) instead
uses the **Gram form** `re⟪e_{(M,κ)}, √Γ e_{(M,κ)}⟫`, the diagonal of the operator square root of
the Gram operator `Γ = V⋆ V` of the compressed-eigenvector synthesis operator
`V = synthesisMap (fun p ↦ P|E^{p.1}_{p.2.1}⟩)` over the global typical index `Σ_M {κ ∈ T_M}`.

This file bridges the two: it proves the two overlaps coincide.  This is Nielsen & Chuang's
identity `α = Γ^{1/2}` between eqs. (12.85) and (12.86) (Box 12.5), evaluated on the diagonal, in
the concrete random-coding apparatus — the missing link between eq. (12.88) and eq. (12.94) that
lets the per-code average error be bounded by the physical error traces of eq. (12.79).

## Main result

* `AxQM.State.re_inner_proj_genInvSqrt_piTensorEigenbasis_eq_re_inner_cfc_sqrt_gram` — the
  **√Γ identification of the decoding overlap**.  For a codebook
  `σ : Fin K → (i : ι) → State (S i)`, a self-adjoint idempotent projector `P`, and an index
  `p = (M, κ)` of the global typical index
  `Σ_M {κ ∈ T_M}`,

  `re⟪P E^M_κ, S⁻¹ᐟ² E^M_κ⟫  =  re⟪e_p, √Γ e_p⟫`,

  where `S = ∑_{M'} P (P_{M'}) P` is the pretty-good total operator,
  `P_{M'} = State.condTypicalSubspaceProj (σ M') s ε`, `S⁻¹ᐟ² = S.genInvSqrt`,
  `Γ = V⋆ V`, `V = synthesisMap (fun p ↦ P|E^{p.1}_{p.2.1}⟩)`, and
  `e_p = EuclideanSpace.basisFun _ ℂ p`.

## Proof

Let `V = synthesisMap ψ` for the global compressed-eigenvector family `ψ_p = P|E^{p.1}_{p.2.1}⟩`.

* **`S = V V⋆`.**  The frame operator identity
  `∑_i |ψ_i⟩⟨ψ_i| = V ∘ V⋆` (`sum_rankOne_self_eq_synthesisMap_comp_adjoint`), regrouped over the
  sigma index (`Fintype.sum_sigma`, `Finset.sum_coe_sort`), turns the sum of rank-one projectors
  into `∑_M ∑_{κ ∈ T_M} |P E^M_κ⟩⟨P E^M_κ| = ∑_M P P_M P = S`, the last step being the
  compressed-eigenvector frame identity
  `State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum` (with `A = P`, `P⋆ = P`).
* **`P` is absorbed by `S⁻¹ᐟ²`.**  Since `P P = P`, the total operator `S = ∑_{M'} P P_{M'} P`
  satisfies `S P = S` and `P S = S`; as `S⁻¹ᐟ²` inherits the support of `S`,
  `S⁻¹ᐟ² P = S⁻¹ᐟ²` (`ContinuousLinearMap.genInvSqrt_mul_of_mul_eq_self`, N&C's `A⁻¹ᐟ² P = A⁻¹ᐟ²`).
* **Collapse.**  The Gram square-root identity
  `V⋆ ∘ S⁻¹ᐟ² ∘ V = √Γ` (`ContinuousLinearMap.adjoint_comp_genInvSqrt_comp_self`, using `S = V V⋆`)
  gives `⟪e_p, √Γ e_p⟫ = ⟪e_p, V⋆ (S⁻¹ᐟ² (V e_p))⟫ = ⟪V e_p, S⁻¹ᐟ² (V e_p)⟫`
  (`adjoint_inner_right`); `V e_p = ψ_p = P E^M_κ` (`synthesisMap_basisFun`); and
  `S⁻¹ᐟ² (P E^M_κ) = S⁻¹ᐟ² E^M_κ` by the absorption above.  Taking `RCLike.re` of the resulting
  complex equality yields the claim.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eqs. (12.85), (12.86), (12.88), (12.94).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → QSystem}

set_option maxHeartbeats 1000000 in
-- The functional calculus `cfc Real.sqrt` of the Gram operator on the concrete global typical index
-- `Σ M, {κ ∈ T_M}` drives elaboration-heavy operator-algebra instance synthesis, so both heartbeat
-- budgets are raised.
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The √Γ identification of the pretty-good decoding overlap** (Nielsen & Chuang, Theorem 12.8,
Box 12.5, the diagonal of the identity `α = Γ^{1/2}` between eqs. (12.85) and (12.86)).  For a
codebook `σ : Fin K → (i : ι) → State (S i)`, a self-adjoint idempotent projector `P`, and an index
`p = (M, κ)` of the global conditional-typical index `Σ_M {κ ∈ T_M}`, the physical decoding overlap
of N&C's per-message error bound eq. (12.88) equals the Gram-square-root diagonal of the per-code
spur bound eq. (12.94):

`re⟪P E^M_κ, S⁻¹ᐟ² E^M_κ⟫  =  re⟪e_p, √Γ e_p⟫`,

where `E^M_κ = State.piTensorEigenbasis (σ M) κ`, `S = ∑_{M'} P (P_{M'}) P` is the pretty-good total
operator, `P_{M'} = State.condTypicalSubspaceProj (σ M') s ε`, `S⁻¹ᐟ² = S.genInvSqrt`, and
`√Γ = cfc Real.sqrt (V⋆ V)` is the operator square root of the Gram operator of the compressed
synthesis operator `V = synthesisMap (fun p ↦ P|E^{p.1}_{p.2.1}⟩)` over the sigma index, evaluated
on the standard basis vector `e_p = EuclideanSpace.basisFun _ ℂ p`.

Chains the frame identity `S = V V⋆` (`sum_rankOne_self_eq_synthesisMap_comp_adjoint` regrouped over
the sigma index, `State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum`), the `P`-absorption
`S⁻¹ᐟ² P = S⁻¹ᐟ²` (`ContinuousLinearMap.genInvSqrt_mul_of_mul_eq_self`), and the Gram square-root
identity `V⋆ S⁻¹ᐟ² V = √Γ` (`ContinuousLinearMap.adjoint_comp_genInvSqrt_comp_self`). -/
theorem State.re_inner_proj_genInvSqrt_piTensorEigenbasis_eq_re_inner_cfc_sqrt_gram
    {K : ℕ} (σ : Fin K → (i : ι) → State (S i)) (s ε : ℝ)
    (P : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
    (hPsa : IsSelfAdjoint P) (hPidem : P.comp P = P)
    (p : Σ M : Fin K, {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) :
    RCLike.re (inner ℂ (P (State.piTensorEigenbasis (σ p.1) p.2.1))
        ((∑ M', P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P)).genInvSqrt
          (State.piTensorEigenbasis (σ p.1) p.2.1)))
      = RCLike.re (inner ℂ
          (EuclideanSpace.basisFun (Σ M : Fin K,
            {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) ℂ p)
          ((cfc Real.sqrt ((adjoint (synthesisMap
              (fun q : (Σ M : Fin K,
                {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) =>
                P (State.piTensorEigenbasis (σ q.1) q.2.1)))).comp
            (synthesisMap (fun q : (Σ M : Fin K,
                {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) =>
                P (State.piTensorEigenbasis (σ q.1) q.2.1)))))
            (EuclideanSpace.basisFun (Σ M : Fin K,
              {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) ℂ p))) := by
  classical
  -- The global compressed-eigenvector family, its synthesis operator, and the total operator.
  set ψ : (Σ M : Fin K, {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) →
      (QSystem.piTensor S).space :=
    fun q => P (State.piTensorEigenbasis (σ q.1) q.2.1) with hψ
  set V := synthesisMap (𝕜 := ℂ) ψ with hV
  set Ssum := ∑ M', P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P) with hS
  have hPadj : adjoint P = P := by rw [← star_eq_adjoint]; exact hPsa
  -- `S = V ∘ V⋆`: the frame operator of the compressed eigenvectors regrouped over the sigma index.
  have hSV : Ssum = V.comp (adjoint V) := by
    rw [hV, ← sum_rankOne_self_eq_synthesisMap_comp_adjoint ψ, Fintype.sum_sigma, hS]
    refine Finset.sum_congr rfl fun M _ => ?_
    simp only [hψ]
    rw [Finset.sum_coe_sort (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)
          (fun κ => rankOne ℂ (P (State.piTensorEigenbasis (σ M) κ))
            (P (State.piTensorEigenbasis (σ M) κ))),
        ← State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum (σ M) s ε P, hPadj]
  -- `0 ≤ S`, hence its generalized inverse square root is defined.
  have hSnn : 0 ≤ Ssum := by
    rw [hSV]; exact nonneg_iff_isPositive.mpr (isPositive_self_comp_adjoint V)
  -- `P` fixes `S` on both sides (`P P = P`), so `S⁻¹ᐟ²` absorbs `P`.
  have hSP : Ssum * P = Ssum := by
    rw [hS, ContinuousLinearMap.mul_def, ContinuousLinearMap.finsetSum_comp]
    refine Finset.sum_congr rfl fun M' _ => ?_
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hPidem]
  have hPS : P * Ssum = Ssum := by
    rw [hS, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_finsetSum]
    refine Finset.sum_congr rfl fun M' _ => ?_
    rw [← ContinuousLinearMap.comp_assoc, hPidem]
  have habs : Ssum.genInvSqrt * P = Ssum.genInvSqrt := genInvSqrt_mul_of_mul_eq_self hSnn hSP hPS
  -- The Gram square-root identity `V⋆ · S⁻¹ᐟ² · V = √Γ`, with `V V⋆` replaced by `S`.
  have hΓ : cfc Real.sqrt ((adjoint V).comp V)
      = (adjoint V).comp (Ssum.genInvSqrt.comp V) := by
    have h := adjoint_comp_genInvSqrt_comp_self V
    rw [← hSV] at h
    exact h.symm
  -- Reduce to the complex-valued overlap identity, then assemble it.
  congr 1
  rw [hΓ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, hV, synthesisMap_basisFun]
  simp only [hψ]
  -- `S⁻¹ᐟ² (P E^M_κ) = S⁻¹ᐟ² E^M_κ` by the `P`-absorption.
  rw [← mul_apply_eq_comp, habs]

set_option maxHeartbeats 1000000 in
-- The functional calculus `cfc Real.sqrt` of the Gram operator on the concrete global typical index
-- `Σ M, {κ ∈ T_M}` drives elaboration-heavy operator-algebra instance synthesis, so both heartbeat
-- budgets are raised.
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The per-code average-error bound of the pretty-good decoder** (Nielsen & Chuang, Theorem 12.8,
Box 12.5, eq. (12.79)).  For a length-`n` codebook `σ : Fin K → (i : ι) → State (S i)` of `K`
product codewords, a self-adjoint idempotent projector `P` (the typical projector), and the
conditional typical projectors `P_{M'} = State.condTypicalSubspaceProj (σ M') s ε`, form N&C's
pretty-good (square-root) decoder `POVM.prettyGood A` of the family `A_{M'} = P P_{M'} P`; its
effect at message `M` is `E_M = S⁻¹ᐟ² (P P_M P) S⁻¹ᐟ²`, `S = ∑_{M'} A_{M'}`.  The **average decoding
error** `p̄ = (1/K) ∑_M (1 − re tr(σ_M E_M))` is bounded by the three physical error traces of
eq. (12.79), averaged over the codebook:

`p̄ ≤ (1/K) ∑_M [3·re tr((1−P) σ_M) + 2·re tr((1−P_M) σ_M) + ∑_{M'≠M} re tr(P σ_M P P_{M'})]`.

Composes the achievability pieces exactly as N&C's Box 12.5 does.  Averaging the per-message
bound `State.one_sub_re_trace_prettyGood_le` (eq. (12.88)) over `M`, its typical block splits as
`2 ∑_M ∑_{κ∈T_M} λ^M_κ (1 − α^phys_{(M,κ)})`; the √Γ identification
`State.re_inner_proj_genInvSqrt_piTensorEigenbasis_eq_re_inner_cfc_sqrt_gram` (eqs. (12.85)→(12.86))
turns each physical overlap `α^phys` into the Gram-square-root diagonal `α^Gram`, and regrouping the
message×typical double sum over the global sigma index `Σ_M {κ ∈ T_M}` (`Fintype.sum_sigma`,
`Finset.sum_coe_sort`) matches the left-hand side of the per-code spur bound
`State.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_codebook_le_re_trace` (eq. (12.94)), which
supplies the `3·re tr((1−P)σ_M) + re tr((1−P_M)σ_M) + ∑_{M'≠M} re tr(Pσ_MPP_{M'})` bound.  The
atypical block `∑_M ∑_{κ∉T_M} λ^M_κ` equals `∑_M re tr((1−P_M) σ_M)` by the conditional-typical mass
bridge `State.re_trace_one_sub_condTypicalSubspaceProj_comp_piTensor` (eq. (12.76)) together with
the normalisation `State.sum_prod_eigenvalueDist_eq_one` (`∑_κ λ^M_κ = 1`, so
`∑_{κ∉T_M} = 1 − ∑_{κ∈T_M}`), adding a **second** copy of the conditional-atypical trace: hence the
coefficient `2` on `re tr((1−P_M)σ_M)` here, where N&C's eq. (12.79) carries `1`.  This overcounting
arises because the same-message spur bound already folds eq. (12.95)'s
`tr(σ_M(1−P)P_M(1−P))` into `3 tr(σ_M(1−P)) + tr(σ_M(1−P_M))`, while eq. (12.88)'s separate atypical
term contributes the extra copy; it is immaterial for the random-coding expectation, where
every term vanishes for `R < χ(E)`.

The functional calculus `cfc Real.sqrt` of the Gram operator on the concrete global typical index
`Σ M, {κ ∈ T_M}` drives elaboration-heavy operator-algebra instance synthesis, so both heartbeat
budgets are raised. -/
theorem State.avgError_prettyGood_le_re_trace_percode
    {K : ℕ} (σ : Fin K → (i : ι) → State (S i)) (s ε : ℝ)
    (P : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
    (hPsa : IsSelfAdjoint P) (hPidem : P.comp P = P)
    (hA : ∀ M', (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
      ≤ P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P)) :
    (K : ℝ)⁻¹ * ∑ M : Fin K, (1 - RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
        (↑((State.piTensor (σ M)).op.comp
          ((POVM.prettyGood (fun M' => P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P))
            hA).elements (some M))) : (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)))
      ≤ (K : ℝ)⁻¹ * ∑ M : Fin K,
          (3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑((1 - P) * (State.piTensor (σ M)).op) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
            + 2 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑((1 - State.condTypicalSubspaceProj (σ M) s ε) * (State.piTensor (σ M)).op) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
            + ∑ M' ∈ Finset.univ.erase M, RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑(P.comp ((State.piTensor (σ M)).op.comp
                  (P.comp (State.condTypicalSubspaceProj (σ M') s ε)))) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))) := by
  classical
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- Regrouping any message×typical double sum over the global sigma index `Σ_M {κ ∈ T_M}`.
  have hregroup : ∀ g : (M : Fin K) → ((i : ι) → Fin (Module.finrank ℂ (S i).space)) → ℝ,
      (∑ p : (Σ M : Fin K,
          {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}), g p.1 p.2.1)
        = ∑ M : Fin K, ∑ κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε, g M κ := by
    intro g
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun M _ => Finset.sum_coe_sort _ fun κ => g M κ
  -- The typical block: average, rewrite `α^phys → α^Gram`, regroup, then apply the per-code spur
  -- bound (eq. (12.94)).
  have hSPUR_le : (∑ M : Fin K, 2 * ∑ κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε,
        (∏ i, (σ M i).eigenvalueDist (κ i)) *
          (1 - RCLike.re (inner ℂ (P (State.piTensorEigenbasis (σ M) κ))
            ((∑ M', P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P)).genInvSqrt
              (State.piTensorEigenbasis (σ M) κ)))))
      ≤ ∑ M : Fin K, (3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
            (↑((1 - P) * (State.piTensor (σ M)).op) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
          + RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
            (↑((1 - State.condTypicalSubspaceProj (σ M) s ε) * (State.piTensor (σ M)).op) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
          + ∑ M' ∈ Finset.univ.erase M, RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
            (↑(P.comp ((State.piTensor (σ M)).op.comp
                (P.comp (State.condTypicalSubspaceProj (σ M') s ε)))) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))) := by
    refine le_trans (le_of_eq ?_)
      (State.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_codebook_le_re_trace σ s ε P hPsa hPidem)
    rw [← Finset.mul_sum]
    congr 1
    rw [← hregroup fun M κ => (∏ i, (σ M i).eigenvalueDist (κ i)) *
        (1 - RCLike.re (inner ℂ (P (State.piTensorEigenbasis (σ M) κ))
          ((∑ M', P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P)).genInvSqrt
            (State.piTensorEigenbasis (σ M) κ))))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [State.re_inner_proj_genInvSqrt_piTensorEigenbasis_eq_re_inner_cfc_sqrt_gram
      σ s ε P hPsa hPidem p]
  -- The atypical block equals the conditional-atypical error trace `∑_M re tr((1−P_M)σ_M)`.
  have hATYP : (∑ M : Fin K, ∑ κ ∈ (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)ᶜ,
        ∏ i, (σ M i).eigenvalueDist (κ i))
      = ∑ M : Fin K, RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
          (↑((1 - State.condTypicalSubspaceProj (σ M) s ε) * (State.piTensor (σ M)).op) :
            (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)) := by
    refine Finset.sum_congr rfl fun M _ => ?_
    have hnorm := State.sum_prod_eigenvalueDist_eq_one (σ M)
    have hcompl := Finset.sum_add_sum_compl
      (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)
      (fun κ => ∏ i, (σ M i).eigenvalueDist (κ i))
    rw [hnorm] at hcompl
    rw [ContinuousLinearMap.mul_def,
      State.re_trace_one_sub_condTypicalSubspaceProj_comp_piTensor (σ M) s ε]
    linarith [hcompl]
  -- Assemble: per-message bound (eq. (12.88)), split, then close both blocks.
  calc ∑ M : Fin K, (1 - RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
        (↑((State.piTensor (σ M)).op.comp
          ((POVM.prettyGood (fun M' => P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P))
            hA).elements (some M))) : (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)))
      ≤ ∑ M : Fin K, (2 * ∑ κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε,
              (∏ i, (σ M i).eigenvalueDist (κ i)) *
                (1 - RCLike.re (inner ℂ (P (State.piTensorEigenbasis (σ M) κ))
                  ((∑ M', P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P)).genInvSqrt
                    (State.piTensorEigenbasis (σ M) κ))))
            + ∑ κ ∈ (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)ᶜ,
                ∏ i, (σ M i).eigenvalueDist (κ i)) :=
        Finset.sum_le_sum fun M _ => State.one_sub_re_trace_prettyGood_le σ s ε P hPsa hA M
    _ = (∑ M : Fin K, 2 * ∑ κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε,
              (∏ i, (σ M i).eigenvalueDist (κ i)) *
                (1 - RCLike.re (inner ℂ (P (State.piTensorEigenbasis (σ M) κ))
                  ((∑ M', P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P)).genInvSqrt
                    (State.piTensorEigenbasis (σ M) κ)))))
          + ∑ M : Fin K, ∑ κ ∈ (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)ᶜ,
              ∏ i, (σ M i).eigenvalueDist (κ i) := Finset.sum_add_distrib
    _ ≤ (∑ M : Fin K, (3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑((1 - P) * (State.piTensor (σ M)).op) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
            + RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑((1 - State.condTypicalSubspaceProj (σ M) s ε) * (State.piTensor (σ M)).op) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
            + ∑ M' ∈ Finset.univ.erase M, RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑(P.comp ((State.piTensor (σ M)).op.comp
                  (P.comp (State.condTypicalSubspaceProj (σ M') s ε)))) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))))
          + ∑ M : Fin K, ∑ κ ∈ (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)ᶜ,
              ∏ i, (σ M i).eigenvalueDist (κ i) := add_le_add hSPUR_le le_rfl
    _ = ∑ M : Fin K,
          (3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑((1 - P) * (State.piTensor (σ M)).op) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
            + 2 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑((1 - State.condTypicalSubspaceProj (σ M) s ε) * (State.piTensor (σ M)).op) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
            + ∑ M' ∈ Finset.univ.erase M, RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
              (↑(P.comp ((State.piTensor (σ M)).op.comp
                  (P.comp (State.condTypicalSubspaceProj (σ M') s ε)))) :
                (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))) := by
        rw [hATYP, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun M _ => by ring

end AxQM
