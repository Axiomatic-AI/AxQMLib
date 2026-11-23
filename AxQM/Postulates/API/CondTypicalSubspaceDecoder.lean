/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspaceFrame
import ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurementError
import ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurement
import ToMathlib.Analysis.InnerProductSpace.GeneralizedInverseSqrt

/-!
# The pretty-good decoder-error bound at the codeword (N&C Thm 12.8, Box 12.5, eqs. (12.84)–(12.88))

The *instantiation* of the abstract pretty-good decoder-error reduction
(`InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le`, N&C eqs. (12.86)→(12.88)) at the
concrete random-coding apparatus of Nielsen & Chuang's Holevo–Schumacher–Westmoreland achievability
argument (Theorem 12.8, `χ(E) = C⁽¹⁾(E)`).

Alice's codebook is `σ : Fin K → (i : ι) → State (S i)`; message `M` is carried by the product
codeword `σ_M = ⨂ₚ i, σ M i` on `(QSystem.piTensor S).space`, diagonal in the product eigenbasis
`|E^M_κ⟩ = State.piTensorEigenbasis (σ M) κ` with eigenvalue `λ^M_κ = ∏ᵢ (σ M i).eigenvalueDist κᵢ`
(`State.piTensor_op_apply_piTensorEigenbasis`).  With `P` the (typical-subspace) projector and
`P_{M'} = State.condTypicalSubspaceProj (σ M') s ε` the conditional typical projectors, N&C's
pretty-good (square-root) decoder is the POVM `POVM.prettyGood A` of the positive family
`A_{M'} = P · P_{M'} · P` (eq. (12.78)): its effect at the true message `M`,
`E_M = S⁻¹ᐟ² · (P P_M P) · S⁻¹ᐟ²` with `S = ∑_{M'} A_{M'}`, is the conjugation of `A_M` by the
generalized inverse square root `S⁻¹ᐟ²` of the total operator.

## Main results

* `AxQM.State.piTensor_op_eq_sum_smul_rankOne` — the **full spectral decomposition of a
  product codeword**: `σ_M = ∑_κ λ^M_κ |E^M_κ⟩⟨E^M_κ|`, the sum over the *entire* product eigenbasis
  (the `T = univ` companion of `State.condTypicalSubspaceProj_comp_piTensor_op_eq_sum`).
* `AxQM.State.sum_prod_eigenvalueDist_eq_one` — the **normalisation of the product
  eigenvalue distribution**: `∑_κ λ^M_κ = 1`, the product-of-marginals form of `tr σ_M = 1`.
* `AxQM.State.one_sub_re_trace_prettyGood_le` — the **per-message decoder-error bound**
  (N&C eqs. (12.84)–(12.88)).  For the pretty-good decoder `POVM.prettyGood A` of the family
  `A_{M'} = P P_{M'} P` and any message `M`, the deficit of the correct-decoding trace satisfies

  `1 − re tr(σ_M · E_M)  ≤  2·∑_{κ∈T_M} λ^M_κ (1 − re⟪Ẽ^M_κ, S⁻¹ᐟ² E^M_κ⟫) + ∑_{κ∉T_M} λ^M_κ`,

  where `T_M = Real.condTypicalSeq (fun i ↦ (σ M i).eigenvalueDist) s ε` is the conditional typical
  set and `Ẽ^M_κ = P|E^M_κ⟩` the compressed eigenvector.  This is N&C's eq. (12.88), with the
  decoding overlap kept in the **physical form** `re⟪Ẽ^M_κ, S⁻¹ᐟ² E^M_κ⟫`.

## Proof of the main result

Instantiate the abstract reduction `InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le` at
`T = S⁻¹ᐟ²` (self-adjoint, `ContinuousLinearMap.isSelfAdjoint_genInvSqrt`), spectral family
`φ_κ = |E^M_κ⟩`, frame family `ψ_κ = P|E^M_κ⟩`, weights `λ^M_κ`, and typical set `J = T_M`.  Its
hypotheses `∑_κ λ^M_κ = 1` and `0 ≤ λ^M_κ` are `State.sum_prod_eigenvalueDist_eq_one` and
`State.eigenvalueDist_nonneg`.  Its left-hand operator is identified with the physical decoder
trace:

* `∑_κ λ^M_κ |E^M_κ⟩⟨E^M_κ| = σ_M` is `State.piTensor_op_eq_sum_smul_rankOne`;
* `∑_{κ∈T_M} |Ẽ^M_κ⟩⟨Ẽ^M_κ| = P P_M P = A_M` is the frame identity
  `State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum` (with `A = P`, using `P⋆ = P`);
* `E_M = S⁻¹ᐟ² · A_M · S⁻¹ᐟ²` is `POVM.prettyGood_elements_some` (with `·` the composition on the
  operator monoid).

The right-hand side is already N&C's eq. (12.88).  The final identification of the physical overlap
`re⟪Ẽ^M_κ, S⁻¹ᐟ² E^M_κ⟫` with the Gram-square-root diagonal `re⟪e_{(M,κ)}, √Γ e_{(M,κ)}⟫` of
`State.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_codebook_le_re_trace` (via `P`-absorption of
`S⁻¹ᐟ²` and the Gram identity `ContinuousLinearMap.adjoint_comp_genInvSqrt_comp_self`), and the
average over `M`, are carried out in `AxQM/Postulates/API/CondTypicalSubspacePerCodeError.lean`.

It composes the frame identities (`CondTypicalSubspaceFrame`) with the abstract
decoder reduction (`ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurementError`).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eqs. (12.78), (12.84)–(12.88).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → QSystem}

/-- **The full spectral decomposition of a product codeword** (Nielsen & Chuang, Theorem 12.8,
Box 12.5).  The product state `σ_M = ⨂ₚ i, σ i` is the eigenvalue-weighted sum of the rank-one
projectors onto its *entire* product eigenbasis:

`σ_M  =  ∑_κ λ_κ |E_κ⟩⟨E_κ|`,   `λ_κ = ∏ᵢ (σ i).eigenvalueDist κᵢ`,
`|E_κ⟩ = State.piTensorEigenbasis σ κ`.

The `T = univ` companion of `State.condTypicalSubspaceProj_comp_piTensor_op_eq_sum` (which keeps
only the typical terms): the product eigenbasis's resolution of the identity
(`OrthonormalBasis.sum_rankOne_eq_id`) composed with `σ_M` contracts each rank-one's second slot
against `σ_M |E_κ⟩ = λ_κ |E_κ⟩` (`State.piTensor_op_apply_piTensorEigenbasis`, using the
self-adjointness `State.isSelfAdjoint_op`), and the real eigenvalue passes out of the
conjugate-linear slot. -/
theorem State.piTensor_op_eq_sum_smul_rankOne (σ : (i : ι) → State (S i)) :
    (State.piTensor σ).op
      = ∑ κ : (i : ι) → Fin (Module.finrank ℂ (S i).space),
          ((∏ i, (σ i).eigenvalueDist (κ i) : ℝ) : ℂ) •
            rankOne ℂ (State.piTensorEigenbasis σ κ) (State.piTensorEigenbasis σ κ) := by
  rw [← ContinuousLinearMap.id_comp (State.piTensor σ).op,
    ← OrthonormalBasis.sum_rankOne_eq_id (State.piTensorEigenbasis σ),
    ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [InnerProductSpace.rankOne_comp, (State.isSelfAdjoint_op (State.piTensor σ)).adjoint_eq,
    State.piTensor_op_apply_piTensorEigenbasis]
  ext z
  simp only [rankOne_apply, FunLike.coe_smul, Pi.smul_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]

/-- **Normalisation of the product eigenvalue distribution** (Nielsen & Chuang, Theorem 12.8).  The
product eigenvalues `λ_κ = ∏ᵢ (σ i).eigenvalueDist κᵢ` of the product codeword `σ_M = ⨂ₚ i, σ i` sum
to `1`:

`∑_κ ∏ᵢ (σ i).eigenvalueDist κᵢ  =  1`.

The product-of-marginals form of `tr σ_M = 1`: the sum over product index sequences factors into the
product of the per-factor sums (`Finset.prod_univ_sum`), each of which is `1`
(`State.eigenvalueDist_sum_eq_one`). -/
theorem State.sum_prod_eigenvalueDist_eq_one (σ : (i : ι) → State (S i)) :
    ∑ κ : (i : ι) → Fin (Module.finrank ℂ (S i).space), ∏ i, (σ i).eigenvalueDist (κ i) = 1 := by
  have h : (1 : ℝ) = ∏ i : ι, ∑ j, (σ i).eigenvalueDist j := by
    simp only [State.eigenvalueDist_sum_eq_one, Finset.prod_const_one]
  rw [h, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **The per-message decoder-error bound of the pretty-good measurement** (Nielsen & Chuang,
Theorem 12.8, Box 12.5, eqs. (12.84)–(12.88)).  For a codebook `σ : Fin K → (i : ι) → State (S i)`,
a self-adjoint idempotent projector `P`, and the conditional typical projectors
`P_{M'} = State.condTypicalSubspaceProj (σ M') s ε`, form N&C's pretty-good (square-root) decoder
`POVM.prettyGood A` of the positive family `A_{M'} = P · P_{M'} · P` (eq. (12.78)); its effect at
the true message `M` is `E_M = S⁻¹ᐟ² · A_M · S⁻¹ᐟ²`, `S = ∑_{M'} A_{M'}`, `S⁻¹ᐟ² = S.genInvSqrt`.
Then
the deficit of the correct-decoding trace `re tr(σ_M · E_M)` is bounded by N&C's eq. (12.88):

`1 − re tr(σ_M · E_M)  ≤  2·∑_{κ∈T_M} λ^M_κ (1 − re⟪Ẽ^M_κ, S⁻¹ᐟ² E^M_κ⟫) + ∑_{κ∉T_M} λ^M_κ`,

where `T_M = Real.condTypicalSeq (fun i ↦ (σ M i).eigenvalueDist) s ε`,
`λ^M_κ = ∏ᵢ (σ M i).eigenvalueDist κᵢ`, `E^M_κ = State.piTensorEigenbasis (σ M) κ`, and
`Ẽ^M_κ = P E^M_κ` is the compressed eigenvector.  The decoding overlap `re⟪Ẽ^M_κ, S⁻¹ᐟ² E^M_κ⟫` is
N&C's diagonal `α_{(M,κ),(M,κ)}` kept in physical form
(its identification with the Gram-square-root diagonal `re⟪e, √Γ e⟫` is in
`AxQM/Postulates/API/CondTypicalSubspacePerCodeError.lean`).

Instantiates the abstract reduction
`InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le` at
`T = S⁻¹ᐟ²`, `φ = |E^M_κ⟩`, `ψ = P|E^M_κ⟩`, `λ = λ^M_κ`, `J = T_M`, identifying its left-hand
operator with the physical decoder trace via `State.piTensor_op_eq_sum_smul_rankOne` (the codeword
`σ_M`), `State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum` (the frame `A_M = P P_M P`), and
`POVM.prettyGood_elements_some` (the decoder effect `E_M`). -/
theorem State.one_sub_re_trace_prettyGood_le {K : ℕ} (σ : Fin K → (i : ι) → State (S i)) (s ε : ℝ)
    (P : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
    (hPsa : IsSelfAdjoint P)
    (hA : ∀ M', (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
      ≤ P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P))
    (M : Fin K) :
    1 - RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
        (↑((State.piTensor (σ M)).op.comp
          ((POVM.prettyGood (fun M' => P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P))
            hA).elements (some M))) : (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
      ≤ 2 * ∑ κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε,
          (∏ i, (σ M i).eigenvalueDist (κ i)) *
            (1 - RCLike.re (inner ℂ (P (State.piTensorEigenbasis (σ M) κ))
              ((∑ M', P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P)).genInvSqrt
                (State.piTensorEigenbasis (σ M) κ))))
        + ∑ κ ∈ (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)ᶜ,
            ∏ i, (σ M i).eigenvalueDist (κ i) := by
  classical
  set A : Fin K → ((QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space) :=
    fun M' => P.comp ((State.condTypicalSubspaceProj (σ M') s ε).comp P) with hAdef
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hPsa
  have hSop : (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space) ≤ ∑ M', A M' :=
    Finset.sum_nonneg fun M' _ => hA M'
  -- The frame operator `A_M = ∑_{κ∈T_M} |P E_κ⟩⟨P E_κ|`.
  have hAM : A M = ∑ κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε,
      rankOne ℂ (P (State.piTensorEigenbasis (σ M) κ)) (P (State.piTensorEigenbasis (σ M) κ)) := by
    have h := State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum (σ M) s ε P
    rw [hPadj] at h
    exact h
  -- The pretty-good decoder effect `E_M = S⁻¹ᐟ² · A_M · S⁻¹ᐟ²`, in composition form.
  have hEff : (POVM.prettyGood A hA).elements (some M)
      = (∑ M', A M').genInvSqrt.comp
          ((∑ κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε,
              rankOne ℂ (P (State.piTensorEigenbasis (σ M) κ))
                (P (State.piTensorEigenbasis (σ M) κ))).comp (∑ M', A M').genInvSqrt) := by
    rw [POVM.prettyGood_elements_some, hAM, mul_assoc]
    rfl
  -- Instantiate the abstract pretty-good decoder-error reduction (eqs. (12.86)→(12.88)).
  have key := InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le
    (∑ M', A M').genInvSqrt (ContinuousLinearMap.isSelfAdjoint_genInvSqrt hSop)
    (fun κ => State.piTensorEigenbasis (σ M) κ)
    (fun κ => P (State.piTensorEigenbasis (σ M) κ))
    (fun κ => ∏ i, (σ M i).eigenvalueDist (κ i))
    (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)
    (fun κ => Finset.prod_nonneg fun i _ => State.eigenvalueDist_nonneg _ _)
    (State.sum_prod_eigenvalueDist_eq_one (σ M))
  rw [hEff, State.piTensor_op_eq_sum_smul_rankOne (σ M)]
  exact key

end AxQM
