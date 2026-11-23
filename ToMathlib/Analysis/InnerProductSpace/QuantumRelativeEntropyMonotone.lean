/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.DepolarizingPartialTrace
public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyConvexNonfaithful
public import ToMathlib.Analysis.InnerProductSpace.ReducedState

/-!
# Monotonicity of the quantum relative entropy under the partial trace

Fix finite-dimensional complex inner product spaces `E`, `F` and an orthonormal basis `b` of `F`
of dimension `d = |ι|`. Tracing out the right factor of a bipartite operator cannot increase the
quantum relative entropy: for strictly positive operators `ρ, σ : E ⊗ F →L[ℂ] E ⊗ F` — density
operators, or more generally any strictly positive operators, not necessarily normalized —

`D(Tr_F ρ ‖ Tr_F σ) ≤ D(ρ ‖ σ)`.

This is the operator-level heart of Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 11.17 (monotonicity of the relative entropy), and the bridge to the strong
subadditivity of the von Neumann entropy (Theorem 11.14).

## Proof route

The completely depolarizing partial-trace channel `τ ↦ (Tr_F τ) ⊗ (I_F/d)` is a **uniform
mixed-unitary average** over the depolarizing `1`-design `{I_E ⊗ Uⱼ}`
(`OrthonormalBasis.sum_conjStarAlgEquiv_congrIsometry_depolarizingUnitary`, N&C Ex 11.19). Feeding
this average into the mixed-unitary monotonicity of the quantum relative entropy
(`ContinuousLinearMap.quantumRelativeEntropy_sum_conjStarAlgEquiv_le`) gives

`D((Tr_F ρ) ⊗ I/d ‖ (Tr_F σ) ⊗ I/d) ≤ D(ρ ‖ σ)`.

The common maximally-mixed factor `I_F/d` is then cancelled by
`ContinuousLinearMap.quantumRelativeEntropy_mapL_right_eq` — `D(A ⊗ M ‖ B ⊗ M) = D(A ‖ B)` for a
shared strictly-positive density operator `M` — leaving `D(Tr_F ρ ‖ Tr_F σ)`. This cancellation
requires the reduced operators to be strictly positive
(`IsStrictlyPositive.of_partialTraceRight_eq`) but **not** normalized, and `I_F/d` to be a
strictly-positive density operator (`ContinuousLinearMap.isDensityOp_finrank_inv_smul_one`,
`ContinuousLinearMap.isStrictlyPositive_finrank_inv_smul_one`). Cancelling the factor this way — via
`quantumRelativeEntropy_mapL_right_eq` rather than the density-operator tensor additivity — is what
lets the density-operator hypothesis on `ρ, σ` be dropped, so that the strictly-positive but
un-normalized identity shift `ρ + ε • 1` can later be pushed through this bound.

## Main results

* `ContinuousLinearMap.quantumRelativeEntropy_mapL_right_eq` — tensoring both arguments with a
  common strictly-positive density operator leaves the relative entropy unchanged,
  `D(A ⊗ M ‖ B ⊗ M) = D(A ‖ B)` (the tensor split behind the twirl, off density operators).
* `ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le_of_isStrictlyPositive` —
  monotonicity under the right partial trace for strictly positive (not necessarily normalized)
  operators; the twirl proof with the tensor split above in place of tensor additivity.
* `ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le_of_hasSupportLE` — monotonicity
  on N&C's own **finite branch**, the support condition `HasSupportLE ρ σ` (`supp ρ ⊆ supp σ`), with
  **no** strict positivity; the faithful form of the theorem, obtained from the strictly-positive
  base by the identity-shift perturbation `ρ + ε • 1` and the limit `ε → 0⁺`.
* `ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le` — its density-operator
  specialization (the form used for states).
-/

@[expose] public section

open Module InnerProductSpace
open scoped TensorProduct Topology

namespace ContinuousLinearMap

variable {ι E F : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- **Tensoring both arguments with a common density operator leaves the relative entropy
unchanged.** For strictly positive operators `A, B : E →L[ℂ] E` and a strictly positive density
operator `M : F →L[ℂ] F`,

`D(A ⊗ M ‖ B ⊗ M) = D(A ‖ B)`.

Unlike `IsDensityOp.quantumRelativeEntropy_tensorMap`, `A` and `B` need **not** be density operators
(no normalization) — only strict positivity, so that `IsSelfAdjoint.cfc_log_tensorMap` applies. The
operator logarithm of each tensor splits as `log(A ⊗ M) = log A ⊗ I + I ⊗ log M`; the shared
`I ⊗ log M` term cancels in the difference `log(A ⊗ M) - log(B ⊗ M)`, and `trace_mapL_comp_mapL`
factors the remaining traces, with the maximally-mixed factor's `tr M = 1`
(`IsDensityOp.trace_eq_one`) absorbing the right tensor slot. This is the tensor split behind the
partial-trace twirl, generalized
off density operators so that the `ε`-shifted operators `ρ + ε • 1` (strictly positive, not
normalized) may be fed through it. -/
theorem quantumRelativeEntropy_mapL_right_eq {A B : E →L[ℂ] E} {M : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B)
    (hM : M.IsDensityOp) (hMs : IsStrictlyPositive M) :
    quantumRelativeEntropy (TensorProduct.mapL A M) (TensorProduct.mapL B M) =
      quantumRelativeEntropy A B := by
  have h_log_A : cfc Real.log (TensorProduct.mapL A M) =
      TensorProduct.mapL (cfc Real.log A) (1 : F →L[ℂ] F) +
        TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log M) :=
    IsSelfAdjoint.cfc_log_tensorMap hA.isSelfAdjoint hMs.isSelfAdjoint
      rfl rfl (fun i => hA.eigenvalues_pos _ rfl i) (fun j => hMs.eigenvalues_pos _ rfl j)
  have h_log_B : cfc Real.log (TensorProduct.mapL B M) =
      TensorProduct.mapL (cfc Real.log B) (1 : F →L[ℂ] F) +
        TensorProduct.mapL (1 : E →L[ℂ] E) (cfc Real.log M) :=
    IsSelfAdjoint.cfc_log_tensorMap hB.isSelfAdjoint hMs.isSelfAdjoint
      rfl rfl (fun i => hB.eigenvalues_pos _ rfl i) (fun j => hMs.eigenvalues_pos _ rfl j)
  simp only [quantumRelativeEntropy_def, h_log_A, h_log_B, ContinuousLinearMap.toLinearMap_add,
    LinearMap.add_comp, map_add, trace_mapL_comp_mapL, ContinuousLinearMap.toLinearMap_one,
    Module.End.one_eq_id, LinearMap.id_comp, hM.trace_eq_one, mul_one]
  ring

/-- **Monotonicity of the quantum relative entropy under the right partial trace, off density
operators** (Nielsen & Chuang, Theorem 11.17). For strictly positive operators
`ρ, σ : E ⊗ F →L[ℂ] E ⊗ F` (not necessarily normalized) and an orthonormal basis `b` of `F`,

`D(Tr_F ρ ‖ Tr_F σ) ≤ D(ρ ‖ σ)`.

The completely depolarizing partial-trace channel is a uniform mixed-unitary average over the
depolarizing `1`-design `{I_E ⊗ Uⱼ}` (N&C Ex 11.19), so this is an instance of the mixed-unitary
data-processing inequality for the relative entropy, after cancelling the maximally mixed `I_F/d`
factor by the common-right-factor identity `quantumRelativeEntropy_mapL_right_eq`. Dropping the
density-operator hypothesis (only strict positivity remains) is what lets the identity-shift
perturbation `ρ + ε • 1` — strictly positive but not normalized — pass through this bound in
`quantumRelativeEntropy_partialTraceRight_le_of_hasSupportLE`; the density-operator form is the
one-line corollary `quantumRelativeEntropy_partialTraceRight_le`. -/
theorem quantumRelativeEntropy_partialTraceRight_le_of_isStrictlyPositive
    (b : OrthonormalBasis ι ℂ F)
    {ρ σ : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)}
    (hρs : IsStrictlyPositive ρ) (hσs : IsStrictlyPositive σ) :
    (LinearMap.toContinuousLinearMap
          (LinearMap.partialTraceRight b (ρ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F))).quantumRelativeEntropy
        (LinearMap.toContinuousLinearMap
          (LinearMap.partialTraceRight b (σ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)))
      ≤ ρ.quantumRelativeEntropy σ := by
  classical
  -- `F` is nontrivial (its orthonormal basis is indexed by the nonempty `ι`), so `I_F/d` is a
  -- genuine density operator.
  have hFpos : 0 < Module.finrank ℂ F := by
    rw [Module.finrank_eq_card_basis b.toBasis]; exact Fintype.card_pos
  have : Nontrivial F := Module.nontrivial_of_finrank_pos hFpos
  -- The real–complex scalar tower on the operator algebra, needed by the mixed-unitary DPI.
  have : NormedSpace ℝ ((E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) := NormedSpace.complexToReal
  have : IsScalarTower ℝ ℂ ((E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  -- The uniform probability weight over the `2^d · d!` depolarizing unitaries.
  set w : (ι → Bool) × Equiv.Perm ι → ℝ :=
    fun _ => ((2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι).factorial : ℝ))⁻¹ with hw
  have hden_ne : ((2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι).factorial : ℝ)) ≠ 0 := by
    positivity
  have hcardκ : Fintype.card ((ι → Bool) × Equiv.Perm ι) =
      2 ^ Fintype.card ι * (Fintype.card ι).factorial := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_perm, Fintype.card_bool]
  have hcardκ_real : (Fintype.card ((ι → Bool) × Equiv.Perm ι) : ℝ) =
      (2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι).factorial : ℝ) := by
    rw [hcardκ]; push_cast; ring
  have hwsum : ∑ p : (ι → Bool) × Equiv.Perm ι, w p = 1 := by
    rw [hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardκ_real,
      mul_inv_cancel₀ hden_ne]
  have hw0 : ∀ p ∈ (Finset.univ : Finset ((ι → Bool) × Equiv.Perm ι)), 0 ≤ w p := by
    intro p _; rw [hw]; positivity
  -- The twirl bridge: the (real-weighted) uniform average of the `I_E ⊗ Uⱼ`-twirls of `τ` equals
  -- the `E`-marginal of `τ` tensored with the maximally mixed state `I_F/d`.
  have hbridge : ∀ τ : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F),
      ∑ p : (ι → Bool) × Equiv.Perm ι,
          w p • (TensorProduct.congrIsometry (.refl ℂ E)
            (b.depolarizingUnitary p)).conjStarAlgEquiv τ
        = TensorProduct.mapL
            (LinearMap.toContinuousLinearMap
              (LinearMap.partialTraceRight b (τ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)))
            ((Fintype.card ι : ℂ)⁻¹ • 1) := by
    intro τ
    rw [← b.sum_conjStarAlgEquiv_congrIsometry_depolarizingUnitary τ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw, ← Complex.coe_smul]
    congr 1
    push_cast
    ring
  -- Apply the mixed-unitary data-processing inequality, then rewrite both averages by the bridge.
  have hDPI := ContinuousLinearMap.quantumRelativeEntropy_sum_conjStarAlgEquiv_le
    (Finset.univ : Finset ((ι → Bool) × Equiv.Perm ι))
    (fun p => TensorProduct.congrIsometry (.refl ℂ E) (b.depolarizingUnitary p))
    hρs hσs hw0 hwsum
  simp only [hbridge] at hDPI
  -- The maximally mixed factor `I_F/d` and the reduced operators are strictly positive.
  set M : F →L[ℂ] F := (Fintype.card ι : ℂ)⁻¹ • 1 with hM
  have hcard : (Module.finrank ℂ F : ℂ) = (Fintype.card ι : ℂ) := by
    rw [Module.finrank_eq_card_basis b.toBasis]
  have hMeq : M = (Module.finrank ℂ F : ℂ)⁻¹ • 1 := by rw [hM, hcard]
  have hMd : M.IsDensityOp := by rw [hMeq]; exact isDensityOp_finrank_inv_smul_one
  have hMs : IsStrictlyPositive M := by rw [hMeq]; exact isStrictlyPositive_finrank_inv_smul_one
  set A₁ := LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
    (ρ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)) with hA₁
  set A₂ := LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
    (σ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)) with hA₂
  have hA₁s : IsStrictlyPositive A₁ :=
    IsStrictlyPositive.of_partialTraceRight_eq hρs b
      (by rw [hA₁, LinearMap.coe_toContinuousLinearMap])
  have hA₂s : IsStrictlyPositive A₂ :=
    IsStrictlyPositive.of_partialTraceRight_eq hσs b
      (by rw [hA₂, LinearMap.coe_toContinuousLinearMap])
  -- Cancel the common maximally mixed factor `I_F/d` (no normalization of the reduced operators
  -- needed): `D(A₁ ⊗ M ‖ A₂ ⊗ M) = D(A₁ ‖ A₂)`.
  rw [quantumRelativeEntropy_mapL_right_eq hA₁s hA₂s hMd hMs] at hDPI
  exact hDPI

/-- **Monotonicity of the quantum relative entropy under the right partial trace** (Nielsen &
Chuang, Theorem 11.17), density-operator form. The strict-positivity theorem
`quantumRelativeEntropy_partialTraceRight_le_of_isStrictlyPositive` does not use normalization, so
the `IsDensityOp` hypotheses are only along for the ride; this form is retained because it is the
one used for states (`AxQM.State.quantumRelativeEntropy_reduced_le`). -/
theorem quantumRelativeEntropy_partialTraceRight_le (b : OrthonormalBasis ι ℂ F)
    {ρ σ : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)}
    (_hρ : ρ.IsDensityOp) (_hσ : σ.IsDensityOp)
    (hρs : IsStrictlyPositive ρ) (hσs : IsStrictlyPositive σ) :
    (LinearMap.toContinuousLinearMap
          (LinearMap.partialTraceRight b (ρ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F))).quantumRelativeEntropy
        (LinearMap.toContinuousLinearMap
          (LinearMap.partialTraceRight b (σ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)))
      ≤ ρ.quantumRelativeEntropy σ :=
  quantumRelativeEntropy_partialTraceRight_le_of_isStrictlyPositive b hρs hσs

/-- **Monotonicity of the quantum relative entropy under the right partial trace on the support
condition** (Nielsen & Chuang, Theorem 11.17), the faithful finite branch. For positive operators
`ρ, σ : E ⊗ F →L[ℂ] E ⊗ F` with the support condition `HasSupportLE ρ σ` (`supp ρ ⊆ supp σ`, on
which the real-valued `cfc`-based relative entropy agrees with the true relative entropy) and an
orthonormal basis `b` of `F`,

`D(Tr_F ρ ‖ Tr_F σ) ≤ D(ρ ‖ σ)`.

This drops the strict-positivity hypothesis of
`quantumRelativeEntropy_partialTraceRight_le_of_isStrictlyPositive` down to N&C's own **finite
branch**, matching the faithful form of the joint-convexity engine this route rests on
(`quantumRelativeEntropy_jointly_convex_of_hasSupportLE`, N&C Theorem 11.12): the strict-positivity
form becomes the special case where both operators are full-rank.

The proof is the identity-shift regularization that removes faithfulness throughout this route: for
`ε > 0` shift both operators by `ε • 1` (strictly positive by `isStrictlyPositive_add_smul_one`,
since `ρ, σ ≥ 0`), apply the strictly-positive monotonicity to the shifted pair, and pass to the
limit `ε → 0⁺` via `tendsto_quantumRelativeEntropy_add_smul_one` on both sides. The `E ⊗ F` side is
shifted by `ε` directly; the marginal side is shifted by `d · ε` (`d = dim F`), because tracing out
`F` sends the shift `ε • 1_{E⊗F}` to `ε • (Tr_F 1) = (ε d) • 1_E` — `Tr_F 1 = (tr 1_F) • 1_E`
`= d • 1_E` by `partialTraceRight_tensorMap` on `1 = 1 ⊗ 1` — and since `d > 0` the reparametrized
shift `ε ↦ d ε` still runs to `0⁺`. The marginal support condition `(Tr_F ρ).HasSupportLE (Tr_F σ)`
is `HasSupportLE.of_partialTraceRight`, and the marginals are self-adjoint as `F`-marginals of
positive operators (`LinearMap.partialTraceRight_isPositive`). -/
theorem quantumRelativeEntropy_partialTraceRight_le_of_hasSupportLE
    (b : OrthonormalBasis ι ℂ F)
    {ρ σ : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hsupp : ρ.HasSupportLE σ) :
    (LinearMap.toContinuousLinearMap
          (LinearMap.partialTraceRight b (ρ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F))).quantumRelativeEntropy
        (LinearMap.toContinuousLinearMap
          (LinearMap.partialTraceRight b (σ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)))
      ≤ ρ.quantumRelativeEntropy σ := by
  classical
  -- `F` is nontrivial (its orthonormal basis is indexed by the nonempty `ι`), so `d = dim F > 0`.
  have hFpos : 0 < Module.finrank ℂ F := by
    rw [Module.finrank_eq_card_basis b.toBasis]; exact Fintype.card_pos
  have : Nontrivial F := Module.nontrivial_of_finrank_pos hFpos
  set dℝ : ℝ := (Module.finrank ℂ F : ℝ) with hdℝ
  have hdpos : (0 : ℝ) < dℝ := by rw [hdℝ]; exact_mod_cast hFpos
  -- The two `A`-marginals `Tr_F ρ`, `Tr_F σ` (as they appear in the goal).
  set X' : E →L[ℂ] E := LinearMap.toContinuousLinearMap
    (LinearMap.partialTraceRight b (ρ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)) with hX'
  set Y' : E →L[ℂ] E := LinearMap.toContinuousLinearMap
    (LinearMap.partialTraceRight b (σ : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)) with hY'
  -- The marginals are positive (`F`-marginal of a positive operator), hence self-adjoint.
  have hX'pos : X'.IsPositive := by
    rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, hX', LinearMap.coe_toContinuousLinearMap]
    exact LinearMap.partialTraceRight_isPositive b hρ.toLinearMap
  have hY'pos : Y'.IsPositive := by
    rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, hY', LinearMap.coe_toContinuousLinearMap]
    exact LinearMap.partialTraceRight_isPositive b hσ.toLinearMap
  -- The marginal support condition descends from the full one.
  have hsuppM : X'.HasSupportLE Y' :=
    HasSupportLE.of_partialTraceRight ((ContinuousLinearMap.nonneg_iff_isPositive (f := σ)).mpr
        hσ) hsupp b
      (by rw [hX', LinearMap.coe_toContinuousLinearMap])
      (by rw [hY', LinearMap.coe_toContinuousLinearMap])
  -- `partialTraceRight` is additive and `ℂ`-linear.
  have hlin : ∀ (S T : (E ⊗[ℂ] F) →ₗ[ℂ] E ⊗[ℂ] F) (c : ℂ),
      LinearMap.partialTraceRight b (S + c • T)
        = LinearMap.partialTraceRight b S + c • LinearMap.partialTraceRight b T := by
    intro S T c
    rw [← LinearMap.partialTraceRightLM_apply, map_add, map_smul,
      LinearMap.partialTraceRightLM_apply, LinearMap.partialTraceRightLM_apply]
  -- Tracing out `F` sends the identity shift `ε • 1` on `E ⊗ F` to the shift `(d ε) • 1` on `E`
  -- (`Tr_F 1 = (tr 1_F) • 1_E = d • 1_E`, `partialTraceRight_tensorMap` on `1 = 1 ⊗ 1`).
  have hmarg : ∀ (T : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) (ε : ℝ),
      LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
          ((T + (ε : ℂ) • 1 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F))
        = LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
            (T : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)) + ((dℝ * ε : ℝ) : ℂ) • 1 := by
    intro T ε
    have hsc : ((dℝ * ε : ℝ) : ℂ) = (ε : ℂ) * (Module.finrank ℂ F : ℂ) := by
      rw [hdℝ]; push_cast; ring
    apply ContinuousLinearMap.coe_injective
    simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_one, LinearMap.coe_toContinuousLinearMap]
    rw [hlin, LinearMap.partialTraceRight_one, smul_smul, hsc]
  have hmargρ : ∀ ε : ℝ, LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
        ((ρ + (ε : ℂ) • 1 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F))
      = X' + ((dℝ * ε : ℝ) : ℂ) • 1 := fun ε => by rw [hmarg ρ ε, ← hX']
  have hmargσ : ∀ ε : ℝ, LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
        ((σ + (ε : ℂ) • 1 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F))
      = Y' + ((dℝ * ε : ℝ) : ℂ) • 1 := fun ε => by rw [hmarg σ ε, ← hY']
  -- The reparametrization `ε ↦ d ε` still runs to `0⁺`.
  have hg_tendsto : Filter.Tendsto (fun ε : ℝ => dℝ * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Filter.Tendsto (fun ε : ℝ => dℝ * ε) (𝓝 (0 : ℝ)) (𝓝 (dℝ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [Set.mem_Ioi] at hε ⊢
      exact mul_pos hdpos hε
  -- The identity-shift continuity engine on the marginal space, reparametrized by `ε ↦ d ε`.
  have hXY : Filter.Tendsto
      (fun η : ℝ => quantumRelativeEntropy (X' + (η : ℂ) • 1) (Y' + (η : ℂ) • 1)) (𝓝[>] 0)
      (𝓝 (quantumRelativeEntropy X' Y')) :=
    tendsto_quantumRelativeEntropy_add_smul_one hX'pos.isSelfAdjoint hY'pos.isSelfAdjoint hsuppM
  -- Left-hand limit: `D(Tr_F(ρ + ε•1) ‖ Tr_F(σ + ε•1)) → D(Tr_F ρ ‖ Tr_F σ)` as `ε → 0⁺`.
  have hf : Filter.Tendsto (fun ε : ℝ => quantumRelativeEntropy
        (LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
          ((ρ + (ε : ℂ) • 1 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)))
        (LinearMap.toContinuousLinearMap (LinearMap.partialTraceRight b
          ((σ + (ε : ℂ) • 1 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F))))
      (𝓝[>] 0) (𝓝 (quantumRelativeEntropy X' Y')) := by
    refine (hXY.comp hg_tendsto).congr (fun ε => ?_)
    simp only [Function.comp_apply]
    rw [hmargρ ε, hmargσ ε]
  -- Right-hand limit: `D(ρ + ε•1 ‖ σ + ε•1) → D(ρ ‖ σ)` as `ε → 0⁺`.
  have hg : Filter.Tendsto (fun ε : ℝ => quantumRelativeEntropy (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1))
      (𝓝[>] 0) (𝓝 (quantumRelativeEntropy ρ σ)) :=
    tendsto_quantumRelativeEntropy_add_smul_one hρ.isSelfAdjoint hσ.isSelfAdjoint hsupp
  -- For every `ε > 0` the identity shift is strictly positive, so the strictly-positive
  -- monotonicity applies to the shifted pair.
  have hshift_pos : ∀ (T : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) (ε : ℝ), T.IsPositive → 0 < ε →
      IsStrictlyPositive (T + (ε : ℂ) • 1) := fun T ε hT hε => by
    rw [Complex.coe_smul]
    exact isStrictlyPositive_add_smul_one ((nonneg_iff_isPositive (f := T)).mpr hT) hε
  refine le_of_tendsto_of_tendsto hf hg ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Set.mem_Ioi] at hε
  exact quantumRelativeEntropy_partialTraceRight_le_of_isStrictlyPositive b
    (hshift_pos ρ ε hρ hε) (hshift_pos σ ε hσ hε)

end ContinuousLinearMap
