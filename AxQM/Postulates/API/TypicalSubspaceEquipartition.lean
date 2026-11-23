/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TypicalSubspace
import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# The equipartition operator bound of the typical subspace (N&C Thm 12.5 / HSW eq. (12.82))

The **maximum-eigenvalue half** of Nielsen & Chuang's asymptotic equipartition property for the
ε-typical subspace of `ρ^⊗n`.  Where `Postulates.API.TypicalSubspace` records the *total mass* and
*dimension* of the typical subspace `T(n, ε)`, this file records how *small* the eigenvalues of
`ρ^⊗n` are **on** that subspace: writing `P = P(n, ε)` for the ε-typical subspace projector and
`S = S(ρ)` for the von Neumann entropy, the compression of `ρ^⊗n` to the typical subspace is bounded
above in the Loewner order by the exponentially small scalar `exp(-n (S - ε))`:

`P ρ^⊗n P  ≤  exp(-n (S - ε)) · 1`   (Nielsen & Chuang, the operator inequality used at eq. (12.82),
in nats — N&C's base-`2` `P σ̄^⊗n P ≤ 2^{-n(S(σ̄)-ε)} I`).

This is exactly the ingredient the achievability half of the **HSW theorem** (`χ(E) = C⁽¹⁾(E)`,
Theorem 12.8) uses to control the "false-decoding" term of the random-coding error estimate: with
`σ̄ = ∑ⱼ pⱼ E(ρⱼ)` the average channel output and `P` its ε-typical projector,
`tr(P σ̄^⊗n P · Πⱼ) ≤ exp(-n(S(σ̄)-ε)) · tr(Πⱼ)`, feeding the exponential decay of eq. (12.82).

## What this file provides

* `AxQM.State.prod_eigenvalueDist_le_of_mem_typicalSeq` — the underlying **scalar**
  equipartition bound: an ε-typical index sequence `κ` has product eigenvalue
  `∏ᵢ λ(κᵢ) ≤ exp(-n (S(ρ) - ε))`.  A restatement of the classical multiplicative typicality bound
  (`Real.mem_typicalSeq`) through the entropy bridge `H(λ) = S(ρ)`.

* `AxQM.State.typicalSubspaceProj_comp_tensorPow_op_comp_le` — the **operator** bound
  `P ρ^⊗n P ≤ exp(-n (S(ρ) - ε)) · 1`.  The proof diagonalises: since `ρ^⊗n` is diagonal in the
  product eigenbasis `|e_κ⟩` with eigenvalue `∏ᵢ λ(κᵢ)` (`tensorPow_op_apply_tensorPowEigenbasis`)
  and `P = ∑_{κ ∈ T(n,ε)} |e_κ⟩⟨e_κ|` (`orthonormalProjector_eq_sum`), the sandwich collapses to
  `P ρ^⊗n P = ∑_{κ ∈ T(n,ε)} (∏ᵢ λ(κᵢ)) |e_κ⟩⟨e_κ|` (via `comp_rankOne`), whence
  `exp(-n(S-ε))·P − P ρ^⊗n P = ∑_{κ ∈ T(n,ε)} (exp(-n(S-ε)) − ∏ᵢ λ(κᵢ)) |e_κ⟩⟨e_κ|` is a sum of
  positive operators (each scalar is `≥ 0` by the scalar bound above), giving `P ρ^⊗n P ≤ c·P`; and
  `c·P ≤ c·1` because `P ≤ 1` (`IsStarProjection.le_one`) and `c ≥ 0`.
-/

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The scalar equipartition bound** (Nielsen & Chuang, Theorem 12.5 / the multiplicative form of
Eq. 12.41): an ε-typical index sequence `κ ∈ T(n, ε)` of eigenvalue indices has product eigenvalue
`∏ᵢ λ(κᵢ) ≤ exp(-n (S(ρ) - ε))` (in nats).  Immediate from the classical multiplicative typicality
bound `Real.mem_typicalSeq` for `λ = ρ.eigenvalueDist`, rewriting the Shannon entropy `H(λ)` to the
von Neumann entropy `S(ρ)` via the entropy bridge `vonNeumannEntropy_eq_entropy_eigenvalueDist`. -/
theorem State.prod_eigenvalueDist_le_of_mem_typicalSeq (ρ : State S) {n : ℕ} {ε : ℝ}
    {κ : Fin n → Fin (Module.finrank ℂ S.space)}
    (hκ : κ ∈ Real.typicalSeq ρ.eigenvalueDist n ε) :
    ∏ i, ρ.eigenvalueDist (κ i) ≤ Real.exp (-(n : ℝ) * (ρ.vonNeumannEntropy - ε)) := by
  rw [ρ.vonNeumannEntropy_eq_entropy_eigenvalueDist]
  exact (Real.mem_typicalSeq.mp hκ).2

/-- **The equipartition operator bound** (Nielsen & Chuang, Theorem 12.5 / the operator inequality
used at Eq. 12.82): the compression of `ρ^⊗n` to its ε-typical subspace is bounded above in the
Loewner order by the exponentially small scalar `exp(-n (S(ρ) - ε))`,

`P(n, ε) · ρ^⊗n · P(n, ε)  ≤  exp(-n (S(ρ) - ε)) · 1`

(in nats; N&C's base-`2` `P σ̄^⊗n P ≤ 2^{-n(S(σ̄)-ε)} I`).  This is the maximum-eigenvalue half of
the asymptotic equipartition property, the ingredient the HSW achievability argument uses to make
the random-coding false-decoding term decay exponentially.

The proof diagonalises in the product eigenbasis `|e_κ⟩` (`ρ.tensorPowEigenbasis n`): `ρ^⊗n` acts on
`|e_κ⟩` with eigenvalue `∏ᵢ λ(κᵢ)` (`tensorPow_op_apply_tensorPowEigenbasis`) and
`P = ∑_{κ ∈ T(n,ε)} |e_κ⟩⟨e_κ|` (`orthonormalProjector_eq_sum`), so the sandwich collapses to
`P ρ^⊗n P = ∑_{κ ∈ T(n,ε)} (∏ᵢ λ(κᵢ)) |e_κ⟩⟨e_κ|`.  Hence
`c·P − P ρ^⊗n P = ∑_{κ ∈ T(n,ε)} (c − ∏ᵢ λ(κᵢ)) |e_κ⟩⟨e_κ|` (`c = exp(-n(S-ε))`) is a nonnegative
combination of rank-one projectors — each coefficient `≥ 0` by the scalar bound
`prod_eigenvalueDist_le_of_mem_typicalSeq` — so `P ρ^⊗n P ≤ c·P`; finally `c·P ≤ c·1` since `P ≤ 1`
(`IsStarProjection.le_one`) and `c ≥ 0`. -/
theorem State.typicalSubspaceProj_comp_tensorPow_op_comp_le (ρ : State S) (n : ℕ) (ε : ℝ) :
    (ρ.typicalSubspaceProj n ε).comp
        ((ρ.tensorPow n).op.comp (ρ.typicalSubspaceProj n ε))
      ≤ (Real.exp (-(n : ℝ) * (ρ.vonNeumannEntropy - ε)) : ℝ) •
          (1 : (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space) := by
  classical
  set c : ℝ := Real.exp (-(n : ℝ) * (ρ.vonNeumannEntropy - ε)) with hc
  set s := Real.typicalSeq ρ.eigenvalueDist n ε with hs
  -- `P = ∑_{κ ∈ T(n,ε)} |e_κ⟩⟨e_κ|`.
  have hP : ρ.typicalSubspaceProj n ε
      = ∑ κ ∈ s, rankOne ℂ (ρ.tensorPowEigenbasis n κ) (ρ.tensorPowEigenbasis n κ) := by
    rw [State.typicalSubspaceProj, orthonormalProjector_eq_sum]
  -- The sandwich collapses to a diagonal sum (complex eigenvalue coefficients).
  have key : (ρ.typicalSubspaceProj n ε).comp
        ((ρ.tensorPow n).op.comp (ρ.typicalSubspaceProj n ε))
      = ∑ κ ∈ s, ((∏ i, ρ.eigenvalueDist (κ i) : ℝ) : ℂ) •
          rankOne ℂ (ρ.tensorPowEigenbasis n κ) (ρ.tensorPowEigenbasis n κ) := by
    have hAP : (ρ.tensorPow n).op.comp (ρ.typicalSubspaceProj n ε)
        = ∑ κ ∈ s, ((∏ i, ρ.eigenvalueDist (κ i) : ℝ) : ℂ) •
            rankOne ℂ (ρ.tensorPowEigenbasis n κ) (ρ.tensorPowEigenbasis n κ) := by
      rw [hP, ContinuousLinearMap.comp_finsetSum]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [InnerProductSpace.comp_rankOne, State.tensorPow_op_apply_tensorPowEigenbasis,
        map_smul, _root_.smul_apply]
      rfl
    rw [hAP, ContinuousLinearMap.comp_finsetSum]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [ContinuousLinearMap.comp_smul, InnerProductSpace.comp_rankOne, State.typicalSubspaceProj,
      orthonormalProjector_apply_eq_ite (ρ.tensorPowEigenbasis n).orthonormal, ite_eq_left hκ]
  -- `P ρ^⊗n P ≤ c·P`, as `c·P − P ρ^⊗n P` is a nonnegative combination of `|e_κ⟩⟨e_κ|`.
  have hstep : (ρ.typicalSubspaceProj n ε).comp
        ((ρ.tensorPow n).op.comp (ρ.typicalSubspaceProj n ε))
      ≤ c • ρ.typicalSubspaceProj n ε := by
    rw [← sub_nonneg, key, hP, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun κ hκ => ?_
    have hle : ∏ i, ρ.eigenvalueDist (κ i) ≤ c :=
      ρ.prod_eigenvalueDist_le_of_mem_typicalSeq hκ
    have hpos : (0 : (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space) ≤
        rankOne ℂ (ρ.tensorPowEigenbasis n κ) (ρ.tensorPowEigenbasis n κ) :=
      ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self _)
    rw [Complex.coe_smul, ← sub_smul]
    exact smul_nonneg (by linarith) hpos
  -- `c·P ≤ c·1`, since `P ≤ 1` and `c ≥ 0`.
  refine hstep.trans ?_
  refine smul_le_smul_of_nonneg_left ?_ (Real.exp_nonneg _)
  rw [State.typicalSubspaceProj]
  exact (isStarProjection_orthonormalProjector (ρ.tensorPowEigenbasis n).orthonormal s).le_one

/-- **The false-decoding decay of the HSW random-coding error estimate** (Nielsen & Chuang,
eq. 12.82): the trace overlap of the equipartition-compressed `P ρ^⊗n P` with *any* positive
operator `Q` decays like the maximal typical eigenvalue,

`re tr(P ρ^⊗n P · Q)  ≤  exp(-n (S(ρ) - ε)) · re tr Q`

(in nats; N&C's base-`2` `tr(P σ̄^⊗n P Q) ≤ 2^{-n(S(σ̄)-ε)} tr Q`).  Immediate from the
equipartition operator bound `P ρ^⊗n P ≤ exp(-n(S-ε)) · 1`
(`typicalSubspaceProj_comp_tensorPow_op_comp_le`) fed
through the scalar trace bound `ContinuousLinearMap.re_trace_mul_le_smul_of_le_smul_one`.  With
`ρ = σ̄ = ∑ⱼ pⱼ E(ρⱼ)` the average channel output and `Q = 𝔼(P₁)` the (expected) conditional-typical
projector, this is exactly the term controlling the false-decoding contribution to the random-coding
average error in the HSW achievability argument. -/
theorem State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le (ρ : State S) (n : ℕ) (ε : ℝ)
    {Q : (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space} (hQ : 0 ≤ Q) :
    RCLike.re (LinearMap.trace ℂ (S ^⊗ₛ n).space
        (((ρ.typicalSubspaceProj n ε).comp
            ((ρ.tensorPow n).op.comp (ρ.typicalSubspaceProj n ε)) * Q : _ →L[ℂ] _) : _ →ₗ[ℂ] _))
      ≤ Real.exp (-(n : ℝ) * (ρ.vonNeumannEntropy - ε)) *
          RCLike.re (LinearMap.trace ℂ (S ^⊗ₛ n).space (Q : _ →ₗ[ℂ] _)) :=
  ContinuousLinearMap.re_trace_mul_le_smul_of_le_smul_one
    (ρ.typicalSubspaceProj_comp_tensorPow_op_comp_le n ε) hQ

/-- The false-decoding decay bound specialised to a positive `Q` whose trace is dimension-bounded:
`re tr(P ρ^⊗n P · Q) ≤ exp(-n(S(ρ)-ε)) · D` whenever `re tr Q ≤ D`.  With `Q = 𝔼(P₁)` and
`D = exp(n(S̄+ε))` the expected conditional-typical dimension bound (N&C eq. 12.77,
`S̄ = ∑ⱼ pⱼ S(σⱼ)`), the two factors combine into the exponent `exp(-n(S(σ̄) - S̄ - 2ε))` of the HSW
error estimate (eq. 12.82). -/
theorem State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le_of_trace_le (ρ : State S) (n : ℕ)
    (ε : ℝ) {Q : (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space} (hQ : 0 ≤ Q) {D : ℝ}
    (hD : RCLike.re (LinearMap.trace ℂ (S ^⊗ₛ n).space (Q : _ →ₗ[ℂ] _)) ≤ D) :
    RCLike.re (LinearMap.trace ℂ (S ^⊗ₛ n).space
        (((ρ.typicalSubspaceProj n ε).comp
            ((ρ.tensorPow n).op.comp (ρ.typicalSubspaceProj n ε)) * Q : _ →L[ℂ] _) : _ →ₗ[ℂ] _))
      ≤ Real.exp (-(n : ℝ) * (ρ.vonNeumannEntropy - ε)) * D :=
  (ρ.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le n ε hQ).trans
    (mul_le_mul_of_nonneg_left hD (Real.exp_nonneg _))

end AxQM
