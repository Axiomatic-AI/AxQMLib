/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.Spectrum
import ToMathlib.Analysis.InnerProductSpace.RankOneSum

/-!
# AxQM — the pseudo-inverse `ρ⁻¹` of a density operator

Nielsen & Chuang, in Exercise 2.73, use the operator `ρ⁻¹` *"defined to be the inverse of `ρ`,
when `ρ` is considered as an operator acting only on the support of `ρ`"* — the support being the
span of the eigenvectors of `ρ` with non-zero eigenvalues. Because a density operator need not be
invertible on the whole space (it can have a kernel), this restricted inverse is the standard
**Moore–Penrose pseudo-inverse** of `ρ`.

We build it from the spectral decomposition of the (self-adjoint, positive) density operator
`ρ = ∑ₖ λₖ |bₖ⟩⟨bₖ|` over its orthonormal eigenbasis `bₖ` (Mathlib's
`LinearMap.IsSymmetric.eigenvectorBasis` / `eigenvalues`, the same machinery behind the
eigenensemble `Ensemble.ofState`). The pseudo-inverse inverts each non-zero eigenvalue and sends
the kernel (zero eigenvalues) to zero:
`ρ⁻¹ = ∑ₖ λₖ⁻¹ |bₖ⟩⟨bₖ|`,
using the real field inverse `(·)⁻¹ : ℝ → ℝ`, which is `x⁻¹` on `x ≠ 0` and `0` at `0` (Lean's
`GroupWithZero` convention), so the zero eigenvalues contribute nothing — exactly the "on the
support" restriction.

## Main definitions

* `AxQM.State.pseudoInverse` — the pseudo-inverse `ρ⁻¹`.

## Main results

* `State.pseudoInverse_apply` — the vector form `ρ⁻¹ v = ∑ₖ λₖ⁻¹ ⟪bₖ, v⟫ bₖ`.
* `State.pseudoInverse_apply_eigenvectorBasis` — the spectral action `ρ⁻¹ bⱼ = λⱼ⁻¹ bⱼ`.
* `State.op_apply_eigenvectorBasis` — the `ρ`-side companion `ρ bⱼ = λⱼ bⱼ` (shared by the proofs
  below).
* `State.isSelfAdjoint_pseudoInverse` — `ρ⁻¹` is self-adjoint.
* `State.op_comp_pseudoInverse_comp_op` — the Moore–Penrose / "inverse on the support" identity
  `ρ ρ⁻¹ ρ = ρ`.
* `State.pseudoInverse_comp_op_comp_pseudoInverse` — the dual identity `ρ⁻¹ ρ ρ⁻¹ = ρ⁻¹`.
-/

open scoped InnerProductSpace
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **The pseudo-inverse `ρ⁻¹` of a density operator** (Nielsen–Chuang Exercise 2.73): the inverse
of `ρ` on its support, extended by zero on the kernel. Built from the spectral decomposition
`ρ = ∑ₖ λₖ |bₖ⟩⟨bₖ|` over the orthonormal eigenbasis `bₖ` by inverting each eigenvalue with the real
field inverse (so a zero eigenvalue stays `0`): `ρ⁻¹ = ∑ₖ λₖ⁻¹ |bₖ⟩⟨bₖ|`. -/
def pseudoInverse (ρ : State S) : S.space →L[ℂ] S.space :=
  ∑ k, (((ρ.isDensity.isSymmetric.eigenvalues rfl k)⁻¹ : ℝ) : ℂ) •
    rankOne ℂ (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k)
      (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k)

/-- **Vector form of the pseudo-inverse**: `ρ⁻¹ v = ∑ₖ λₖ⁻¹ ⟪bₖ, v⟫ bₖ`, the spectral expansion of
`ρ⁻¹` (compare `LinearMap.IsSymmetric.spectral_sum_apply` for `ρ` itself). -/
theorem pseudoInverse_apply (ρ : State S) (v : S.space) :
    ρ.pseudoInverse v =
      ∑ k, (((ρ.isDensity.isSymmetric.eigenvalues rfl k)⁻¹ : ℝ) : ℂ) •
        (inner ℂ (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k) v •
          ρ.isDensity.isSymmetric.eigenvectorBasis rfl k) := by
  rw [pseudoInverse, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, rankOne_apply]

/-- **Spectral action of the pseudo-inverse**: `ρ⁻¹ bⱼ = λⱼ⁻¹ bⱼ` on each eigenvector `bⱼ`.
Together with `ρ bⱼ = λⱼ bⱼ` this says `ρ⁻¹` inverts `ρ` eigenvalue-by-eigenvalue, mapping the zero
eigenvalues (the kernel) to `0`. Tagged `@[simp]` as the canonical rewrite target for `ρ⁻¹ bⱼ`. -/
@[simp]
theorem pseudoInverse_apply_eigenvectorBasis (ρ : State S) (j : Fin (Module.finrank ℂ S.space)) :
    ρ.pseudoInverse (ρ.isDensity.isSymmetric.eigenvectorBasis rfl j) =
      (((ρ.isDensity.isSymmetric.eigenvalues rfl j)⁻¹ : ℝ) : ℂ) •
        ρ.isDensity.isSymmetric.eigenvectorBasis rfl j := by
  rw [pseudoInverse_apply, Finset.sum_eq_single j]
  · rw [orthonormal_iff_ite.mp (ρ.isDensity.isSymmetric.eigenvectorBasis rfl).orthonormal j j,
      ite_eq_left rfl, one_smul]
  · intro k _ hk
    rw [orthonormal_iff_ite.mp (ρ.isDensity.isSymmetric.eigenvectorBasis rfl).orthonormal k j,
      ite_eq_right hk, zero_smul, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Spectral action of `ρ` on its eigenvectors**: `ρ bⱼ = λⱼ bⱼ`. The continuous-linear-map
restatement of Mathlib's `LinearMap.IsSymmetric.apply_eigenvectorBasis` for a density operator
(bridging CLM application to the `LinearMap`-level lemma by definitional unfolding). The `ρ`-side
mirror of `pseudoInverse_apply_eigenvectorBasis`; shared by the Moore–Penrose proofs below. -/
theorem op_apply_eigenvectorBasis (ρ : State S) (j : Fin (Module.finrank ℂ S.space)) :
    ρ.op (ρ.isDensity.isSymmetric.eigenvectorBasis rfl j) =
      (ρ.isDensity.isSymmetric.eigenvalues rfl j : ℂ) •
        ρ.isDensity.isSymmetric.eigenvectorBasis rfl j :=
  ρ.isDensity.isSymmetric.apply_eigenvectorBasis rfl j

/-- The **canonical orthonormal eigenbasis** of a state's density operator: the eigenvector basis of
the self-adjoint (symmetric) operator `ρ.op`, indexed by `Fin (dim S.space)`. The named form of
`ρ.isDensity.isSymmetric.eigenvectorBasis rfl`, whose eigenvalues are
`ρ.isDensity.isSymmetric.eigenvalues rfl` (`= State.eigenvalueDist`). Adopted by `ρ`-spectral
developments (`op_apply_eigenbasis` below, and the majorization module). -/
def eigenbasis (ρ : State S) :
    OrthonormalBasis (Fin (Module.finrank ℂ S.space)) ℂ S.space :=
  ρ.isDensity.isSymmetric.eigenvectorBasis rfl

/-- **Spectral action on the eigenbasis**: `ρ (bⱼ) = λⱼ • bⱼ`, with `bⱼ = ρ.eigenbasis j` and
`λⱼ = ρ.isDensity.isSymmetric.eigenvalues rfl j` (`= ρ.eigenvalueDist j`). The `State.eigenbasis`
phrasing of `op_apply_eigenvectorBasis`. -/
theorem op_apply_eigenbasis (ρ : State S) (j : Fin (Module.finrank ℂ S.space)) :
    ρ.op (ρ.eigenbasis j) = (ρ.isDensity.isSymmetric.eigenvalues rfl j : ℂ) • ρ.eigenbasis j :=
  ρ.op_apply_eigenvectorBasis j

/-- The eigenbasis vectors are orthonormal: `⟪bₖ, bₖ⟫ = 1`. -/
theorem inner_eigenbasis_self (ρ : State S) (k : Fin (Module.finrank ℂ S.space)) :
    inner ℂ (ρ.eigenbasis k) (ρ.eigenbasis k) = 1 := by
  rw [orthonormal_iff_ite.mp ρ.eigenbasis.orthonormal k k]
  simp

/-- Each eigenbasis vector is a unit vector: `‖bₖ‖ = 1`. -/
theorem norm_eigenbasis (ρ : State S) (k : Fin (Module.finrank ℂ S.space)) :
    ‖ρ.eigenbasis k‖ = 1 :=
  ρ.eigenbasis.orthonormal.1 k

/-- **The pseudo-inverse is self-adjoint.** Each summand `λₖ⁻¹ |bₖ⟩⟨bₖ|` is a real scalar times the
self-adjoint rank-one projector `|bₖ⟩⟨bₖ|`, and a sum of self-adjoint operators is self-adjoint. -/
theorem isSelfAdjoint_pseudoInverse (ρ : State S) : IsSelfAdjoint ρ.pseudoInverse := by
  rw [pseudoInverse]
  refine isSelfAdjoint_sum Finset.univ fun k _ => ?_
  rw [Complex.coe_smul]
  refine (IsSelfAdjoint.all _).smul ?_
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- **The pseudo-inverse inverts `ρ` on its support** (Nielsen–Chuang Exercise 2.73): the
Moore–Penrose identity `ρ ρ⁻¹ ρ = ρ`. On each eigenvector `bⱼ` the composite scales by
`λⱼ · λⱼ⁻¹ · λⱼ = λⱼ` (equal to `λⱼ` whether or not `λⱼ = 0`), so it agrees with `ρ` on the
eigenbasis — the precise sense in which `ρ⁻¹` is the inverse of `ρ` on the support. -/
theorem op_comp_pseudoInverse_comp_op (ρ : State S) :
    ρ.op.comp (ρ.pseudoInverse.comp ρ.op) = ρ.op := by
  refine ContinuousLinearMap.coe_injective
    ((ρ.isDensity.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun j => ?_)
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, op_apply_eigenvectorBasis, map_smul,
    pseudoInverse_apply_eigenvectorBasis, smul_smul]
  congr 1
  rw [Complex.ofReal_inv, mul_inv_mul_cancel]

/-- **The dual Moore–Penrose identity `ρ⁻¹ ρ ρ⁻¹ = ρ⁻¹`.** On each eigenvector `bⱼ` the composite
scales by `λⱼ⁻¹ · λⱼ · λⱼ⁻¹ = λⱼ⁻¹` (equal whether or not `λⱼ = 0`), so it agrees with `ρ⁻¹`. -/
theorem pseudoInverse_comp_op_comp_pseudoInverse (ρ : State S) :
    ρ.pseudoInverse.comp (ρ.op.comp ρ.pseudoInverse) = ρ.pseudoInverse := by
  refine ContinuousLinearMap.coe_injective
    ((ρ.isDensity.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun j => ?_)
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, pseudoInverse_apply_eigenvectorBasis, map_smul,
    op_apply_eigenvectorBasis, smul_smul]
  congr 1
  simpa [Complex.ofReal_inv] using
    mul_inv_mul_cancel (ρ.isDensity.isSymmetric.eigenvalues rfl j : ℂ)⁻¹

end State

end AxQM
