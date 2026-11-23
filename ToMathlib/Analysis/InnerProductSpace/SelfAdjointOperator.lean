/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Spectrum
public import ToMathlib.Analysis.InnerProductSpace.NormalOperator

/-!
# The spectral theorem for self-adjoint (Hermitian) operators

An operator `T` on a finite-dimensional inner product space is *self-adjoint* (N&C: *Hermitian*)
when it equals its own adjoint. Mathlib spells this with the `IsSelfAdjoint` predicate
(`star T = T`); for `T : E →ₗ[𝕜] E` the `star` is `LinearMap.adjoint`
(`LinearMap.star_eq_adjoint`), so `IsSelfAdjoint T` is exactly `Tᴴ = T`. This file proves the
**spectral theorem** for such operators: `T` is self-adjoint if and only if it is diagonal with
respect to some orthonormal basis *with real eigenvalues*, i.e. there is an orthonormal eigenbasis
whose eigenvalues are real.

This is the Hermitian special case of the spectral theorem for normal operators
(`LinearMap.isStarNormal_iff_exists_orthonormalBasis`, N&C Theorem 2.1 / Box 2.2). The two
distinctive features of the Hermitian case, both of which this file makes explicit, are:

* the eigenvalues are **real** (a family `μ : _ → ℝ`, coerced into `𝕜`), where a general normal
  operator only has scalar eigenvalues in `𝕜`; and
* the whole result holds over **any** `RCLike` field `𝕜` (`ℝ` or `ℂ`), whereas the forward
  direction of the normal spectral theorem genuinely requires `ℂ` (over `ℝ` a rotation is normal
  but not diagonalisable).

Consequently the proof here is a genuine simplification of Box 2.2 (as N&C Exercise 2.21 asks): the
forward direction reads off Mathlib's diagonalisation of a symmetric operator
(`LinearMap.IsSymmetric.eigenvectorBasis` / `eigenvalues` / `apply_eigenvectorBasis`), with real
eigenvalues supplied directly, and needs neither the Cartesian decomposition `T = A + i·B` nor the
induction on `QMQ` used for the normal case. The converse reuses the general fact that the adjoint
of a diagonal operator is diagonal with conjugated eigenvalues
(`LinearMap.adjoint_apply_of_forall_apply_eq_smul`): real eigenvalues are their own conjugates, so
`Tᴴ` and `T` agree on the basis, hence `Tᴴ = T`.

## Main results

* `IsSelfAdjoint.exists_orthonormalBasis_forall_apply_eq_real_smul`: a self-adjoint operator has an
  orthonormal eigenbasis with real eigenvalues (the existence half).
* `LinearMap.isSelfAdjoint_of_forall_apply_eq_real_smul`: an operator that is diagonal in an
  orthonormal basis with real eigenvalues is self-adjoint (the converse half).
* `LinearMap.isSelfAdjoint_iff_exists_orthonormalBasis_real`: the spectral theorem, packaging the
  two halves as an equivalence.
-/

public section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Spectral theorem for self-adjoint operators** (existence half): a self-adjoint operator `T`
on a finite-dimensional inner product space, i.e. one satisfying `IsSelfAdjoint T` (`Tᴴ = T`), is
diagonal with respect to some orthonormal basis with **real** eigenvalues. Concretely, there is an
orthonormal basis `b` and real scalars `μ` with `T (b i) = (μ i : 𝕜) • b i` for all `i`. -/
theorem _root_.IsSelfAdjoint.exists_orthonormalBasis_forall_apply_eq_real_smul
    {T : E →ₗ[𝕜] E} (hT : IsSelfAdjoint T) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E) (μ : Fin (Module.finrank 𝕜 E) → ℝ),
      ∀ i, T (b i) = (μ i : 𝕜) • b i := by
  -- A self-adjoint operator is symmetric, so Mathlib's diagonalisation of symmetric operators
  -- supplies an orthonormal eigenbasis with real eigenvalues directly.
  have hS : T.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint T).2 hT
  exact ⟨hS.eigenvectorBasis rfl, hS.eigenvalues rfl, fun i => hS.apply_eigenvectorBasis rfl i⟩

/-- **Spectral theorem for self-adjoint operators** (converse half): an operator that is diagonal
with respect to some orthonormal basis `b` with **real** eigenvalues `μ` is self-adjoint. If
`T (b i) = (μ i : 𝕜) • b i` for an orthonormal basis `b` and real `μ`, then `Tᴴ = T`, i.e.
`IsSelfAdjoint T`. Reality of the eigenvalues is essential: a diagonal operator with complex
eigenvalues is normal but need not be Hermitian. -/
theorem isSelfAdjoint_of_forall_apply_eq_real_smul
    {ι : Type*} [Fintype ι] {T : E →ₗ[𝕜] E}
    (b : OrthonormalBasis ι 𝕜 E) (μ : ι → ℝ)
    (h : ∀ i, T (b i) = (μ i : 𝕜) • b i) : IsSelfAdjoint T := by
  -- It suffices to show `Tᴴ = T`; the two agree on the basis `b` because the adjoint of a diagonal
  -- operator is diagonal with the conjugated eigenvalues, and real eigenvalues are self-conjugate.
  rw [isSelfAdjoint_iff, LinearMap.star_eq_adjoint]
  refine b.toBasis.ext (fun k => ?_)
  rw [OrthonormalBasis.coe_toBasis,
    LinearMap.adjoint_apply_of_forall_apply_eq_smul b (fun i => (μ i : 𝕜)) h k,
    RCLike.conj_ofReal, h k]

/-- **Spectral theorem for self-adjoint operators.** An operator `T` on a finite-dimensional inner
product space is self-adjoint (`IsSelfAdjoint T`, i.e. `Tᴴ = T`) if and only if it is diagonal with
respect to some orthonormal basis with real eigenvalues. This is the Hermitian case of N&C's
spectral decomposition (Theorem 2.1 / Box 2.2), and unlike the normal case it holds over any
`RCLike` field. -/
theorem isSelfAdjoint_iff_exists_orthonormalBasis_real {T : E →ₗ[𝕜] E} :
    IsSelfAdjoint T ↔
      ∃ (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E) (μ : Fin (Module.finrank 𝕜 E) → ℝ),
        ∀ i, T (b i) = (μ i : 𝕜) • b i :=
  ⟨fun hT => hT.exists_orthonormalBasis_forall_apply_eq_real_smul,
    fun ⟨b, μ, h⟩ => isSelfAdjoint_of_forall_apply_eq_real_smul b μ h⟩

end LinearMap

end
