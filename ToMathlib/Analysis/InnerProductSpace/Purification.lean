/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.Matricization
public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# Purification — partial trace of a rank-one projection (Nielsen–Chuang §2.5)

A bipartite pure state `Ψ : E ⊗[𝕜] F` is a **purification** of an operator `ρ : E →L[𝕜] E`
when the partial trace of its rank-one self-projection over the ancilla factor `F`
recovers `ρ`. The right-hand side `matricize b Ψ ∘L (matricize b Ψ).adjoint` is the
"outer-product" form of the reduced density matrix (for any orthonormal basis `b` on `F`).

## Main results

- `TensorProduct.IsPurification` : abstract purification predicate, parametric in an
  ancilla `F`.
- `TensorProduct.canonicalPurification` : the canonical doubled purification on
  `E ⊗ EuclideanSpace 𝕜 (Fin n)` (n = `Module.finrank 𝕜 E`).
- `TensorProduct.norm_canonicalPurification` / `isPurification_canonicalPurification`
  / `exists_purification` : the abstract characterizations + existence corollary.
-/

@[expose] public section

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [CompleteSpace E]

/-- **Purification predicate**: `Ψ : E ⊗[𝕜] F` is a purification of `ρ` if the
right-partial-trace at `stdOrthonormalBasis 𝕜 F` of `rankOne Ψ Ψ` equals `ρ` at LM level. -/
def IsPurification {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (ρ : E →L[𝕜] E) (Ψ : E ⊗[𝕜] F) : Prop :=
  LinearMap.partialTraceRight (stdOrthonormalBasis 𝕜 F)
    ((InnerProductSpace.rankOne 𝕜 Ψ Ψ).toLinearMap) = ρ.toLinearMap

/-- **Basis-parametric matricize characterization of `IsPurification`** (abstract).
`Ψ` is a purification of `ρ` iff the matricize-square `matricize Ψ ∘ (matricize Ψ)†`
recovers `ρ`, **for any** orthonormal basis `b` on the ancilla `F`. The basis
independence comes from `LinearMap.partialTraceRight_eq_of_basis`.

This is the CLM-level identity that allows the
purification predicate to be checked / produced via any natural ancilla basis without
threading `stdOrthonormalBasis` through the proof. -/
theorem isPurification_iff_matricize_comp_adjoint
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [CompleteSpace F] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 F) (ρ : E →L[𝕜] E) (Ψ : E ⊗[𝕜] F) :
    IsPurification ρ Ψ ↔ (matricize b Ψ).comp (matricize b Ψ).adjoint = ρ := by
  rw [IsPurification, LinearMap.partialTraceRight_eq_of_basis _ b,
    partialTraceRight_rankOne_self]
  exact ContinuousLinearMap.coe_inj

omit [CompleteSpace E] in
/-- **Every purification of a density operator has unit norm** (abstract). For any
ancilla `F` and any `Ψ : E ⊗[𝕜] F` purifying a density operator `ρ`, `‖Ψ‖ = 1`.

Proof: the partial trace preserves trace (`trace_partialTraceRight`), so
`‖Ψ‖² = ⟨Ψ, Ψ⟩ = trace (rankOne Ψ Ψ) = trace (partialTraceRight (rankOne Ψ Ψ)) = trace ρ = 1`. -/
theorem norm_eq_one_of_isPurification {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp)
    {Ψ : E ⊗[𝕜] F} (hΨ : IsPurification ρ Ψ) :
    ‖Ψ‖ = 1 := by
  suffices h : ‖Ψ‖ ^ 2 = 1 by
    rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_one]
  have htr : (LinearMap.trace 𝕜 _) ((InnerProductSpace.rankOne 𝕜 Ψ Ψ :
      _ →L[𝕜] _).toLinearMap) = 1 := by
    rw [← LinearMap.trace_partialTraceRight (stdOrthonormalBasis 𝕜 F), hΨ, hρ.trace_eq_one]
  rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K] at htr
  exact_mod_cast htr

/-- **Canonical doubled purification of a density operator** (abstract, basis-parametric).
For a density operator `ρ : E →L[𝕜] E` and any orthonormal basis `b` on the ancilla `F`
indexed by `Fin (Module.finrank 𝕜 E)`, the canonical purification on `E ⊗[𝕜] F` is built
from `ρ`'s spectral decomposition:

  `canonicalPurification hρ b = ∑ i, (√λᵢ : 𝕜) • (eᵢ ⊗ₜ b i)`

where `λᵢ, eᵢ` are the eigenvalues and eigenvectors of `ρ` (via `IsSymmetric.eigenvalues` /
`IsSymmetric.eigenvectorBasis`). Setting `F := EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))`
and `b := EuclideanSpace.basisFun _ 𝕜` recovers the original concrete-ancilla form. -/
noncomputable def canonicalPurification {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp)
    (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 F) : E ⊗[𝕜] F :=
  ∑ i, (Real.sqrt (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl i) : 𝕜) •
    (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl i ⊗ₜ[𝕜] b i)

/-- **The canonical purification's right-partial-trace recovers `ρ`.** Spectral form via
`partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt` reduces the LHS to `∑ i, λᵢ • rankOne eᵢ eᵢ`,
which is the spectral decomposition of `ρ` via `IsSelfAdjoint.spectral_sum`. -/
theorem isPurification_canonicalPurification {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp)
    (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 F) :
    IsPurification ρ (canonicalPurification hρ b) := by
  have hSA : IsSelfAdjoint ρ := hρ.isPositive.isSelfAdjoint
  have hSym := hSA.isSymmetric
  rw [IsPurification,
    LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis 𝕜 F)
      (Ψ := canonicalPurification hρ b)
      (fun i ↦ Real.sqrt (hSym.eigenvalues rfl i))
      (fun i ↦ hSym.eigenvectorBasis rfl i)
      (fun i ↦ b i)
      b.orthonormal rfl]
  conv_rhs => rw [hSA.spectral_sum rfl]
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← RCLike.ofReal_pow, Real.sq_sqrt (hρ.eigenvalues_nonneg rfl i)]

/-- **The canonical doubled purification has unit norm.** Direct corollary of the general
`norm_eq_one_of_isPurification` applied to `isPurification_canonicalPurification`. -/
theorem norm_canonicalPurification {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp)
    (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 F) :
    ‖canonicalPurification hρ b‖ = 1 :=
  norm_eq_one_of_isPurification hρ (isPurification_canonicalPurification hρ b)

/-- **Abstract purification existence**: every density operator on a finite-dimensional
inner product space admits a purification on `E ⊗ EuclideanSpace 𝕜 (Fin n)`. Abstract
analog of `ContinuousLinearMap.IsDensityOp.exists_purification`. -/
theorem exists_purification {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp) :
    ∃ Ψ : E ⊗[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E)),
      ‖Ψ‖ = 1 ∧ IsPurification ρ Ψ :=
  ⟨canonicalPurification hρ (EuclideanSpace.basisFun _ 𝕜),
    norm_canonicalPurification hρ _, isPurification_canonicalPurification hρ _⟩

end TensorProduct
