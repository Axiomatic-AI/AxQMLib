/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumDataCompression
public import ToMathlib.Analysis.InnerProductSpace.HSPairing
public import ToMathlib.Analysis.InnerProductSpace.Density

/-! # The converse of Schumacher's noiseless channel coding theorem

The **converse (optimality) part** of Schumacher's quantum noiseless channel coding theorem
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, §12.2.2, Theorem 12.6, Eqs.
(12.54)–(12.58)) shows that a rate below the source entropy cannot be achieved reliably. This file
packages the operator-level, *source-independent* half of that argument as a bound on the
entanglement fidelity of any `ContinuousLinearMap.QuantumCompressionScheme`.

## The bound

Fix a block length, i.e. a scheme `sch : QuantumCompressionScheme K numBits` (with `K = H^⊗n`,
`numBits = ⌊nR⌋`) and a source `ρ` (a density operator on `K`). N&C's converse estimate
(Eqs. (12.54)–(12.58)) is: if *every* output subspace carries only a small weight of the source,
then the fidelity is small. Precisely (`QuantumCompressionScheme.fidelity_le`), if every orthogonal
projector `P` onto a subspace of dimension `≤ 2^numBits` satisfies `re tr(P ρ) ≤ δ`, then

`F(ρ, Dₙ ∘ Cₙ) ≤ δ`.

Specialised (in `AxQM/Postulates/API/SchumacherConverse.lean`) to `ρ = ρ^⊗n` and
`numBits = ⌊nR⌋` with `R < S(ρ)`, part (3) of the typical subspace theorem (the *small-subspace
bound*, N&C Eq. (12.45)) supplies exactly the hypothesis `re tr(P ρ^⊗n) ≤ δ` for all `P` of rank
`≤ 2^{nR}`, whence
`F(ρ^⊗n, Dₙ ∘ Cₙ) ≤ δ → 0`: the scheme is not reliable.

## The proof (N&C Eqs. (12.54)–(12.58))

Write `F(ρ, Dₙ ∘ Cₙ) = ∑ₖⱼ |tr(Dₖ Cⱼ ρ)|²` (`fidelity_eq`, N&C Eq. (12.54)). For each
decompression index `k`, let `Sₖ = outputProjection sch k` be the orthogonal projector onto the
image `Dₖ (S(n) K)` of the compressed subspace under `Dₖ`; since `Cⱼ = S(n) Cⱼ`, the composite
`Dₖ Cⱼ` factors through `Sₖ` (`Sₖ Dₖ Cⱼ = Dₖ Cⱼ`, `outputProjection_mul_composite`), and `Sₖ` has
rank `≤ 2^numBits` (`finrank_range_outputProjection_le`, since `Dₖ` cannot increase the dimension).

With `r = √ρ` (`cfc Real.sqrt ρ`, self-adjoint with `r r = ρ`), the fidelity term is the
Hilbert–Schmidt pairing `tr(Dₖ Cⱼ ρ) = ⟨Dₖ Cⱼ r, Sₖ r⟩_HS` (`hsPairing`), so the Cauchy–Schwarz
inequality `‖⟨T, U⟩_HS‖² ≤ ‖T‖²_HS ‖U‖²_HS` (`norm_hsPairing_sq_le`, N&C Eq. (12.56)) gives

`|tr(Dₖ Cⱼ ρ)|² ≤ re tr(Dₖ Cⱼ ρ Cⱼ† Dₖ†) · re tr(Sₖ ρ) ≤ re tr(Dₖ Cⱼ ρ Cⱼ† Dₖ†) · δ`.

Summing over `(k, j)` and using trace-preservation `∑ₖⱼ (Dₖ Cⱼ)† (Dₖ Cⱼ) = 1`
(`composite_isTracePreserving`, N&C Eq. (12.58)) collapses `∑ₖⱼ re tr(Dₖ Cⱼ ρ Cⱼ† Dₖ†) = tr ρ = 1`,
leaving `F ≤ δ`.

## Main definitions and results

* `ContinuousLinearMap.QuantumCompressionScheme.outputProjection` — the output-subspace projector
  `Sₖ` (N&C's `Sₖ(n)`, the paragraph before Eq. (12.55)).
* `ContinuousLinearMap.QuantumCompressionScheme.fidelity_le_of_output_projectors` — the
  Cauchy–Schwarz core: `F(ρ, Dₙ∘Cₙ) ≤ δ` from an *abstract* family of output projectors bounding
  the source weight.
* `ContinuousLinearMap.QuantumCompressionScheme.fidelity_le` — **the converse bound** for a
  `QuantumCompressionScheme`: `F(ρ, Dₙ∘Cₙ) ≤ δ` whenever every rank-`≤ 2^numBits` orthogonal
  projector `P` has `re tr(P ρ) ≤ δ`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Theorem 12.6; Eqs. (12.54)–(12.58)).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap.QuantumCompressionScheme

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  [CompleteSpace K] {numBits : ℕ}

/-- **The output-subspace projector** `Sₖ = Sₖ(n)` of a compression scheme (Nielsen & Chuang,
§12.2.2, the paragraph before Eq. (12.55)): the orthogonal projector onto the image
`Dₖ (S(n) K)` of the compressed subspace under the `k`-th decompression element `Dₖ`. Because
`Dₖ` cannot increase the dimension, `Sₖ` again has rank `≤ 2^numBits`
(`finrank_range_outputProjection_le`), and every composite operation element `Dₖ Cⱼ` factors
through it (`outputProjection_mul_composite`). -/
noncomputable def outputProjection (sch : QuantumCompressionScheme K numBits)
    (k : Fin sch.decCard) : K →L[ℂ] K :=
  (LinearMap.range ((sch.decode k * sch.compressedProjection : K →L[ℂ] K) :
    K →ₗ[ℂ] K)).starProjection

/-- The output-subspace projector `Sₖ` is an orthogonal projection (self-adjoint idempotent). -/
theorem outputProjection_isStarProjection (sch : QuantumCompressionScheme K numBits)
    (k : Fin sch.decCard) : IsStarProjection (sch.outputProjection k) :=
  isStarProjection_starProjection

/-- Every composite operation element `Dₖ Cⱼ` factors through the output projector `Sₖ`:
`Sₖ Dₖ Cⱼ = Dₖ Cⱼ` (Nielsen & Chuang, §12.2.2, `Sₖ(n) Dₖ Cⱼ = Dₖ Cⱼ`). Indeed
`Dₖ Cⱼ = Dₖ S(n) Cⱼ` factors through `Dₖ S(n)`, whose image is the subspace `Sₖ` projects onto. -/
theorem outputProjection_mul_composite (sch : QuantumCompressionScheme K numBits)
    (k : Fin sch.decCard) (j : Fin sch.encCard) :
    sch.outputProjection k * (sch.decode k * sch.encode j) = sch.decode k * sch.encode j := by
  have hcomp : sch.decode k * sch.encode j
      = (sch.decode k * sch.compressedProjection) * sch.encode j := by
    rw [mul_assoc, sch.compressedProjection_mul_encode]
  rw [hcomp, ← mul_assoc]
  congr 1
  ext x
  simp only [mul_apply_eq_comp, outputProjection]
  exact (Submodule.starProjection_eq_self_iff).mpr (LinearMap.mem_range_self _ x)

/-- The output subspace has dimension `≤ 2^numBits`: `Dₖ` maps the `≤ 2^numBits`-dimensional
compressed subspace to a subspace of no larger dimension. -/
theorem finrank_range_outputProjection_le (sch : QuantumCompressionScheme K numBits)
    (k : Fin sch.decCard) :
    Module.finrank ℂ (LinearMap.range (sch.outputProjection k : K →ₗ[ℂ] K)) ≤ 2 ^ numBits := by
  rw [outputProjection, Submodule.range_starProjection, ContinuousLinearMap.toLinearMap_mul,
    Module.End.mul_eq_comp, LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans sch.finrank_range_compressedProjection_le

/-- **The Cauchy–Schwarz core of Schumacher's converse** (Nielsen & Chuang, §12.2.2,
Eqs. (12.54)–(12.58)). Given an *arbitrary* family of orthogonal projectors `S k` such that every
composite operation element `Dₖ Cⱼ` factors through `S k` (`S k · Dₖ Cⱼ = Dₖ Cⱼ`) and the source
weight `re tr(S k · ρ)` in each output subspace is at most `δ`, the entanglement fidelity of the
source `ρ` through the scheme is at most `δ`.

The proof splits `ρ = r · r` with `r = √ρ` (`cfc Real.sqrt ρ`) and reads each fidelity term
`tr(Dₖ Cⱼ ρ)` as a Hilbert–Schmidt pairing `⟨Dₖ Cⱼ r, S k · r⟩_HS`; Cauchy–Schwarz
(`norm_hsPairing_sq_le`) bounds its square by `re tr(Dₖ Cⱼ ρ Cⱼ† Dₖ†) · re tr(S k · ρ)`, and
trace-preservation (`composite_isTracePreserving`) sums the first factors to `tr ρ = 1`. -/
theorem fidelity_le_of_output_projectors (sch : QuantumCompressionScheme K numBits)
    {ρ : K →L[ℂ] K} (hρ : ρ.IsDensityOp) {δ : ℝ} (S : Fin sch.decCard → K →L[ℂ] K)
    (hSproj : ∀ k, IsStarProjection (S k))
    (hSfix : ∀ k j, S k * (sch.decode k * sch.encode j) = sch.decode k * sch.encode j)
    (hSbound : ∀ k, RCLike.re ((LinearMap.trace ℂ K) (↑(S k * ρ) : K →ₗ[ℂ] K)) ≤ δ) :
    sch.fidelity ρ ≤ δ := by
  classical
  have hSadj : ∀ k, ContinuousLinearMap.adjoint (S k) = S k := fun k => by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact (hSproj k).isSelfAdjoint.star_eq
  have hSidem : ∀ k, S k * S k = S k := fun k => (hSproj k).isIdempotentElem
  set r : K →L[ℂ] K := cfc Real.sqrt ρ with hrdef
  -- The general pairing→trace identity `⟨X·√ρ, Y·√ρ⟩_HS = tr(Y† X ρ)`
  -- (`ContinuousLinearMap.hsPairing_mul_cfc_sqrt_eq_trace`, in `Density.lean`).
  have hgen : ∀ X Y : K →L[ℂ] K, (X * r).hsPairing (Y * r)
      = (LinearMap.trace ℂ K) (↑(ContinuousLinearMap.adjoint Y * X * ρ) : K →ₗ[ℂ] K) :=
    fun X Y => ContinuousLinearMap.hsPairing_mul_cfc_sqrt_eq_trace hρ.nonneg X Y
  -- Each fidelity term is the squared HS pairing `‖⟨Dₖ Cⱼ r, Sₖ r⟩_HS‖²`.
  have hterm : ∀ k j, (LinearMap.trace ℂ K) (↑(sch.decode k * sch.encode j * ρ) : K →ₗ[ℂ] K)
      = ((sch.decode k * sch.encode j) * r).hsPairing (S k * r) := by
    intro k j
    rw [hgen, hSadj k, hSfix k j]
  -- The first Cauchy–Schwarz factors sum to `tr ρ = 1`.
  have hcomp1 : (∑ p : Fin sch.decCard × Fin sch.encCard,
      ContinuousLinearMap.adjoint (sch.decode p.1 * sch.encode p.2)
        * (sch.decode p.1 * sch.encode p.2)) = 1 := sch.composite_isTracePreserving
  have hCLM : (∑ k, ∑ j, ContinuousLinearMap.adjoint (sch.decode k * sch.encode j)
      * (sch.decode k * sch.encode j) * ρ) = ρ := by
    simp_rw [← Finset.sum_mul]
    rw [← Finset.sum_product', Finset.univ_product_univ, hcomp1, one_mul]
  have hC : (∑ k, ∑ j, (((sch.decode k * sch.encode j) * r).hsPairing
      ((sch.decode k * sch.encode j) * r))) = (1 : ℂ) := by
    simp_rw [hgen, ← map_sum, ← ContinuousLinearMap.toLinearMap_sum]
    rw [hCLM, hρ.trace_eq_one]
  have hsum1 : ∑ k, ∑ j, RCLike.re
      (((sch.decode k * sch.encode j) * r).hsPairing ((sch.decode k * sch.encode j) * r)) = 1 := by
    rw [show (1 : ℝ) = RCLike.re (1 : ℂ) from RCLike.one_re.symm, ← hC]
    simp_rw [map_sum]
  -- Assemble the bound.
  rw [QuantumCompressionScheme.fidelity_eq]
  calc ∑ k, ∑ j, ‖(LinearMap.trace ℂ K) (↑(sch.decode k * sch.encode j * ρ) : K →ₗ[ℂ] K)‖ ^ 2
      ≤ ∑ k, ∑ j, RCLike.re
          (((sch.decode k * sch.encode j) * r).hsPairing ((sch.decode k * sch.encode j) * r))
          * δ := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => ?_
        rw [hterm k j]
        refine (ContinuousLinearMap.norm_hsPairing_sq_le _ _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.re_hsPairing_self_nonneg _)
        rw [hgen, hSadj k, hSidem k]
        exact hSbound k
    _ = δ := by simp_rw [← Finset.sum_mul]; rw [hsum1, one_mul]

/-- **The converse bound of Schumacher's noiseless channel coding theorem** (Nielsen & Chuang,
§12.2.2, Theorem 12.6, Eqs. (12.54)–(12.58)), in terms of `QuantumCompressionScheme`. If every
orthogonal projector `P` onto a subspace of dimension at most `2^numBits` captures only weight
`re tr(P ρ) ≤ δ` of the source `ρ`, then the entanglement fidelity of `ρ` through the scheme is at
most `δ`.

The witnesses are the output projectors `Sₖ = outputProjection sch k` (rank `≤ 2^numBits`,
`finrank_range_outputProjection_le`; factoring the composites, `outputProjection_mul_composite`);
`fidelity_le_of_output_projectors` then supplies the Cauchy–Schwarz estimate. Specialised to
`ρ = ρ^⊗n` and `numBits = ⌊nR⌋` with `R < S(ρ)`, the small-subspace bound (typical subspace theorem
part (3)) provides the hypothesis, forcing `F(ρ^⊗n, Dₙ∘Cₙ) → 0`. -/
theorem fidelity_le (sch : QuantumCompressionScheme K numBits) {ρ : K →L[ℂ] K}
    (hρ : ρ.IsDensityOp) {δ : ℝ}
    (hsmall : ∀ P : K →L[ℂ] K, IsStarProjection P →
      Module.finrank ℂ (LinearMap.range (P : K →ₗ[ℂ] K)) ≤ 2 ^ numBits →
      RCLike.re ((LinearMap.trace ℂ K) (↑(P * ρ) : K →ₗ[ℂ] K)) ≤ δ) :
    sch.fidelity ρ ≤ δ :=
  fidelity_le_of_output_projectors sch hρ (fun k => sch.outputProjection k)
    (fun k => sch.outputProjection_isStarProjection k)
    (fun k j => sch.outputProjection_mul_composite k j)
    (fun k => hsmall _ (sch.outputProjection_isStarProjection k)
      (sch.finrank_range_outputProjection_le k))

end ContinuousLinearMap.QuantumCompressionScheme
