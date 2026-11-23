/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
public import ToMathlib.Analysis.InnerProductSpace.OperatorSumComposition
public import ToMathlib.Analysis.InnerProductSpace.PiTensorProductMap

/-! # Quantum data compression: schemes, entanglement fidelity, and reliability

This file sets up the operational framework for Schumacher's quantum noiseless channel coding
theorem (Nielsen–Chuang, *Quantum Computation and Quantum Information*, §12.2.2): the notion of a
**rate-`R` quantum compression scheme** for an i.i.d. quantum source `{H, ρ}`, the **entanglement
fidelity** through such a scheme, and the resulting **reliability** predicate. It is the quantum
analogue of the classical compression model in `ToMathlib/InformationTheory/NoiselessCoding.lean`
(N&C Theorem 12.4), and the target it works towards is
`ReliablyCompressible ρ R ↔ S(ρ) < R` (Theorem 12.6).

## The model

Following N&C §12.2.2, a compression scheme at block length `n` is a pair of quantum operations:
a **compression** `Cₙ` taking states on `H^⊗n` into a `2^{nR}`-dimensional *compressed space*, and
a **decompression** `Dₙ` back to `H^⊗n`. N&C's own analysis of both directions (the direct part's
projection–reset encoder, Eq. (12.50), and the converse, Eqs. (12.54)–(12.55)) realises `Cₙ` as a
quantum operation *on `H^⊗n`* whose operation elements `Cⱼ` all factor through a projector `S(n)`
onto a subspace of dimension `≤ 2^{nR}` (`Cⱼ = S(n) Cⱼ`). We take that as the definition, so a
scheme is `QuantumCompressionScheme K numBits` for a Hilbert space `K` (standing for `H^⊗n`) and a
qubit budget `numBits` (standing for `⌊nR⌋`):

* Kraus families `encode : Fin encCard → K →L[ℂ] K` and `decode : Fin decCard → K →L[ℂ] K`, each
  trace-preserving (`∑ Eᵢ† Eᵢ = 1`);
* a projector `compressedProjection` (`= S(n)`), an orthogonal (`IsStarProjection`) projection whose
  range has dimension `≤ 2^numBits` and through which every `encode` element factors.

The combined operation `Dₙ ∘ Cₙ` has operation elements `Dₖ Cⱼ`
(`QuantumCompressionScheme.composite`), and N&C's reliability criterion is that the entanglement
fidelity `F(ρ^⊗n, Dₙ ∘ Cₙ)`
(`QuantumCompressionScheme.fidelity`) tends to `1` as `n → ∞` (`ReliablyCompressible`), where
`ρ^⊗n = PiTensorProduct.mapCLM (fun _ ↦ ρ)`.

## Main definitions and results

* `ContinuousLinearMap.QuantumCompressionScheme` — a rate-`numBits` compression scheme on `K`.
* `ContinuousLinearMap.QuantumCompressionScheme.composite` — the operation elements `Dₖ Cⱼ` of
  `Dₙ ∘ Cₙ`.
* `ContinuousLinearMap.QuantumCompressionScheme.fidelity` — `F(ρ, Dₙ ∘ Cₙ)`, the entanglement
  fidelity of the source `ρ` through the scheme.
* `ContinuousLinearMap.QuantumCompressionScheme.fidelity_eq` — **N&C Eq. (12.54)**:
  `F(ρ, Dₙ ∘ Cₙ) = ∑ₖ ∑ⱼ |tr(Dₖ Cⱼ ρ)|²`.
* `ContinuousLinearMap.QuantumCompressionScheme.composite_isTracePreserving` — `Dₙ ∘ Cₙ` is a
  trace-preserving operation (`∑ⱼₖ (Dₖ Cⱼ)† (Dₖ Cⱼ) = 1`), used in the converse (N&C Eq. (12.58)).
* `ContinuousLinearMap.ReliablyCompressible` — a source `ρ` is reliably compressible at rate `R`:
  a family of rate-`R` schemes exists whose entanglement fidelity for `ρ^⊗n` tends to `1`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Theorem 12.6; Eqs. (12.50)–(12.58)).
-/

open scoped InnerProductSpace TensorProduct

@[expose] public section

namespace ContinuousLinearMap

/-- A **rate-`numBits` quantum compression scheme** on a Hilbert space `K` (Nielsen & Chuang,
§12.2.2), standing for one block length `n` with `K = H^⊗n` and `numBits = ⌊nR⌋`. It bundles a
compression operation `Cₙ` and a decompression operation `Dₙ`, given by their Kraus families, with
the requirement that `Cₙ` compresses into a subspace of dimension at most `2^numBits`.

Both operations are quantum operations *on `K`* (endomorphisms), and the compressed space is the
range of an orthogonal projector `compressedProjection = S(n)` of dimension `≤ 2^numBits` through
which every compression element factors — exactly N&C's own description of the compression operation
in the converse (Eq. (12.55), `Cⱼ = S(n) Cⱼ`) and satisfied by the projection–reset encoder of the
direct part (Eq. (12.50)). -/
structure QuantumCompressionScheme (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] [CompleteSpace K] (numBits : ℕ) where
  /-- The number of Kraus operators of the compression operation `Cₙ`. -/
  encCard : ℕ
  /-- The number of Kraus operators of the decompression operation `Dₙ`. -/
  decCard : ℕ
  /-- The Kraus operators (operation elements) `Cⱼ` of the compression operation `Cₙ`. -/
  encode : Fin encCard → K →L[ℂ] K
  /-- The Kraus operators (operation elements) `Dₖ` of the decompression operation `Dₙ`. -/
  decode : Fin decCard → K →L[ℂ] K
  /-- `Cₙ` is trace-preserving: `∑ⱼ Cⱼ† Cⱼ = 1`. -/
  encode_isTracePreserving : ∑ j, adjoint (encode j) * encode j = 1
  /-- `Dₙ` is trace-preserving: `∑ₖ Dₖ† Dₖ = 1`. -/
  decode_isTracePreserving : ∑ k, adjoint (decode k) * decode k = 1
  /-- The projector `S(n)` onto the compressed subspace (the `2^numBits`-dimensional space). -/
  compressedProjection : K →L[ℂ] K
  /-- `S(n)` is an orthogonal (self-adjoint idempotent) projection. -/
  isStarProjection_compressedProjection : IsStarProjection compressedProjection
  /-- Every compression element maps into the compressed subspace: `Cⱼ = S(n) Cⱼ`. -/
  compressedProjection_mul_encode : ∀ j, compressedProjection * encode j = encode j
  /-- Rate bound: the compressed subspace has dimension at most `2^numBits`. -/
  finrank_range_compressedProjection_le :
    Module.finrank ℂ (LinearMap.range (compressedProjection : K →ₗ[ℂ] K)) ≤ 2 ^ numBits

namespace QuantumCompressionScheme

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  [CompleteSpace K] {numBits : ℕ}

/-- The operation elements of the combined compression–decompression operation `Dₙ ∘ Cₙ`: the
products `Dₖ Cⱼ`, indexed by pairs `(k, j)`. -/
def composite (sch : QuantumCompressionScheme K numBits) :
    Fin sch.decCard × Fin sch.encCard → K →L[ℂ] K :=
  fun p => sch.decode p.1 * sch.encode p.2

/-- The operation element of `Dₙ ∘ Cₙ` at a pair `(k, j)` is `Dₖ Cⱼ`. -/
@[simp]
theorem composite_apply (sch : QuantumCompressionScheme K numBits)
    (p : Fin sch.decCard × Fin sch.encCard) : sch.composite p = sch.decode p.1 * sch.encode p.2 :=
  rfl

/-- The **entanglement fidelity** `F(ρ, Dₙ ∘ Cₙ)` of a source `ρ` through the scheme, i.e. the
entanglement fidelity of `ρ` under the combined operation `Dₙ ∘ Cₙ` (Nielsen & Chuang, §12.2.2).
Reliability of a family of schemes is this quantity tending to `1` (`ReliablyCompressible`). -/
noncomputable def fidelity (sch : QuantumCompressionScheme K numBits) (ρ : K →L[ℂ] K) : ℝ :=
  ContinuousLinearMap.entanglementFidelity ρ sch.composite

/-- **Nielsen & Chuang, Eq. (12.54).** The entanglement fidelity of the source `ρ` through the
scheme is the double sum `∑ₖ ∑ⱼ |tr(Dₖ Cⱼ ρ)|²` over the decompression and compression operation
elements. -/
theorem fidelity_eq (sch : QuantumCompressionScheme K numBits) (ρ : K →L[ℂ] K) :
    sch.fidelity ρ
      = ∑ k, ∑ j, ‖LinearMap.trace ℂ K
          ((sch.decode k * sch.encode j * ρ : K →L[ℂ] K) : K →ₗ[ℂ] K)‖ ^ 2 := by
  rw [fidelity, ContinuousLinearMap.entanglementFidelity, Fintype.sum_prod_type]
  simp only [composite_apply, ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm]

/-- The entanglement fidelity through a scheme is nonnegative (it is a sum of squared norms). -/
theorem fidelity_nonneg (sch : QuantumCompressionScheme K numBits) (ρ : K →L[ℂ] K) :
    0 ≤ sch.fidelity ρ :=
  ContinuousLinearMap.entanglementFidelity_nonneg ρ sch.composite

/-- The combined compression–decompression operation `Dₙ ∘ Cₙ` is **trace-preserving**: its
operation elements `Dₖ Cⱼ` satisfy the completeness relation `∑ⱼₖ (Dₖ Cⱼ)† (Dₖ Cⱼ) = 1`. This is
the fact used in the last step of N&C's converse (Eq. (12.58)); it is the composition case of the
operator-sum trace condition, `ContinuousLinearMap.sum_adjoint_comp_comp_eq_one`, applied to the
trace-preserving encode/decode families. -/
theorem composite_isTracePreserving (sch : QuantumCompressionScheme K numBits) :
    ∑ p, adjoint (sch.composite p) * sch.composite p = 1 := by
  simpa only [composite_apply, ContinuousLinearMap.mul_def] using
    ContinuousLinearMap.sum_adjoint_comp_comp_eq_one sch.encode sch.decode
      sch.encode_isTracePreserving sch.decode_isTracePreserving

end QuantumCompressionScheme

/- Only `[FiniteDimensional ℂ H]` is required below (no `[CompleteSpace H]`, unlike
`QuantumCompressionScheme`/`EntanglementFidelity`): the schemes live on the block spaces `H^⊗n`, not
on `H` itself, and `CompleteSpace (⨂[ℂ] (_ : Fin n), H)` is *derived* from `[FiniteDimensional ℂ H]`
(a finite tensor power of a finite-dimensional space is finite-dimensional, hence complete). For an
arbitrary space `CompleteSpace` is **not** an instance consequence of `FiniteDimensional`, which is
why `QuantumCompressionScheme` (over a general `K`) must carry it explicitly. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A source `ρ` (a density operator on `H`) is **reliably compressible at rate `R`** if there is a
family of rate-`R` quantum compression schemes — one for each block length `n`, on the block space
`H^⊗n` with qubit budget `⌊nR⌋` — whose entanglement fidelity for the source `ρ^⊗n` tends to `1` as
`n → ∞` (Nielsen & Chuang, §12.2.2). Here `ρ^⊗n = PiTensorProduct.mapCLM (fun _ ↦ ρ)` is the
`n`-fold tensor power of `ρ`. Schumacher's noiseless channel coding theorem (Theorem 12.6) states
that this holds exactly when `S(ρ) < R`. -/
def ReliablyCompressible (ρ : H →L[ℂ] H) (R : ℝ) : Prop :=
  ∃ sch : (n : ℕ) → QuantumCompressionScheme (⨂[ℂ] (_ : Fin n), H) ⌊(n : ℝ) * R⌋₊,
    Filter.Tendsto
      (fun n => (sch n).fidelity (PiTensorProduct.mapCLM fun _ : Fin n => ρ))
      Filter.atTop (nhds 1)

end ContinuousLinearMap
