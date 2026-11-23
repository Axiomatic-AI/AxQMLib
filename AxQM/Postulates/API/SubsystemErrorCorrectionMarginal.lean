/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SubsystemErrorCorrection

/-!
# AxQM.Postulates.API — the maximally-mixed code purification and its marginals

Infrastructure for **Nielsen & Chuang, Exercise 12.14** (p. 567). An `[n, k]` code `C` living in a
system `Q` with orthonormal codewords `|x⟩` and code projector `P` has maximally-mixed code state
`P / 2ᵏ`, which N&C purify to a pure state of `R ⊗ Q`,

`|RQ⟩ = (1 / √2ᵏ) ∑ₓ |x⟩ ⊗ |x⟩`   (N&C Eq. (12.142)),

with `R` a `2ᵏ`-dimensional reference system. Splitting the coded system as `Q = Q₁ ⊗ Q₂`
(`Q₁` the protected subsystem), the exercise's *decoupling condition* `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1}`
is a statement about the marginals of `|RQ⟩⟨RQ|`. This file computes those marginals in closed
form; the files `AxQM/Postulates/API/SubsystemErrorCorrection*.lean` develop the code-theoretic side
and the equivalence `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1} ⟺ ProtectsLeftFactor P`.

Everything here is basis/operator-level computation over abstract finite-dimensional inner product
spaces `R` (reference), `A` (`Q₁`), `B` (`Q₂`). The two marginals:

* `AxQM.codePurifyVec` — the (unnormalized) code purification vector `∑ x, e x ⊗ w x`.
* `AxQM.codePurifyVec_partialTraceRight_ref` — the **reference marginal**
  `Tr_{A⊗B} |RQ⟩⟨RQ| = ∑ᵢⱼ ⟪wⱼ, wᵢ⟫ • |eᵢ⟩⟨eⱼ|`, hence `= 1` (maximally mixed, up to normalisation)
  when `e` is an orthonormal basis and the codewords `w` are orthonormal
  (`codePurifyVec_partialTraceRight_ref_eq_id`).
* `AxQM.codePurifyVec_partialTraceRight_assoc` — the **`R ⊗ A` (i.e. `R ⊗ Q₁`) marginal**
  `Tr_B |RQ⟩⟨RQ| = ∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ Tr_B |wᵢ⟩⟨wⱼ|`, obtained by re-associating `R ⊗ (A ⊗ B)` to
  `(R ⊗ A) ⊗ B` and tracing out `B` (`LinearMap.partialTraceRight_assoc_conj_map`), the block form
  the decoupling condition is read against.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

variable {R A B : Type*}
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
  {ι : Type*} [Fintype ι]

/-- The (unnormalized) **maximally-entangled code purification vector** `|RQ⟩ = ∑ₓ eₓ ⊗ wₓ` in
`R ⊗ (A ⊗ B)`, for a reference family `e : ι → R` and codewords `w : ι → A ⊗ B`. Nielsen & Chuang's
`(1 / √2ᵏ) ∑ₓ |x⟩ ⊗ |x⟩` (Eq. (12.142)); the scalar `1 / √2ᵏ = 1 / √(card ι)` normalisation is
carried by the caller (it multiplies the density operator `|RQ⟩⟨RQ|` by `1 / card ι`). -/
def codePurifyVec (e : ι → R) (w : ι → A ⊗[ℂ] B) : R ⊗[ℂ] (A ⊗[ℂ] B) :=
  ∑ x, e x ⊗ₜ[ℂ] w x

/-- The density operator `|RQ⟩⟨RQ|` of the code purification expands over the index pairs into
tensor-product rank-ones: `|RQ⟩⟨RQ| = ∑ᵢⱼ (|eᵢ⟩⟨eⱼ|) ⊗ (|wᵢ⟩⟨wⱼ|)` (as `TensorProduct.mapL`). The
starting point for both marginal computations. -/
theorem rankOne_codePurifyVec (e : ι → R) (w : ι → A ⊗[ℂ] B) :
    (rankOne ℂ (codePurifyVec e w)) (codePurifyVec e w)
      = ∑ i, ∑ j, TensorProduct.mapL (rankOne ℂ (e i) (e j)) (rankOne ℂ (w i) (w j)) := by
  simp only [codePurifyVec, map_sum, sum_apply,
    InnerProductSpace.rankOne_tmul_tmul]
  rw [Finset.sum_comm]

/-- **The reference marginal of the code purification.** Tracing out the whole coded factor `A ⊗ B`
from `|RQ⟩⟨RQ|` gives `∑ᵢⱼ ⟪wⱼ, wᵢ⟫ • |eᵢ⟩⟨eⱼ|` on the reference `R`. -/
theorem codePurifyVec_partialTraceRight_ref {κ : Type*} [Fintype κ]
    (bAB : OrthonormalBasis κ ℂ (A ⊗[ℂ] B)) (e : ι → R) (w : ι → A ⊗[ℂ] B) :
    LinearMap.partialTraceRight bAB
        ((rankOne ℂ (codePurifyVec e w)) (codePurifyVec e w)).toLinearMap
      = ∑ i, ∑ j, (inner ℂ (w j) (w i)) • (rankOne ℂ (e i) (e j)).toLinearMap := by
  rw [rankOne_codePurifyVec, ← LinearMap.partialTraceRightLM_apply]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum, LinearMap.partialTraceRightLM_apply,
    TensorProduct.toLinearMap_mapL, LinearMap.partialTraceRight_tensorMap,
    InnerProductSpace.trace_rankOne]

/-- **The reference marginal is maximally mixed.** When the reference family `e` is an orthonormal
basis and the codewords `w` are orthonormal, tracing out the coded factor `A ⊗ B` from `|RQ⟩⟨RQ|`
gives the identity `1` on `R` (i.e. `2ᵏ · ρ^R`, the unnormalised maximally mixed state). -/
theorem codePurifyVec_partialTraceRight_ref_eq_id {κ : Type*} [Fintype κ]
    (bAB : OrthonormalBasis κ ℂ (A ⊗[ℂ] B)) (e : OrthonormalBasis ι ℂ R) {w : ι → A ⊗[ℂ] B}
    (hw : Orthonormal ℂ w) :
    LinearMap.partialTraceRight bAB
        ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap
      = LinearMap.id := by
  classical
  rw [codePurifyVec_partialTraceRight_ref]
  have hdiag : ∀ i, (∑ j, (inner ℂ (w j) (w i)) • (rankOne ℂ (e i) (e j)).toLinearMap)
      = ((rankOne ℂ (e i) (e i)).toLinearMap : R →ₗ[ℂ] R) := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [orthonormal_iff_ite.mp hw i i, ite_eq_left rfl, one_smul]
    · intro j _ hj
      rw [orthonormal_iff_ite.mp hw j i, ite_eq_right hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hdiag]
  rw [← ContinuousLinearMap.toLinearMap_sum, OrthonormalBasis.sum_rankOne_eq_id,
      ContinuousLinearMap.coe_id]

/-- **The `R ⊗ A` marginal of the code purification** — N&C's `ρ^{RQ1}`. Tracing out the second
coded factor `B` (i.e. `Q₂`) from `|RQ⟩⟨RQ|`, keeping the reference `R` and first coded factor `A`
(i.e. `Q₁`), gives the block form `∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ Tr_B |wᵢ⟩⟨wⱼ|`. The marginal is obtained by
re-associating `R ⊗ (A ⊗ B)` to `(R ⊗ A) ⊗ B` (`TensorProduct.assoc _ R A B).symm`) and tracing out
`B`; `LinearMap.partialTraceRight_assoc_conj_map` slides the trace past the reference block. -/
theorem codePurifyVec_partialTraceRight_assoc {κ : Type*} [Fintype κ]
    (bB : OrthonormalBasis κ ℂ B) (e : ι → R) (w : ι → A ⊗[ℂ] B) :
    LinearMap.partialTraceRight bB
        ((TensorProduct.assoc ℂ R A B).symm.conj
          ((rankOne ℂ (codePurifyVec e w)) (codePurifyVec e w)).toLinearMap)
      = ∑ i, ∑ j, TensorProduct.map (rankOne ℂ (e i) (e j)).toLinearMap
          (LinearMap.partialTraceRight bB (rankOne ℂ (w i) (w j)).toLinearMap) := by
  rw [rankOne_codePurifyVec, ← LinearMap.partialTraceRightLM_apply]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum, LinearMap.partialTraceRightLM_apply,
    TensorProduct.toLinearMap_mapL, LinearMap.partialTraceRight_assoc_conj_map]

end AxQM
