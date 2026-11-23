/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SubsystemErrorCorrectionDecoupling

/-!
# AxQM.Postulates.API — subsystem protection as a block condition on the codewords

Infrastructure for **Nielsen & Chuang, Exercise 12.14** (p. 567). For a code with orthonormal
codewords `w : ι → Q₁ ⊗ Q₂` and code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|`, split the coded system as
`Q = Q₁ ⊗ Q₂` and write `σᵢⱼ := Tr_{Q₂} |wᵢ⟩⟨wⱼ|` for the **codeword reduced operators** on `Q₁`.
This file shows that the code **protects the left factor `Q₁`** — `∀ A, ∃ c, P (A ⊗ I) P = c • P`
(the predicate `ProtectsLeftFactor`, in `SubsystemErrorCorrection`) — exactly when the family `σ`
is **scalar-diagonal**:

`(∀ A, ∃ c, P (A ⊗ I) P = c • P)  ⟺  ∃ ρ₁, ∀ i j, Tr_{Q₂} |wᵢ⟩⟨wⱼ| = if i = j then ρ₁ else 0`

(`protectsLeftFactor_iff_codewordReducedScalar`). Together with the decoupling result
`codePurify_decoupledLeftFactor_iff` (decoupling `ρ^{RQ1} = ρ^R ⊗ ρ₁ ⟺ σ scalar-diagonal`), this
supplies the second half of N&C's bridge `decoupling ⟺ ProtectsLeftFactor`; feeding
`ProtectsLeftFactor` into `ProtectsLeftFactor.satisfiesQECConditions` (N&C Theorem 10.1) then makes
the `Q₁`-errors correctable.

## The argument

* `codewordProj_comp_comp_eq` — the sandwich expansion
  `(∑ᵢ |wᵢ⟩⟨wᵢ|) T (∑ᵢ |wᵢ⟩⟨wᵢ|) = ∑ₐ∑_b ⟪wₐ, T w_b⟫ • |wₐ⟩⟨w_b|` for any operator `T` (rank-one
  composition algebra, no orthonormality needed).
* `inner_codewordDoubleSum` / `inner_codewordProjSum` — for orthonormal `w`, the matrix elements
  `⟪wₚ, (∑ₐ∑_b Cₐ_b |wₐ⟩⟨w_b|) wq⟫ = C p q` and `⟪wₚ, (∑ᵢ |wᵢ⟩⟨wᵢ|) wq⟫ = δ_{pq}` read block
  coefficients back off, i.e. the rank-one family `{|wₐ⟩⟨w_b|}` is linearly independent.
* `inner_mapL_eq_trace_partialTraceRight` — the trace/partial-trace duality
  `⟪x, (A ⊗ I) y⟫ = Tr(A · Tr_{Q₂} |y⟩⟨x|)`
  (`trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight` on the coded factor), turning
  `⟪wₐ, (A ⊗ I) w_b⟫` into `Tr(A · σ_{ba})`.
* `traceMatrix_scalarDiag_iff` — the purely linear-algebraic core: a family `σ : ι → ι → (A →ₗ A)`
  has `∀ A, ∃ c, ∀ k l, Tr(A σₖₗ) = δₖₗ c` **iff** it is scalar-diagonal `σₖₗ = δₖₗ ρ₁`. The forward
  direction is Hilbert–Schmidt nondegeneracy (`eq_zero_of_trace_adjoint_comp_self_eq_zero`) applied
  to the off-diagonal `σₖₗ` (`k ≠ l`) and to the differences `σₖₖ − σₗₗ` of the diagonal blocks.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

section CodewordProjector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} [Fintype ι]

/-- **Sandwich expansion of a code projector.** For codewords `w : ι → H` and an operator `T`, the
sandwich of `T` by the (unnormalised) code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` expands over index pairs into
`P T P = ∑ₐ∑_b ⟪wₐ, T w_b⟫ • |wₐ⟩⟨w_b|`, using only rank-one composition algebra
(`comp_rankOne`, `rankOne_comp_rankOne`) — no orthonormality of `w` is needed. -/
theorem codewordProj_comp_comp_eq (w : ι → H) (T : H →L[ℂ] H) :
    (∑ i, rankOne ℂ (w i) (w i)) ∘L T ∘L (∑ i, rankOne ℂ (w i) (w i))
      = ∑ a, ∑ b, (inner ℂ (w a) (T (w b))) • rankOne ℂ (w a) (w b) := by
  rw [ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp_rankOne]

/-- **Block-coefficient read-off.** For an orthonormal codeword family `w`, the `(p, q)` matrix
element of a block sum `∑ₐ∑_b Cₐ_b • |wₐ⟩⟨w_b|` recovers `C p q`:
`⟪wₚ, (∑ₐ∑_b Cₐ_b • |wₐ⟩⟨w_b|) wq⟫ = C p q`. In particular the rank-one family `{|wₐ⟩⟨w_b|}` is
linearly independent. -/
theorem inner_codewordDoubleSum (w : ι → H) (hw : Orthonormal ℂ w) (C : ι → ι → ℂ) (p q : ι) :
    inner ℂ (w p) ((∑ a, ∑ b, C a b • rankOne ℂ (w a) (w b)) (w q)) = C p q := by
  classical
  simp only [sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp hw]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ q) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [ite_eq_right (Ne.symm ha), mul_zero]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- **Diagonal read-off for the code projector.** For orthonormal `w`, the `(p, q)` matrix element
of the code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` is `δ_{pq}`:
`⟪wₚ, (∑ᵢ |wᵢ⟩⟨wᵢ|) wq⟫ = if p = q then 1 else 0`.
-/
theorem inner_codewordProjSum [DecidableEq ι] (w : ι → H) (hw : Orthonormal ℂ w) (p q : ι) :
    inner ℂ (w p) ((∑ i, rankOne ℂ (w i) (w i)) (w q)) = if p = q then (1 : ℂ) else 0 := by
  simp only [sum_apply, InnerProductSpace.rankOne_apply, inner_sum,
    inner_smul_right, orthonormal_iff_ite.mp hw]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ q) h

end CodewordProjector

section Subsystem

variable {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
  {ι : Type*} [Fintype ι]

/-- **Trace / partial-trace duality for the left-factor lift.** For `A ⊗ I` acting on `A ⊗ B`, the
matrix element `⟪x, (A ⊗ I) y⟫` equals `Tr(A · Tr_B |y⟩⟨x|)`, the trace against the codeword reduced
operator: `⟪x, (mapL T 1) y⟫ = Tr(T · partialTraceRight b |y⟩⟨x|)`. This slides the identity on the
traced-out factor `B` out of the pairing
(`trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight`), reducing the left-factor matrix
elements to traces on `A`. -/
theorem inner_mapL_eq_trace_partialTraceRight {κ : Type*} [Fintype κ]
    (bB : OrthonormalBasis κ ℂ B) (T : A →L[ℂ] A) (x y : A ⊗[ℂ] B) :
    inner ℂ x (TensorProduct.mapL T 1 y)
      = LinearMap.trace ℂ A
          (T.toLinearMap ∘ₗ LinearMap.partialTraceRight bB (rankOne ℂ y x).toLinearMap) := by
  rw [← LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight bB T.toLinearMap
      (rankOne ℂ y x).toLinearMap,
    show (TensorProduct.map T.toLinearMap LinearMap.id) = (TensorProduct.mapL T 1).toLinearMap by
      rw [TensorProduct.toLinearMap_mapL, ContinuousLinearMap.toLinearMap_one,
        Module.End.one_eq_id],
    ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.comp_rankOne,
    InnerProductSpace.trace_rankOne]

omit [Fintype ι] in
/-- **The trace-matrix scalar-diagonal criterion.** A family of operators `σ : ι → ι → (A →ₗ A)`
satisfies `∀ T, ∃ c, ∀ k l, Tr(T σₖₗ) = δₖₗ c` **iff** it is scalar-diagonal, `σₖₗ = δₖₗ ρ₁` for a
single operator `ρ₁`. Forward: Hilbert–Schmidt nondegeneracy
(`eq_zero_of_trace_adjoint_comp_self_eq_zero`) with `T = σₖₗ†` kills every off-diagonal
(`Tr(σₖₗ† σₖₗ) = 0 ⟹ σₖₗ = 0`), and with `T = (σₖₖ − σₗₗ)†` forces all diagonal blocks equal.
Reverse: take `c = Tr(T ρ₁)`. -/
theorem traceMatrix_scalarDiag_iff [Nonempty ι] [DecidableEq ι] (σ : ι → ι → (A →ₗ[ℂ] A)) :
    (∀ T : A →L[ℂ] A, ∃ c : ℂ, ∀ k l,
        LinearMap.trace ℂ A (T.toLinearMap ∘ₗ σ k l) = if k = l then c else 0)
      ↔ ∃ ρ1 : A →ₗ[ℂ] A, ∀ k l, σ k l = if k = l then ρ1 else 0 := by
  classical
  constructor
  · intro h
    -- Off-diagonal blocks vanish (HS nondegeneracy with `T = σₖₗ†`).
    have hoff : ∀ k l, k ≠ l → σ k l = 0 := by
      intro k l hkl
      obtain ⟨c, hc⟩ := h (LinearMap.toContinuousLinearMap (LinearMap.adjoint (σ k l)))
      apply LinearMap.eq_zero_of_trace_adjoint_comp_self_eq_zero
      have hkl' := hc k l
      rwa [ite_eq_right hkl, LinearMap.coe_toContinuousLinearMap] at hkl'
    -- All diagonal blocks agree (HS nondegeneracy with `T = (σₖₖ − σ₀₀)†`).
    have hdiag : ∀ k, σ k k = σ (Classical.arbitrary ι) (Classical.arbitrary ι) := by
      intro k
      set i0 := Classical.arbitrary ι
      obtain ⟨c, hc⟩ := h (LinearMap.toContinuousLinearMap (LinearMap.adjoint (σ k k - σ i0 i0)))
      have hkk := hc k k
      have hi0 := hc i0 i0
      rw [ite_eq_left rfl, LinearMap.coe_toContinuousLinearMap] at hkk hi0
      have hzero : LinearMap.trace ℂ A
          (LinearMap.adjoint (σ k k - σ i0 i0) ∘ₗ (σ k k - σ i0 i0)) = 0 := by
        rw [LinearMap.comp_sub, map_sub, hkk, hi0, sub_self]
      have := LinearMap.eq_zero_of_trace_adjoint_comp_self_eq_zero _ hzero
      rwa [sub_eq_zero] at this
    refine ⟨σ (Classical.arbitrary ι) (Classical.arbitrary ι), fun k l => ?_⟩
    by_cases hkl : k = l
    · subst hkl; rw [ite_eq_left rfl, hdiag k]
    · rw [ite_eq_right hkl, hoff k l hkl]
  · rintro ⟨ρ1, hρ1⟩ T
    refine ⟨LinearMap.trace ℂ A (T.toLinearMap ∘ₗ ρ1), fun k l => ?_⟩
    rw [hρ1 k l]
    by_cases hkl : k = l
    · rw [ite_eq_left hkl, ite_eq_left hkl]
    · rw [ite_eq_right hkl, ite_eq_right hkl, LinearMap.comp_zero, map_zero]

/-- **N&C Exercise 12.14, protection side: subsystem protection is a scalar-diagonal condition on
the codeword reduced operators.** For orthonormal codewords `w : ι → Q₁ ⊗ Q₂` with code projector
`P = ∑ᵢ |wᵢ⟩⟨wᵢ|`, the code **protects the left factor** `Q₁` — `∀ A, ∃ c, P (A ⊗ I_{Q₂}) P = c • P`
— **iff** the codeword reduced operators `σᵢⱼ = Tr_{Q₂} |wᵢ⟩⟨wⱼ|` are scalar-diagonal, i.e. there is
a single `Q₁`-operator `ρ₁` with `σᵢⱼ = if i = j then ρ₁ else 0`.

Expanding `P (A ⊗ I) P = ∑ₐ∑_b ⟪wₐ, (A ⊗ I) w_b⟫ • |wₐ⟩⟨w_b|` (`codewordProj_comp_comp_eq`) and
reading off matrix elements (`inner_codewordDoubleSum`, `inner_codewordProjSum`), the operator
equation `P (A ⊗ I) P = c • P` is equivalent to `∀ a b, ⟪wₐ, (A ⊗ I) w_b⟫ = δ_{ab} c`; the trace
duality `inner_mapL_eq_trace_partialTraceRight` rewrites `⟪wₐ, (A ⊗ I) w_b⟫ = Tr(A σ_{ba})`, whence
`traceMatrix_scalarDiag_iff` closes it. This is the same scalar-diagonal condition characterised, on
the decoupling side, by `codePurify_decoupledLeftFactor_iff`.

Stated over abstract inner product spaces `A` (`Q₁`), `B` (`Q₂`) with the code-projector sandwich
written via `TensorProduct.mapL T 1` (which for the composite system is definitionally
`ProtectsLeftFactor`'s `leftFactorOp T`), as on the decoupling side. -/
theorem protectsLeftFactor_iff_codewordReducedScalar [Nonempty ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] (bB : OrthonormalBasis κ ℂ B) (w : ι → A ⊗[ℂ] B)
    (hw : Orthonormal ℂ w) :
    (∀ T : A →L[ℂ] A, ∃ c : ℂ,
        (∑ i, rankOne ℂ (w i) (w i)) ∘L TensorProduct.mapL T 1 ∘L (∑ i, rankOne ℂ (w i) (w i))
          = c • ∑ i, rankOne ℂ (w i) (w i))
      ↔ ∃ ρ1 : A →ₗ[ℂ] A, ∀ i j,
          LinearMap.partialTraceRight bB (rankOne ℂ (w i) (w j)).toLinearMap
            = if i = j then ρ1 else 0 := by
  -- Reduce the operator condition to the trace-matrix condition, then apply the core criterion.
  have step : (∀ T : A →L[ℂ] A, ∃ c : ℂ,
        (∑ i, rankOne ℂ (w i) (w i)) ∘L TensorProduct.mapL T 1 ∘L (∑ i, rankOne ℂ (w i) (w i))
          = c • ∑ i, rankOne ℂ (w i) (w i))
      ↔ (∀ T : A →L[ℂ] A, ∃ c : ℂ, ∀ k l,
          LinearMap.trace ℂ A (T.toLinearMap ∘ₗ
              LinearMap.partialTraceRight bB (rankOne ℂ (w k) (w l)).toLinearMap)
            = if k = l then c else 0) := by
    refine forall_congr' fun T => exists_congr fun c => ?_
    constructor
    · -- `P (A⊗I) P = c • P  ⟹  ∀ k l, Tr(T σₖₗ) = δₖₗ c`.
      intro hop k l
      have hpair : inner ℂ (w l)
          (((∑ i, rankOne ℂ (w i) (w i)) ∘L TensorProduct.mapL T 1 ∘L
              (∑ i, rankOne ℂ (w i) (w i))) (w k))
          = inner ℂ (w l) ((c • ∑ i, rankOne ℂ (w i) (w i)) (w k)) := by rw [hop]
      rw [codewordProj_comp_comp_eq w (TensorProduct.mapL T 1),
        inner_codewordDoubleSum w hw (fun a b => inner ℂ (w a) (TensorProduct.mapL T 1 (w b))) l k,
        smul_apply, inner_smul_right, inner_codewordProjSum w hw l k] at hpair
      rw [← inner_mapL_eq_trace_partialTraceRight bB T (w l) (w k), hpair]
      by_cases hkl : k = l
      · subst hkl; simp
      · rw [ite_eq_right (fun h => hkl h.symm), ite_eq_right hkl, mul_zero]
    · -- `∀ k l, Tr(T σₖₗ) = δₖₗ c  ⟹  P (A⊗I) P = c • P`.
      intro hmat
      rw [codewordProj_comp_comp_eq w (TensorProduct.mapL T 1)]
      have hcoef : ∀ a b, inner ℂ (w a) (TensorProduct.mapL T 1 (w b))
          = if a = b then c else 0 := by
        intro a b
        rw [inner_mapL_eq_trace_partialTraceRight bB T (w a) (w b), hmat b a]
        by_cases hab : a = b
        · subst hab; simp
        · rw [ite_eq_right fun h => hab h.symm, ite_eq_right hab]
      simp only [hcoef]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a]
      · rw [ite_eq_left rfl]
      · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_smul]
      · intro h; exact absurd (Finset.mem_univ a) h
  exact step.trans
    (traceMatrix_scalarDiag_iff
      (fun i j => LinearMap.partialTraceRight bB (rankOne ℂ (w i) (w j)).toLinearMap))

end Subsystem

end AxQM
