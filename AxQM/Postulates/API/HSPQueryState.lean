/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CosetDensityState
import AxQM.Postulates.PartialTrace
import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
import ToMathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# AxQM.Postulates.API — the HSP query state (5.80) and its coset reduced state

The reduced-state step of Nielsen & Chuang, Problem 5.5 (the
non-Abelian hidden subgroup problem). Given a finite group `G`, a finite range `X`, and a query
function `f : G → X` promised to be **constant and distinct on the left cosets** of a subgroup
`K ≤ G` (`hf : ∀ g₁ g₂, f g₁ = f g₂ ↔ (g₁ : G ⧸ K) = g₂`), the **single-copy query state** (the
`m = 1` case of Nielsen & Chuang eq. 5.80)

`|ψ_f⟩ = |G|^{-1/2} ∑_{g ∈ G} |g⟩ |f(g)⟩ ∈ ℂ[G] ⊗ ℂ[X]`

lives on the composite `groupSystem G ⊗ groupSystem X` (the range register `ℂ[X]` is the same
`ofModel (EuclideanSpace ℂ ·)` construction as the group register — it needs only finiteness).

This file defines:

* `hspQueryVec f` / `hspQueryState f` — the query vector `|ψ_f⟩` and its promotion to a `PureState`
  of `groupSystem G ⊗ groupSystem X`. It is normalized because the elementary tensors
  `{|g⟩|f(g)⟩}_{g ∈ G}` are orthonormal (distinct `g` give orthogonal `|g⟩`), so
  `‖|ψ_f⟩‖² = ∑_g |G|⁻¹ = 1`.
* `hspQueryVec_eq_schmidt` — the **Schmidt decomposition over cosets**
  `|ψ_f⟩ = ∑_{q ∈ G ⧸ K} √(|K|/|G|) |C_q⟩ |f(q̂)|⟩`, where `|C_q⟩` is the normalized coset state and
  `q̂` is any representative of `q`. Because `f` is constant on cosets, all `|g⟩` in a coset share
  the same range label, and `∑_{g ∈ q} |g⟩ = √|K| |C_q⟩`; because `f` is distinct across cosets,
  both Schmidt factor families are orthonormal.
* `hspQueryState_reducedLeft_op` — the operator-level reduced state
  `Tr_{ℂ[X]} |ψ_f⟩⟨ψ_f| = σ_K`: tracing out the range register `ℂ[X]` leaves the group register in
  the coset density operator `(cosetDensityState K).op`. The right (range) Schmidt factors
  `|f(q̂)⟩` are orthonormal, so the Schmidt partial-trace lemma gives
  `∑_q (|K|/|G|) |C_q⟩⟨C_q|`, which is `σ_K` by `cosetDensityState_op_eq_sum`.

The `State`-level statement `(hspQueryState f).toState.reducedLeft = cosetDensityState K` is in
`AxQM/NC/Ch5/Problem5_5.lean`, proved by `State.ext` from the `_op` lemma here.

## Design notes

* This is the **single-copy** (`m = 1`) reduced-state identity, the mathematical kernel of the
  Problem 5.5 sampling argument (`σ_K` is the per-copy reduced state whose `m`-fold tensor power
  carries the identifiability). The `m`-copy lift `Tr |ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}| = σ_K^{⊗m}` is
  not proved in this file; it follows from multiplicativity of the reduced state under tensor
  powers.
* The proof reuses the abstract Schmidt partial-trace lemma
  `LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt` (the same one behind the Bell
  marginals `bellState_reducedLeft_op`), transported from its `Fin n` index to `G ⧸ K` via
  `Fintype.equivFin`. All the coset combinatorics stay in `Concrete.CosetState*`; here we only
  regroup the query sum over cosets and invoke the spectral form `cosetDensityState_op_eq_sum`.
-/

open scoped InnerProductSpace TensorProduct ComplexOrder

noncomputable section

namespace AxQM

variable {G X : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]

/-- The **single-copy HSP query vector** `|ψ_f⟩ = |G|^{-1/2} ∑_{g} |g⟩|f(g)⟩` (Nielsen & Chuang
eq. 5.80, `m = 1`) as an element of the composite state space `ℂ[G] ⊗ ℂ[X]`. -/
def hspQueryVec (f : G → X) : ((groupSystem G).compose (groupSystem X)).space :=
  ∑ g : G, (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) •
    (EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single (f g) (1 : ℂ))

omit [Group G] in
/-- The elementary tensors `|g⟩|f(g)⟩` of the query state form an **orthonormal family**: distinct
`g` give orthogonal computational basis vectors `|g⟩`, so `⟪|g⟩|f(g)⟩, |g'⟩|f(g')⟩⟫ = [g = g']`.
(No promise on `f` is needed here.) -/
theorem hspQueryFactor_orthonormal (f : G → X) :
    Orthonormal ℂ (fun g : G =>
      (EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single (f g) (1 : ℂ) :
        ((groupSystem G).compose (groupSystem X)).space)) := by
  rw [orthonormal_iff_ite]
  intro g g'
  erw [TensorProduct.inner_tmul,
    orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single g g',
    orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single (f g) (f g')]
  by_cases hg : g = g'
  · subst hg; simp
  · simp [hg]

/-- The **HSP query vector is a unit vector**: `‖|ψ_f⟩‖ = 1`, since the `|g⟩|f(g)⟩` are orthonormal
and `∑_g (|G|^{-1/2})² = |G| · |G|⁻¹ = 1`. -/
theorem hspQueryVec_norm (f : G → X) : ‖hspQueryVec f‖ = 1 := by
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hnorm : ‖(((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ)‖ ^ 2 = (Fintype.card G : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), inv_pow,
      Real.sq_sqrt hG.le]
  have hsq : ‖hspQueryVec f‖ ^ 2 = 1 := by
    have h : ‖hspQueryVec f‖ ^ 2
        = ∑ _g : G, ‖(((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ)‖ ^ 2 := by
      unfold hspQueryVec
      exact (hspQueryFactor_orthonormal f).norm_sum_smul_sq _ _
    rw [h, Finset.sum_const, Finset.card_univ, hnorm, nsmul_eq_mul,
      mul_inv_cancel₀ (ne_of_gt hG)]
  nlinarith [norm_nonneg (hspQueryVec f), hsq]

/-- The **single-copy HSP query state** `|ψ_f⟩` (Nielsen & Chuang eq. 5.80, `m = 1`) as a
`PureState` of the composite system `groupSystem G ⊗ groupSystem X`. -/
def hspQueryState (f : G → X) : PureState ((groupSystem G).compose (groupSystem X)) where
  vec := hspQueryVec f
  normalized := hspQueryVec_norm f

@[simp]
theorem hspQueryState_vec (f : G → X) : (hspQueryState f).vec = hspQueryVec f := rfl

variable (K : Subgroup G) [DecidablePred (· ∈ K)]

/-- **Schmidt decomposition of the query state over cosets** (given the HSP promise `hf`):
`|ψ_f⟩ = ∑_{q ∈ G ⧸ K} √(|K|/|G|) |C_q⟩ |f(q̂)⟩`, with `q̂ = q.out` a representative of `q`. Since
`f` is constant on cosets, every `|g⟩` in coset `q` shares the label `|f(q̂)⟩`, and
`∑_{g ∈ q} |g⟩ = √|K| |C_q⟩` (`Concrete.sum_single_coset_eq_smul_cosetState`); the coefficient
combines as `|G|^{-1/2} · √|K| = √(|K|/|G|)`. -/
theorem hspQueryVec_eq_schmidt (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂) :
    hspQueryVec f = ∑ q : G ⧸ K, (((Real.sqrt (Fintype.card K / Fintype.card G) : ℝ)) : ℂ) •
      (Concrete.cosetState K q ⊗ₜ[ℂ] EuclideanSpace.single (f q.out) (1 : ℂ) :
        ((groupSystem G).compose (groupSystem X)).space) := by
  change (∑ g : G, (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) •
        (EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single (f g) (1 : ℂ)) :
          EuclideanSpace ℂ G ⊗[ℂ] EuclideanSpace ℂ X)
      = ∑ q : G ⧸ K, (((Real.sqrt (Fintype.card K / Fintype.card G) : ℝ)) : ℂ) •
        (Concrete.cosetState K q ⊗ₜ[ℂ] EuclideanSpace.single (f q.out) (1 : ℂ) :
          EuclideanSpace ℂ G ⊗[ℂ] EuclideanSpace ℂ X)
  rw [← Finset.sum_fiberwise (g := fun g : G => (↑g : G ⧸ K))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hrep : ∀ g ∈ Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q),
      EuclideanSpace.single (f g) (1 : ℂ) = EuclideanSpace.single (f q.out) (1 : ℂ) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    have : f g = f q.out := (hf g q.out).mpr (hg.2.trans (Quotient.out_eq q).symm)
    rw [this]
  have hscalar : (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) *
      ((Real.sqrt (Fintype.card K) : ℝ) : ℂ)
      = ((Real.sqrt (Fintype.card K / Fintype.card G) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.sqrt_div (by positivity), div_eq_mul_inv, mul_comm]
  calc ∑ g ∈ Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q),
          (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) •
            (EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single (f g) (1 : ℂ))
      = ∑ g ∈ Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q),
          (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) •
            (EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single (f q.out) (1 : ℂ)) :=
        Finset.sum_congr rfl fun g hg => by rw [hrep g hg]
    _ = (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) •
          ((∑ g ∈ Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q),
              EuclideanSpace.single g (1 : ℂ)) ⊗ₜ[ℂ] EuclideanSpace.single (f q.out) (1 : ℂ)) := by
        rw [← Finset.smul_sum, ← TensorProduct.sum_tmul]
    _ = (((Real.sqrt (Fintype.card G))⁻¹ : ℝ) : ℂ) •
          ((((Real.sqrt (Fintype.card K) : ℝ) : ℂ) • Concrete.cosetState K q) ⊗ₜ[ℂ]
            EuclideanSpace.single (f q.out) (1 : ℂ)) := by
        rw [Concrete.sum_single_coset_eq_smul_cosetState]
    _ = ((Real.sqrt (Fintype.card K / Fintype.card G) : ℝ) : ℂ) •
          (Concrete.cosetState K q ⊗ₜ[ℂ] EuclideanSpace.single (f q.out) (1 : ℂ)) := by
        rw [← TensorProduct.smul_tmul', smul_smul, hscalar]

/-- **The reduced state of the HSP query state on the group register is `σ_K`** (operator form,
the mathematical kernel of the reduced-state step of Nielsen & Chuang, Problem 5.5): tracing out
the range register `ℂ[X]` from `|ψ_f⟩⟨ψ_f|` leaves the coset density operator,
`Tr_{ℂ[X]} |ψ_f⟩⟨ψ_f| = σ_K = (cosetDensityState K).op`. The query state is the coset Schmidt
decomposition `∑_q √(|K|/|G|) |C_q⟩|f(q̂)⟩` (`hspQueryVec_eq_schmidt`); the range factors `|f(q̂)⟩`
are orthonormal (`f` is distinct across cosets), so the Schmidt partial-trace lemma yields
`∑_q (|K|/|G|) |C_q⟩⟨C_q|`, the spectral form of `σ_K` (`cosetDensityState_op_eq_sum`). The Schmidt
index is transported from `Fin |G ⧸ K|` to `G ⧸ K` via `Fintype.equivFin`. -/
theorem hspQueryState_reducedLeft_op (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂) :
    (hspQueryState f).toState.reducedLeft.op = (cosetDensityState K).op := by
  set e := Fintype.equivFin (G ⧸ K) with he
  have hnn : (0 : ℝ) ≤ (Fintype.card K / Fintype.card G : ℝ) := by positivity
  have hout : ∀ q : G ⧸ K, (↑(Quotient.out q) : G ⧸ K) = q := Quotient.out_eq
  have hforth : Orthonormal ℂ (fun i => (EuclideanSpace.single (f (e.symm i).out) (1 : ℂ) :
      (groupSystem X).space)) := by
    rw [orthonormal_iff_ite]
    intro i j
    erw [orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single
      (f (e.symm i).out) (f (e.symm j).out)]
    refine if_congr ?_ rfl rfl
    rw [hf, hout, hout, e.symm.injective.eq_iff]
  have hschmidt : hspQueryVec f = ∑ i, ((Real.sqrt (Fintype.card K / Fintype.card G) : ℝ) : ℂ) •
      (Concrete.cosetState K (e.symm i) ⊗ₜ[ℂ] EuclideanSpace.single (f (e.symm i).out) (1 : ℂ) :
        ((groupSystem G).compose (groupSystem X)).space) := by
    rw [hspQueryVec_eq_schmidt K f hf]
    exact (Equiv.sum_comp e.symm (fun q => ((Real.sqrt (Fintype.card K / Fintype.card G) : ℝ) : ℂ) •
      (Concrete.cosetState K q ⊗ₜ[ℂ] EuclideanSpace.single (f q.out) (1 : ℂ)))).symm
  apply ContinuousLinearMap.coe_injective
  rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op,
    hspQueryState_vec]
  refine Eq.trans (LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
    (stdOrthonormalBasis ℂ (groupSystem X).space)
    (fun _ => Real.sqrt (Fintype.card K / Fintype.card G))
    (fun i => Concrete.cosetState K (e.symm i))
    (fun i => EuclideanSpace.single (f (e.symm i).out) (1 : ℂ)) hforth hschmidt) ?_
  rw [cosetDensityState_op_eq_sum, ContinuousLinearMap.toLinearMap_sum]
  simp only [ContinuousLinearMap.toLinearMap_smul]
  rw [← Equiv.sum_comp e.symm (fun q => (((Fintype.card K / Fintype.card G : ℝ) : ℂ) •
      (↑((cosetPureState K q).toState.op) :
        ((groupSystem G).space →ₗ[ℂ] (groupSystem G).space))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PureState.toState_op, cosetPureState_vec, sq, ← RCLike.ofReal_mul,
    Real.mul_self_sqrt hnn]
  rfl

end AxQM
