/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumChoiKraus

/-!
# Assembling the reverse direction of the operator-sum theorem (Theorem 8.1)

This file completes the reverse direction of the operator-sum representation theorem
(Nielsen–Chuang Theorem 8.1, *Quantum Computation and Quantum Information*, §8.2.4, Eqs.
(8.64)–(8.65)). Its predecessor `ToMathlib.Analysis.InnerProductSpace.OperatorSumChoiKraus`
established, for a **completely positive** superoperator `Φ`, a finite family of operation elements
`E` such that `Φ(|ψ⟩⟨ψ|) = Σᵢ Eᵢ |ψ⟩⟨ψ| Eᵢ†` holds on every **pure** state
(`ContinuousLinearMap.IsCompletelyPositive.exists_krausSumₗ_apply_rankOne`). Two steps remain, and
this file supplies both:

* **Extension to all operators (N&C Eq. (8.65), "by convex-linearity").** Two `ℂ`-linear
  superoperators that agree on all rank-one self-projectors `|ψ⟩⟨ψ|` agree everywhere, since the
  `|ψ⟩⟨ψ|` span the whole operator space. The spanning is a **polarization identity**
  (`InnerProductSpace.rankOne_eq_inv_four_smul_sum`): every rank-one operator `|x⟩⟨y|` is a
  `ℂ`-combination of four self-projectors `|x + iᵏy⟩⟨x + iᵏy|`, and every operator is a sum of
  rank-one operators over a basis. This upgrades the pure-state equality to `Φ = krausSumₗ E`.
* **The trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1` (N&C axiom A1).** From trace-non-increasing
  (`IsTraceNonIncreasing (krausSumₗ E)`), testing against the state `|x⟩⟨x|` and using the trace
  identity `tr(krausSumₗ E |x⟩⟨x|) = ⟪x, (Σᵢ Eᵢ† Eᵢ) x⟫` gives `re⟪x, (Σᵢ Eᵢ† Eᵢ) x⟫ ≤ ‖x‖²` for
  all `x`, i.e. `1 − Σᵢ Eᵢ† Eᵢ ≥ 0`.

## Main results

* `InnerProductSpace.rankOne_add_smul_self` — the bilinear expansion
  `|x + c y⟩⟨x + c y| = |x⟩⟨x| + c̄ |x⟩⟨y| + c |y⟩⟨x| + |c|² |y⟩⟨y|`.
* `InnerProductSpace.rankOne_eq_inv_four_smul_sum` — the **polarization identity**
  `|x⟩⟨y| = ¼ Σ_{k<4} iᵏ |x + iᵏ y⟩⟨x + iᵏ y|`, writing a rank-one operator as a `ℂ`-combination of
  rank-one self-projectors.
* `InnerProductSpace.superop_ext_of_forall_rankOne_self` — a `ℂ`-linear map out of the operator
  space `H →L[ℂ] H` is determined by its values on the self-projectors `|ψ⟩⟨ψ|`.
* `ContinuousLinearMap.sum_adjoint_comp_le_one_of_isTraceNonIncreasing` — a trace-non-increasing
  operator-sum map `krausSumₗ E` satisfies the trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`.
* `ContinuousLinearMap.SatisfiesOperationAxioms.isOperatorSum` — **N&C Theorem 8.1, reverse
  direction (`⇒`):** a superoperator satisfying the operation axioms A1, A2, A3 admits an
  operator-sum (Kraus) representation `IsOperatorSum E Φ` with at most `d²` operation elements.

Everything here is general finite-dimensional complex Hilbert-space operator mathematics (the
Choi–Kraus theorem).
-/

open scoped TensorProduct InnerProductSpace ComplexConjugate
open ContinuousLinearMap InnerProductSpace

noncomputable section

@[expose] public section

namespace InnerProductSpace

section Polarization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Bilinear expansion of a rank-one self-projector along a shifted vector.** Expanding
`|x + c y⟩⟨x + c y|` by the (conjugate-)bilinearity of `rankOne` gives
`|x⟩⟨x| + c̄ |x⟩⟨y| + c |y⟩⟨x| + (c c̄) |y⟩⟨y|`, the conjugate `c̄` appearing on the second
(ket-conjugate) slot. This is the per-term building block of the polarization identity. -/
theorem rankOne_add_smul_self (x y : H) (c : ℂ) :
    rankOne ℂ (x + c • y) (x + c • y)
      = rankOne ℂ x x + (starRingEnd ℂ c) • rankOne ℂ x y + c • rankOne ℂ y x
        + (c * starRingEnd ℂ c) • rankOne ℂ y y := by
  simp only [map_add, map_smul, map_smulₛₗ, _root_.add_apply,
    _root_.smul_apply]
  module

/-- **Polarization identity for rank-one operators** (Nielsen–Chuang §8.2.4, the algebraic content
of "by convex-linearity", Eq. (8.65)). Every rank-one operator `|x⟩⟨y|` is a `ℂ`-linear combination
of the four rank-one self-projectors `|x + iᵏ y⟩⟨x + iᵏ y|`:
`|x⟩⟨y| = ¼ Σ_{k<4} iᵏ |x + iᵏ y⟩⟨x + iᵏ y|`.
In particular the self-projectors `|ψ⟩⟨ψ|` span the whole operator space. Proved by expanding each
diagonal term with `rankOne_add_smul_self` and collecting the four complex coefficients
(`Σ iᵏ = 0`, `Σ iᵏ · i̅ᵏ = 4`, `Σ i²ᵏ = 0`). -/
theorem rankOne_eq_inv_four_smul_sum (x y : H) :
    rankOne ℂ x y = (4⁻¹ : ℂ) •
      (rankOne ℂ (x + y) (x + y)
        + Complex.I • rankOne ℂ (x + Complex.I • y) (x + Complex.I • y)
        - rankOne ℂ (x - y) (x - y)
        - Complex.I • rankOne ℂ (x - Complex.I • y) (x - Complex.I • y)) := by
  have e1 : x + y = x + (1 : ℂ) • y := by rw [one_smul]
  have e2 : x - y = x + (-1 : ℂ) • y := by rw [neg_one_smul, ← sub_eq_add_neg]
  have e3 : x - Complex.I • y = x + (-Complex.I) • y := by rw [neg_smul, ← sub_eq_add_neg]
  rw [e1, e2, e3, rankOne_add_smul_self, rankOne_add_smul_self, rankOne_add_smul_self,
    rankOne_add_smul_self]
  simp only [map_one, map_neg, Complex.conj_I, smul_add, smul_smul, mul_one, mul_neg,
    neg_mul, Complex.I_mul_I, neg_neg]
  module

end Polarization

section Extension

variable {H X : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [AddCommGroup X] [Module ℂ X]

/-- **A superoperator is determined by its values on pure states.** Two `ℂ`-linear maps
`Φ, Ψ : (H →L[ℂ] H) →ₗ[ℂ] X` out of the operator space that agree on every rank-one self-projector
`|ψ⟩⟨ψ|` are equal. This is the "extension by convex-linearity" of Nielsen–Chuang Eq. (8.65):
polarization (`rankOne_eq_inv_four_smul_sum`) lifts the agreement from self-projectors to all
rank-one operators `|x⟩⟨y|`, and every operator `ρ` is the basis sum `Σₖ |ρ eₖ⟩⟨eₖ|`
(`OrthonormalBasis.sum_rankOne_eq_id` composed with `ρ`, via `comp_rankOne`). -/
theorem superop_ext_of_forall_rankOne_self {Φ Ψ : (H →L[ℂ] H) →ₗ[ℂ] X}
    (h : ∀ ψ : H, Φ (rankOne ℂ ψ ψ) = Ψ (rankOne ℂ ψ ψ)) :
    Φ = Ψ := by
  -- Step 1: `Φ` and `Ψ` agree on every rank-one operator, by polarization. The four self-projectors
  -- are `set` first so that `map_add`/`map_smul` distribute `Φ`, `Ψ` over the polarization
  -- combination without expanding the (linear) `rankOne` in its argument.
  have key : ∀ x y : H, Φ (rankOne ℂ x y) = Ψ (rankOne ℂ x y) := by
    intro x y
    rw [rankOne_eq_inv_four_smul_sum x y]
    set t0 := rankOne ℂ (x + y) (x + y) with ht0
    set t1 := rankOne ℂ (x + Complex.I • y) (x + Complex.I • y) with ht1
    set t2 := rankOne ℂ (x - y) (x - y) with ht2
    set t3 := rankOne ℂ (x - Complex.I • y) (x - Complex.I • y) with ht3
    have e0 : Φ t0 = Ψ t0 := by rw [ht0]; exact h (x + y)
    have e1 : Φ t1 = Ψ t1 := by rw [ht1]; exact h (x + Complex.I • y)
    have e2 : Φ t2 = Ψ t2 := by rw [ht2]; exact h (x - y)
    have e3 : Φ t3 = Ψ t3 := by rw [ht3]; exact h (x - Complex.I • y)
    simp only [map_smul, map_add, map_sub, e0, e1, e2, e3]
  -- Step 2: extend to every operator `ρ`, written as a basis sum of rank-one operators.
  ext ρ
  set b := stdOrthonormalBasis ℂ H with hb
  have hρ : ρ = ∑ i, rankOne ℂ (ρ (b i)) (b i) := by
    calc ρ = ρ.comp (ContinuousLinearMap.id ℂ H) := (ρ.comp_id).symm
      _ = ρ.comp (∑ i, rankOne ℂ (b i) (b i)) := by rw [b.sum_rankOne_eq_id]
      _ = ∑ i, ρ.comp (rankOne ℂ (b i) (b i)) := by rw [ContinuousLinearMap.comp_finsetSum]
      _ = ∑ i, rankOne ℂ (ρ (b i)) (b i) :=
        Finset.sum_congr rfl fun i _ => InnerProductSpace.comp_rankOne (b i) (b i) ρ
  rw [hρ, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => key _ _

end Extension

end InnerProductSpace

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]
  {ι : Type*} [Fintype ι]

/-- **The operator-sum trace condition from trace-non-increasing (Nielsen–Chuang axiom A1).** If the
operator-sum map `krausSumₗ E` is trace-non-increasing (`re tr(Σᵢ Eᵢ ρ Eᵢ†) ≤ re tr ρ` for every
positive `ρ`), then its operation elements satisfy the trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`. The converse
of `krausSumₗ_isTraceNonIncreasing`. Testing at the positive operator `ρ = |x⟩⟨x|`, the trace
identity `trace_krausSumₗ` and `comp_rankOne`/`trace_rankOne` recast the hypothesis as
`re⟪x, (Σᵢ Eᵢ† Eᵢ) x⟫ ≤ re⟪x, x⟫` for all `x`; with `A := Σᵢ Eᵢ† Eᵢ` positive (hence self-adjoint),
`1 − A` is self-adjoint with `reApplyInnerSelf (1 − A) x = re⟪x, x⟫ − re⟪x, A x⟫ ≥ 0`, so
`(1 − A).IsPositive`, i.e. `A ≤ 1`. -/
theorem sum_adjoint_comp_le_one_of_isTraceNonIncreasing (E : ι → H →L[ℂ] G)
    (h : IsTraceNonIncreasing (krausSumₗ E)) :
    ∑ i, adjoint (E i) ∘L E i ≤ 1 := by
  set A : H →L[ℂ] H := ∑ i, adjoint (E i) ∘L E i with hA
  have hApos : A.IsPositive :=
    isPositive_sum _ fun i _ => isPositive_adjoint_comp_self (E i)
  -- The pairing bound `re⟪x, A x⟫ ≤ re⟪x, x⟫`, obtained by testing A1 at the state `|x⟩⟨x|`.
  have hbound : ∀ x : H, RCLike.re ⟪x, A x⟫_ℂ ≤ RCLike.re ⟪x, x⟫_ℂ := by
    intro x
    have hpos : (0 : H →L[ℂ] H) ≤ rankOne ℂ x x :=
      nonneg_iff_isPositive.2 (isPositive_rankOne_self x)
    have h1 := h (rankOne ℂ x x) hpos
    rw [trace_krausSumₗ, ← hA] at h1
    -- `A ∘L |x⟩⟨x| = |A x⟩⟨x|`, whose trace is `⟪x, A x⟫`; and `tr|x⟩⟨x| = ⟪x, x⟫`.
    rw [comp_rankOne x x A, InnerProductSpace.trace_rankOne, InnerProductSpace.trace_rankOne] at h1
    exact h1
  -- `A ≤ 1`, i.e. `(1 - A).IsPositive`.
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def]
  refine ⟨?_, fun x => ?_⟩
  · rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact (IsSelfAdjoint.one (H →L[ℂ] H)).sub
      ((ContinuousLinearMap.isPositive_iff' A).mp hApos).1
  · have hre : (1 - A).reApplyInnerSelf x = RCLike.re ⟪x, x⟫_ℂ - RCLike.re ⟪x, A x⟫_ℂ := by
      simp only [ContinuousLinearMap.reApplyInnerSelf, _root_.sub_apply,
        one_apply_eq_self, inner_sub_left, map_sub]
      rw [← inner_conj_symm x (A x), RCLike.conj_re]
    rw [hre]
    linarith [hbound x]

/-- **The operator-sum completeness relation from trace preservation (Nielsen–Chuang Eq. (8.33)).**
If the operator-sum map `krausSumₗ E` is *trace-preserving* (`tr(Σᵢ Eᵢ ρ Eᵢ†) = tr ρ` for every
operator `ρ`), then its operation elements obey the **completeness relation** `Σᵢ Eᵢ† Eᵢ = 1` — the
equality sharpening of `sum_adjoint_comp_le_one_of_isTraceNonIncreasing` (`≤`) available when the
channel is deterministic. Testing at `ρ = |x⟩⟨x|`, the trace identity `trace_krausSumₗ` with
`comp_rankOne`/`trace_rankOne` recasts the hypothesis as `⟪x, (Σᵢ Eᵢ† Eᵢ) x⟫ = ⟪x, x⟫` for every
`x`; hence `⟪(A − 1) x, x⟫ = 0` for `A := Σᵢ Eᵢ† Eᵢ` (using conjugate symmetry), so `A − 1 = 0` by
nondegeneracy of the inner product (`inner_map_self_eq_zero`). -/
theorem sum_adjoint_comp_eq_one_of_trace_krausSumₗ_eq (E : ι → H →L[ℂ] G)
    (h : ∀ ρ : H →L[ℂ] H,
      LinearMap.trace ℂ G ↑(krausSumₗ E ρ) = LinearMap.trace ℂ H ↑ρ) :
    ∑ i, adjoint (E i) ∘L E i = 1 := by
  set A : H →L[ℂ] H := ∑ i, adjoint (E i) ∘L E i with hA
  -- `⟪x, A x⟫ = ⟪x, x⟫` for all `x`, by testing trace preservation at the state `|x⟩⟨x|`.
  have hpair : ∀ x : H, (⟪x, A x⟫_ℂ : ℂ) = ⟪x, x⟫_ℂ := by
    intro x
    have h1 := h (rankOne ℂ x x)
    rwa [trace_krausSumₗ, ← hA, comp_rankOne x x A, InnerProductSpace.trace_rankOne,
      InnerProductSpace.trace_rankOne] at h1
  -- Its conjugate form `⟪A x, x⟫ = ⟪x, x⟫`.
  have hpair2 : ∀ x : H, (⟪A x, x⟫_ℂ : ℂ) = ⟪x, x⟫_ℂ := by
    intro x
    rw [← inner_conj_symm (A x) x, hpair x, inner_conj_symm]
  -- `A - 1 = 0`, so `A = 1`.
  have hLM : ((A - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0 := by
    rw [← inner_map_self_eq_zero]
    intro x
    have hx : ((A - 1 : H →L[ℂ] H) x) = A x - x := by
      rw [_root_.sub_apply, one_apply_eq_self]
    rw [ContinuousLinearMap.coe_coe, hx, inner_sub_left, hpair2 x, sub_self]
  rw [ContinuousLinearMap.toLinearMap_sub, sub_eq_zero] at hLM
  exact ContinuousLinearMap.coe_injective hLM

/-- **Nielsen–Chuang Theorem 8.1, reverse direction (`⇒`): a quantum operation admits an
operator-sum representation.** A superoperator `Φ` satisfying the operation axioms A1, A2, A3
(`SatisfiesOperationAxioms`) has an operator-sum (Kraus) representation `IsOperatorSum E Φ` — a
finite family of at most `d² = finrank ℂ (H ⊗ G)` operation elements `E` with `Φ = krausSumₗ E` and
`Σᵢ Eᵢ† Eᵢ ≤ 1`.

Complete positivity provides, via the Choi construction, a family agreeing with `Φ` on the pure
states (`IsCompletelyPositive.exists_krausSumₗ_apply_rankOne`); `superop_ext_of_forall_rankOne_self`
upgrades this to the map equality `Φ = krausSumₗ E`, and
`sum_adjoint_comp_le_one_of_isTraceNonIncreasing` derives the trace condition from axiom A1.
Together with the forward direction `IsOperatorSum.satisfiesAxioms` this is the full equivalence
of Theorem 8.1. -/
theorem SatisfiesOperationAxioms.isOperatorSum {Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)}
    (hΦ : SatisfiesOperationAxioms Φ) :
    ∃ E : Fin (Module.finrank ℂ (H ⊗[ℂ] G)) → (H →L[ℂ] G), IsOperatorSum E Φ := by
  obtain ⟨hCP, hTNI⟩ := hΦ
  obtain ⟨E, hE⟩ := hCP.exists_krausSumₗ_apply_rankOne (stdOrthonormalBasis ℂ H)
  have heq : Φ = krausSumₗ E := InnerProductSpace.superop_ext_of_forall_rankOne_self hE
  refine ⟨E, heq, ?_⟩
  rw [heq] at hTNI
  exact sum_adjoint_comp_le_one_of_isTraceNonIncreasing E hTNI

end ContinuousLinearMap
