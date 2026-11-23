/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspacePerCodeError
import AxQM.Postulates.API.CondTypicalSubspaceExpectation
import AxQM.Postulates.API.RandomCodingConfusionExpectation

/-!
# The random-coding expected per-code error of the HSW pretty-good decoder (N&C Thm 12.8)

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability, Box 12.5), Alice draws a length-`n` product-state codebook of `K`
messages by choosing every letter i.i.d. from an input ensemble `{pₐ, ρₐ}`; message `M`'s output
codeword is `σ_M = ⨂ᵢ E(ρ_{wᵢ})`.  The pretty-good (square-root) decoder's per-code average error
`p̄` is bounded, for each fixed codebook, by three physical traces (N&C eq. (12.79),
`State.avgError_prettyGood_le_re_trace_percode`):

`p̄ ≤ (1/K) ∑_M [3·re tr((1−P) σ_M) + 2·re tr((1−P_M) σ_M) + ∑_{M'≠M} re tr(P σ_M P P_{M'})]`.

This file takes the **random-coding expectation** `𝔼[·]` of that bound over the i.i.d. codebook,
producing N&C's eqs. (12.80)–(12.82): each of the three terms is averaged by its own
expectation lemma, and because the resulting bound is independent of `M` the outer `(1/K) ∑_M`
collapses.

## Main result

* `AxQM.State.expectation_avgError_prettyGood_le` — the **expected per-code error bound**:
  averaging the per-code bound over the random codebook `w : Fin K → Fin n → α`,

  `𝔼[p̄] ≤ 3·re tr((1−P) σ̄^⊗n) + 2·V/(n ε²) + (K−1)·exp(−n(S(σ̄) − s − 2ε))`,

  where `σ̄ = ∑ₐ pₐ E(ρₐ)` is the average output, `P = σ̄.typicalSubspaceProj n ε` its typical
  projector, and `V = ∑ₐ pₐ ∑_b λ_{a,b}(−log λ_{a,b} − s)²` the per-letter surprisal variance.

  The three terms come from:
  * the **typical-defect** term `𝔼[re tr((1−P) σ_M)] = re tr((1−P) σ̄^⊗n)`, the single-codeword
    marginal `Real.sum_pi_weight_mul_apply` folding the average output `𝔼[σ_M] = σ̄^⊗n`
    (`State.tensorPow_mix`) through the `ℝ`-linear `re ∘ tr` (`re_trace_finsetSum_real_smul`);
  * the **conditional-atypical** term `𝔼[re tr((1−P_M) σ_M)] ≤ V/(n ε²)`, the single-codeword
    marginal reducing it to `State.expectation_re_trace_one_sub_condTypicalSubspaceProj_le`
    (N&C eq. (12.76)); and
  * the **confusion** term `∑_{M'≠M} 𝔼[re tr(P σ_M P P_{M'})] ≤ (K−1)·exp(−n(S(σ̄)−s−2ε))`, the
    two-codeword independence marginal per pair
    (`State.expectation_re_trace_confusion_prettyGood_le`, N&C eq. (12.82)), summed over the `K−1`
    confusing messages.

  As `n → ∞` (with `ε` fixed) the typical-defect and atypical terms vanish, and for a rate
  `R < χ(E)` the confusion term `(K−1)·exp(…) ≈ e^{nR}·e^{−nχ}` vanishes too — the vanishing
  expected error that derandomises to an achievable rate (not carried out here).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eqs. (12.79)–(12.82).
-/

open scoped BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem} {α : Type*} [Fintype α]

/-- **The random-coding expected per-code error bound of the HSW pretty-good decoder** (Nielsen &
Chuang, Theorem 12.8, Box 12.5, eqs. (12.80)–(12.82)).  See the module docstring. -/
theorem State.expectation_avgError_prettyGood_le
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (n : ℕ) (hn : 0 < n) (s ε : ℝ) (hε : 0 < ε)
    (hs : s = ∑ a, p a * (E (ρ a)).vonNeumannEntropy)
    (P : (QSystem.piTensor fun _ : Fin n => S).space →L[ℂ]
        (QSystem.piTensor fun _ : Fin n => S).space)
    (hPsa : IsSelfAdjoint P) (hPidem : P.comp P = P)
    (hP : P = QSystem.tensorPow_eq S n ▸
      (State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceProj n ε)
    {K : ℕ} [NeZero K]
    (hA : ∀ (w : Fin K → Fin n → α) (M' : Fin K),
      (0 : (QSystem.piTensor fun _ : Fin n => S).space →L[ℂ]
          (QSystem.piTensor fun _ : Fin n => S).space)
        ≤ P.comp ((State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε).comp P)) :
    ∑ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) *
        ((K : ℝ)⁻¹ * ∑ M : Fin K, (1 - RCLike.re ((LinearMap.trace ℂ
            (QSystem.piTensor fun _ : Fin n => S).space)
          (↑((State.piTensor fun i => E (ρ (w M i))).op.comp
            ((POVM.prettyGood (fun M' => P.comp ((State.condTypicalSubspaceProj
              (fun i => E (ρ (w M' i))) s ε).comp P)) (hA w)).elements (some M))) :
            (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
              (QSystem.piTensor fun _ : Fin n => S).space))))
      ≤ 3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
            (↑((1 - P) * (QSystem.tensorPow_eq S n ▸
                ((State.mix p hp hsum fun a => E (ρ a)).tensorPow n).op)) :
              (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
                (QSystem.piTensor fun _ : Fin n => S).space))
        + 2 * ((∑ a, p a * ∑ b, (E (ρ a)).eigenvalueDist b *
            (- Real.log ((E (ρ a)).eigenvalueDist b) - s) ^ 2) / (n * ε ^ 2))
        + ((K : ℝ) - 1) * Real.exp (-(n : ℝ) *
            ((State.mix p hp hsum fun a => E (ρ a)).vonNeumannEntropy - s - 2 * ε)) := by
  classical
  set σbar := State.mix p hp hsum fun a => E (ρ a) with hσbar
  -- The i.i.d. length-`n` product weight is a probability distribution over codewords.
  have hWsum : ∑ v : Fin n → α, ∏ i, p (v i) = 1 := sum_iidProdWeight p hsum n
  -- The average output codeword: `σ̄^⊗n.op = ∑_v (∏ᵢ p_{vᵢ}) • (⨂ᵢ E(ρ_{vᵢ})).op`.
  have hop : (σbar.tensorPow n).op
      = ∑ v : Fin n → α, (↑(∏ i, p (v i)) : ℂ) • (State.piTensor fun i => E (ρ (v i))).op := by
    rw [hσbar, State.tensorPow_mix p hp hsum (fun a => E (ρ a)) n, State.mix_op]
  -- **(T1) Typical-defect term**: `𝔼[re tr((1−P) σ_M)] = re tr((1−P) σ̄^⊗n)`, via the single-
  -- codeword marginal folding the average output through the `ℝ`-linear `re ∘ tr`.
  have hT1 : ∀ _M : Fin K, ∑ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) *
        RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
          (↑((1 - P) * (State.piTensor fun i => E (ρ (w _M i))).op)))
      = RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
          (↑((1 - P) * (QSystem.tensorPow_eq S n ▸ (σbar.tensorPow n).op)))) := by
    intro M
    rw [Real.sum_pi_weight_mul_apply (fun v : Fin n → α => ∏ i, p (v i)) hWsum
      (fun v => RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
        (↑((1 - P) * (State.piTensor fun i => E (ρ (v i))).op)))) M]
    have hopP : (QSystem.tensorPow_eq S n ▸ (σbar.tensorPow n).op :
          (QSystem.piTensor fun _ : Fin n => S).space →L[ℂ]
            (QSystem.piTensor fun _ : Fin n => S).space)
        = ∑ v : Fin n → α, (↑(∏ i, p (v i)) : ℂ) • (State.piTensor fun i => E (ρ (v i))).op := hop
    rw [hopP]
    have hpull : (1 - P) * (∑ v : Fin n → α, (↑(∏ i, p (v i)) : ℂ) •
          (State.piTensor fun i => E (ρ (v i))).op)
        = ∑ v : Fin n → α, (↑(∏ i, p (v i)) : ℂ) •
          ((1 - P) * (State.piTensor fun i => E (ρ (v i))).op) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_finsetSum]
      exact Finset.sum_congr rfl fun v _ => by
        rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.mul_def]
    rw [hpull, re_trace_finsetSum_real_smul]
  -- **(T2) Conditional-atypical term**: `𝔼[re tr((1−P_M) σ_M)] ≤ V/(n ε²)` (N&C eq. (12.76)).
  have hT2 : ∀ _M : Fin K, ∑ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) *
        RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
          (↑((1 - State.condTypicalSubspaceProj (fun i => E (ρ (w _M i))) s ε) *
            (State.piTensor fun i => E (ρ (w _M i))).op)))
      ≤ (∑ a, p a * ∑ b, (E (ρ a)).eigenvalueDist b *
          (- Real.log ((E (ρ a)).eigenvalueDist b) - s) ^ 2) / (n * ε ^ 2) := by
    intro M
    rw [Real.sum_pi_weight_mul_apply (fun v : Fin n → α => ∏ i, p (v i)) hWsum
      (fun v => RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
        (↑((1 - State.condTypicalSubspaceProj (fun i => E (ρ (v i))) s ε) *
          (State.piTensor fun i => E (ρ (v i))).op)))) M]
    simp only [ContinuousLinearMap.mul_def]
    exact State.expectation_re_trace_one_sub_condTypicalSubspaceProj_le (fun a => E (ρ a)) p hp hsum
      hn hε hs
  -- **(T3) Confusion term** (per confusing message `M' ≠ M`): `𝔼[re tr(P σ_M P P_{M'})] ≤ exp(…)`.
  have hT3 : ∀ (M M' : Fin K), M ≠ M' → ∑ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) *
        RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
          (↑(P.comp ((State.piTensor fun i => E (ρ (w M i))).op.comp
            (P.comp (State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε))))))
      ≤ Real.exp (-(n : ℝ) * (σbar.vonNeumannEntropy - s - 2 * ε)) := by
    intro M M' hMM'
    exact State.expectation_re_trace_confusion_prettyGood_le p hp hsum E ρ n s ε P hP hMM'
  -- Weight the pointwise per-code bound over the random codebook.
  refine le_trans (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
    (State.avgError_prettyGood_le_re_trace_percode (fun M i => E (ρ (w M i))) s ε P hPsa hPidem
      (hA w))
    (Finset.prod_nonneg fun M'' _ => Finset.prod_nonneg fun i _ => hp _)) ?_
  -- Pull out `(1/K)` and swap the codebook/message sums.
  have hrearrange : ∀ f : (Fin K → Fin n → α) → Fin K → ℝ,
      (∑ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) * ((K : ℝ)⁻¹ * ∑ M, f w M))
        = (K : ℝ)⁻¹ * ∑ M, ∑ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) * f w M := by
    intro f
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun w _ => by ring
  rw [hrearrange]
  -- The target bound is `M`-independent, so `(1/K) ∑_{M : Fin K}` of it collapses.
  have hcollapse : ∀ c : ℝ, (K : ℝ)⁻¹ * ∑ _M : Fin K, c = c := fun c => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne K)), one_mul]
  rw [← hcollapse (3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
        (↑((1 - P) * (QSystem.tensorPow_eq S n ▸ (σbar.tensorPow n).op)) :
          (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
            (QSystem.piTensor fun _ : Fin n => S).space))
      + 2 * ((∑ a, p a * ∑ b, (E (ρ a)).eigenvalueDist b *
          (- Real.log ((E (ρ a)).eigenvalueDist b) - s) ^ 2) / (n * ε ^ 2))
      + ((K : ℝ) - 1) * Real.exp (-(n : ℝ) * (σbar.vonNeumannEntropy - s - 2 * ε)))]
  gcongr with M
  -- Per-message bound: the expectation of the three-trace bracket `≤` the target constant.
  -- Distribute the codebook weight over the bracket, term by term.
  have step : ∀ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) *
        (3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
              (↑((1 - P) * (State.piTensor fun i => E (ρ (w M i))).op)))
          + 2 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
              (↑((1 - State.condTypicalSubspaceProj (fun i => E (ρ (w M i))) s ε) *
                (State.piTensor fun i => E (ρ (w M i))).op)))
          + ∑ M' ∈ Finset.univ.erase M, RCLike.re
              ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
              (↑(P.comp ((State.piTensor fun i => E (ρ (w M i))).op.comp
                (P.comp (State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε)))))))
      = 3 * ((∏ M'' : Fin K, ∏ i, p (w M'' i)) *
            RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
              (↑((1 - P) * (State.piTensor fun i => E (ρ (w M i))).op))))
        + 2 * ((∏ M'' : Fin K, ∏ i, p (w M'' i)) *
            RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
              (↑((1 - State.condTypicalSubspaceProj (fun i => E (ρ (w M i))) s ε) *
                (State.piTensor fun i => E (ρ (w M i))).op))))
        + ∑ M' ∈ Finset.univ.erase M, (∏ M'' : Fin K, ∏ i, p (w M'' i)) * RCLike.re
            ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
            (↑(P.comp ((State.piTensor fun i => E (ρ (w M i))).op.comp
              (P.comp (State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε)))))) := by
    intro w
    rw [mul_add, mul_add, Finset.mul_sum]; ring
  rw [Finset.sum_congr rfl fun w _ => step w, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm, hT1 M]
  -- The confusion block: each of the `K − 1` distinct messages contributes `≤ exp(…)`.
  have hconf : ∑ M' ∈ Finset.univ.erase M, ∑ w : Fin K → Fin n → α,
        (∏ M'' : Fin K, ∏ i, p (w M'' i)) *
        RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
          (↑(P.comp ((State.piTensor fun i => E (ρ (w M i))).op.comp
            (P.comp (State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε))))))
      ≤ ((K : ℝ) - 1) * Real.exp (-(n : ℝ) * (σbar.vonNeumannEntropy - s - 2 * ε)) := by
    refine le_trans (Finset.sum_le_sum fun M' hM' => hT3 M M' (Finset.ne_of_mem_erase hM').symm) ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ M), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)),
      Nat.cast_one]
  linarith [hT2 M, hconf]

end AxQM
