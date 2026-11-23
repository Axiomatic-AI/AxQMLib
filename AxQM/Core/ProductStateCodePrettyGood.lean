/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ProductStateCode
import AxQM.Core.HolevoChi
import AxQM.Postulates.API.PrettyGoodDecoder
import AxQM.Postulates.API.RandomCodingExpectedError
import AxQM.Postulates.API.TensorPowMix
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyPinching
import ToMathlib.InformationTheory.TypicalSequence

/-!
# The pretty-good product-state code and its derandomized per-block error bound (N&C Thm 12.8)

The random-coding (achievability) half of the Holevo–Schumacher–Westmoreland theorem (Nielsen &
Chuang, Theorem 12.8, Box 12.5) builds, for each block length `n` and message count `K`, a
**product-state code** whose codewords are drawn i.i.d. from an input ensemble `{pₐ, ρₐ}` and which
Bob decodes with the **pretty-good (square-root) measurement** of the codeword family, projected
onto the average-output typical subspace.  This file packages that construction and turns the
random-coding *expectation* bound (eqs. (12.79)–(12.82),
`State.expectation_avgError_prettyGood_le`) into a **single concrete code** via derandomization.

## Main definitions and results

* `AxQM.ProductStateCode.prettyGood` — for an ensemble `{pₐ, ρₐ}`, channel `E`, block
  length `n`, parameters `s, ε`, and a codebook `w : Fin K → Fin n → α`, the product-state code
  whose encoder sends message `M` to the letters `ρ_{w M 0}, …, ρ_{w M (n-1)}` and whose decoder
  is the pretty-good measurement `Measurement.ofPOVM (POVM.prettyGood A)` of the conjugated family
  `A_{M'} = P · P_{M'} · P` (`P` the average-output typical projector, `P_{M'}` the conditional
  typical projector of codeword `M'`, N&C eq. (12.78)).

* `AxQM.ProductStateCode.exists_const_avgError_prettyGood_le` — the **derandomized
  per-block average-error bound**: for an ensemble `{pₐ, ρₐ}` and `ε > 0` there is a constant
  `C ≥ 0` (depending only on the ensemble and `ε`) such that for every block length `n ≥ 1` and
  message count `K ≥ 1` there is a product-state code `c : ProductStateCode E n K` with

  `p̄(c)  ≤  C / n  +  (K − 1)·exp(−n·(χ({pₐ, E(ρₐ)}) − 2ε))`,

  where `χ({pₐ, E(ρₐ)})` is the output-ensemble Holevo χ (`State.holevoChi`).  This is the whole
  random-coding error estimate collapsed to one code:

  1. **Construct** the pretty-good code family `codeₙ,ₖ(w) = ProductStateCode.prettyGood …`; its
     average error `p̄(codeₙ,ₖ(w)) = (1/K) ∑_M (1 − Tr(σ_M E_M))` matches the per-code bracket of
     the expectation bound (`Measurement.ofPOVM_bornProb_eq_re_trace` plus trace cyclicity).
  2. **Average** over the i.i.d. codebook (`State.expectation_avgError_prettyGood_le`, eqs.
     (12.79)–(12.82)): `𝔼_w[p̄] ≤ 3·Tr((1−P) σ̄^⊗n) + 2·V/(n ε²) + (K−1)·exp(−n(S(σ̄) − s − 2ε))`.
  3. **Derandomize** (`Real.exists_le_of_weighted_sum_le`): the i.i.d. weights are a probability
     distribution over codebooks, so some codebook `w` has `p̄(codeₙ,ₖ(w)) ≤ 𝔼_w[p̄]`.
  4. **Bound the three terms**: the typical-defect trace `Tr((1−P) σ̄^⊗n) = 1 − Pr[σ̄^⊗n typical]`
     (`State.re_trace_one_sub_avgOutputTypicalProj_tensorPow_eq`) is at most `V_σ̄/(n ε²)` by the
     classical typicality bound (`Real.sum_typicalSeq_ge`), so the first two terms fold into `C/n`
     with `C = (3·V_σ̄ + 2·V)/ε²`; and `S(σ̄) − s = χ({pₐ, E(ρₐ)})` (`State.holevoChi_def`).

  The bound is used for the achievability direction: with
  `K = ⌈eⁿᴿ⌉` and `2ε < χ({pₐ, E(ρₐ)}) − R`, both terms tend to `0`, so `R` is average-achievable.


## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eqs. (12.78)–(12.83).
-/

open scoped BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem} {α : Type*} [Fintype α]

/-- **The pretty-good product-state code** (Nielsen & Chuang, Theorem 12.8, Box 12.5, eq. (12.78)).
For an input ensemble `{pₐ, ρₐ}` (`ρ : α → State S`), channel `E`, block length `n`, entropy
parameter `s`, threshold `ε`, and a codebook `w : Fin K → Fin n → α`, this is the product-state
code whose

* **encoder** sends message `M` to the single-use inputs `ρ_{w M 0}, …, ρ_{w M (n−1)}` (so the
  output codeword is `σ_M = ⨂ᵢ E(ρ_{w M i})`); and
* **decoder** is the pretty-good (square-root) measurement `Measurement.ofPOVM (POVM.prettyGood A)`
  of the conjugated projector family `A_{M'} = P · P_{M'} · P`, where `P = avgOutputTypicalProj …`
  is the average-output ε-typical subspace projector and `P_{M'} = condTypicalSubspaceProj …` the
  conditional typical projector of codeword `M'`; the required positivity `0 ≤ A_{M'}` is
  `State.avgOutputTypicalProj_condTypical_conj_nonneg`. -/
def ProductStateCode.prettyGood (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (n : ℕ) (s ε : ℝ) {K : ℕ}
    (w : Fin K → Fin n → α) : ProductStateCode E n K where
  encoder := fun M i => ρ (w M i)
  decoder := prettyGoodDecoder p hp hsum E ρ n s ε w

/-- **The derandomized per-block average-error bound of the HSW pretty-good code** (Nielsen &
Chuang, Theorem 12.8, Box 12.5, eqs. (12.79)–(12.83)).  See the module docstring for the four steps
(construct → average → derandomize → bound the three terms). -/
theorem ProductStateCode.exists_const_avgError_prettyGood_le
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (s ε : ℝ) (hε : 0 < ε)
    (hs : s = ∑ a, p a * (E (ρ a)).vonNeumannEntropy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n → ∀ (K : ℕ), 0 < K →
      ∃ c : ProductStateCode E n K, c.avgError ≤
        C / (n : ℝ) + ((K : ℝ) - 1) *
          Real.exp (-(n : ℝ) * (State.holevoChi p hp hsum (fun a => E (ρ a)) - 2 * ε)) := by
  classical
  refine ⟨(3 * (∑ x, (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x *
          (-Real.log ((State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x)
            - Real.entropy (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist) ^ 2)
        + 2 * (∑ a, p a * ∑ b, (E (ρ a)).eigenvalueDist b *
            (-Real.log ((E (ρ a)).eigenvalueDist b) - s) ^ 2)) / ε ^ 2, ?_, ?_⟩
  · -- `0 ≤ C`: both surprisal variances are nonnegative and `ε² ≥ 0`.
    refine div_nonneg ?_ (sq_nonneg ε)
    have hVbar : 0 ≤ ∑ x, (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x *
        (-Real.log ((State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x)
          - Real.entropy (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist) ^ 2 :=
      Finset.sum_nonneg fun x _ =>
        mul_nonneg ((State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist_nonneg x) (sq_nonneg _)
    have hV : 0 ≤ ∑ a, p a * ∑ b, (E (ρ a)).eigenvalueDist b *
        (-Real.log ((E (ρ a)).eigenvalueDist b) - s) ^ 2 :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hp a)
        (Finset.sum_nonneg fun b _ => mul_nonneg ((E (ρ a)).eigenvalueDist_nonneg b) (sq_nonneg _))
    linarith
  intro n hn K hK
  have : NeZero K := ⟨hK.ne'⟩
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
  -- Step 2: the random-coding expected per-code error bound (eqs. (12.80)–(12.82)).
  have hexp := State.expectation_avgError_prettyGood_le p hp hsum E ρ n hn s ε hε hs
    (State.avgOutputTypicalProj p hp hsum E ρ n ε)
    (State.avgOutputTypicalProj_isSelfAdjoint p hp hsum E ρ n ε)
    (State.avgOutputTypicalProj_idem p hp hsum E ρ n ε)
    (State.avgOutputTypicalProj_eq p hp hsum E ρ n ε) (K := K)
    (fun w M' => State.avgOutputTypicalProj_condTypical_conj_nonneg p hp hsum E ρ n ε
      (fun i => E (ρ (w M' i))) s ε)
  -- The i.i.d. codebook weights are a probability distribution.
  have hW0 : ∀ w : Fin K → Fin n → α, 0 ≤ ∏ M'' : Fin K, ∏ i, p (w M'' i) :=
    fun w => Finset.prod_nonneg fun M'' _ => Finset.prod_nonneg fun i _ => hp _
  have hW1 : ∑ w : Fin K → Fin n → α, ∏ M'' : Fin K, ∏ i, p (w M'' i) = 1 := by
    have key := Finset.prod_univ_sum (fun _ : Fin K => (Finset.univ : Finset (Fin n → α)))
      (fun (_ : Fin K) (v : Fin n → α) => ∏ i, p (v i))
    rw [Fintype.piFinset_univ] at key
    rw [← key, Finset.prod_congr rfl fun M'' _ => sum_iidProdWeight p hsum n,
      Finset.prod_const_one]
  -- Step 1: the pretty-good code's average error equals the per-code trace bracket.
  have havg : ∀ w : Fin K → Fin n → α,
      (ProductStateCode.prettyGood p hp hsum E ρ n s ε w).avgError
        = (K : ℝ)⁻¹ * ∑ M : Fin K, (1 - RCLike.re ((LinearMap.trace ℂ
            (QSystem.piTensor fun _ : Fin n => S).space)
          (↑((State.piTensor fun i => E (ρ (w M i))).op.comp
            ((POVM.prettyGood (fun M' => (State.avgOutputTypicalProj p hp hsum E ρ n ε).comp
              ((State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε).comp
                (State.avgOutputTypicalProj p hp hsum E ρ n ε)))
              (fun M' => State.avgOutputTypicalProj_condTypical_conj_nonneg p hp hsum E ρ n ε
                (fun i => E (ρ (w M' i))) s ε)).elements (some M))) :
            (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
              (QSystem.piTensor fun _ : Fin n => S).space))) := by
    intro w
    rw [ProductStateCode.avgError, div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [ProductStateCode.errorProb, ProductStateCode.successProb]
    congr 1
    simp only [ProductStateCode.prettyGood, ProductStateCode.outputCodeword, prettyGoodDecoder]
    erw [Measurement.ofPOVM_bornProb_eq_re_trace]
    congr 1
    exact ContinuousLinearMap.trace_toLinearMap_mul_comm _ _
  -- Step 3: derandomize — some codebook `w` beats the expectation.
  obtain ⟨w, hw⟩ := Real.exists_le_of_weighted_sum_le _ hW0 hW1
    (fun w => (ProductStateCode.prettyGood p hp hsum E ρ n s ε w).avgError) _
    (le_of_eq_of_le (Finset.sum_congr rfl fun w _ => by simp only [havg w]) hexp)
  refine ⟨ProductStateCode.prettyGood p hp hsum E ρ n s ε w, hw.trans ?_⟩
  -- Step 4: bound the three terms.  Typical-defect term `Tr((1−P) σ̄^⊗n) ≤ V_σ̄/(n ε²)`.
  have hterm1 : 3 * RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
        (↑((1 - State.avgOutputTypicalProj p hp hsum E ρ n ε) *
            (QSystem.tensorPow_eq S n ▸
              ((State.mix p hp hsum fun a => E (ρ a)).tensorPow n).op)) :
          (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
            (QSystem.piTensor fun _ : Fin n => S).space))
      ≤ 3 * ((∑ x, (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x *
          (-Real.log ((State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x)
            - Real.entropy (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist) ^ 2)
        / ((n : ℝ) * ε ^ 2)) := by
    rw [State.re_trace_one_sub_avgOutputTypicalProj_tensorPow_eq p hp hsum E ρ n ε,
      (State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceMeasurement_bornProb_true n ε]
    have hge := Real.sum_typicalSeq_ge (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist_nonneg
      (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist_sum_eq_one hn hε
    linarith
  -- `S(σ̄) − s = χ({pₐ, E(ρₐ)})`.
  have hgap : (State.mix p hp hsum fun a => E (ρ a)).vonNeumannEntropy - s - 2 * ε
      = State.holevoChi p hp hsum (fun a => E (ρ a)) - 2 * ε := by
    rw [State.holevoChi_def, ← hs]
  rw [hgap]
  -- Fold the two `1/n` terms into `C/n`.
  have halg : 3 * ((∑ x, (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x *
          (-Real.log ((State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x)
            - Real.entropy (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist) ^ 2)
        / ((n : ℝ) * ε ^ 2))
      + 2 * ((∑ a, p a * ∑ b, (E (ρ a)).eigenvalueDist b *
          (-Real.log ((E (ρ a)).eigenvalueDist b) - s) ^ 2) / ((n : ℝ) * ε ^ 2))
      = (3 * (∑ x, (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x *
            (-Real.log ((State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist x)
              - Real.entropy (State.mix p hp hsum fun a => E (ρ a)).eigenvalueDist) ^ 2)
          + 2 * (∑ a, p a * ∑ b, (E (ρ a)).eigenvalueDist b *
              (-Real.log ((E (ρ a)).eigenvalueDist b) - s) ^ 2)) / ε ^ 2 / (n : ℝ) := by
    field_simp
  linarith [hterm1, halg]

end AxQM
