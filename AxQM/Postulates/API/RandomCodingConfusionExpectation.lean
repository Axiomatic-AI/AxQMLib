/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RandomCodingConfusion
import ToMathlib.InformationTheory.RandomCodingExpectation

/-!
# The random-coding expectation of the HSW confusion term (N&C Thm 12.8, eqs. 12.80–12.82)

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability), the per-code average error is bounded by three physical traces
(N&C eq. (12.79), `State.avgError_prettyGood_le_re_trace_percode`).  The **confusion**
(false-decoding) contribution — the probability of decoding a random codeword `M` as a *different*
message `M'` — is `∑_{M'≠M} tr(P σ_M P P_{M'})`, where `P = σ̄.typicalSubspaceProj n ε` is the
typical projector of the average output `σ̄ = ∑ⱼ pⱼ E(ρⱼ)`, `σ_M = ⨂ᵢ E(ρ_{Mᵢ})` the output
codeword, and
`P_{M'} = State.condTypicalSubspaceProj (σ_{M'}) s ε` its conditional typical projector.

This file takes the **random-coding expectation** of one such confusion trace.  For two *distinct*
messages `M ≠ M'` the codewords are drawn independently, so — averaging the codebook against the
i.i.d. product weight `∏_M ∏ᵢ p((w M) i)` — the two-codeword marginal
(`Real.sum_pi_weight_mul_apply₂`) factors the expectation into a product of single-codeword
expectations, `𝔼[σ_M] = σ̄^⊗n` (`State.tensorPow_mix`) and `𝔼[P_{M'}] = 𝔼(P_M)`
(`State.expectedCondTypicalSubspaceProj`).  The resulting middle-factor trace
`re tr(P σ̄^⊗n P 𝔼(P_M))` is then exactly the confusion-decay bound of
`Postulates/API/RandomCodingConfusion` (N&C eq. (12.82) exponent).

## Main results

* `AxQM.re_trace_comp_finsetSum_comp_comp_finsetSum` — a general ℝ-bilinearity helper: the
  sandwiched trace `re tr(P (∑ᵢ cᵢ Aᵢ) P (∑ⱼ dⱼ Bⱼ))` splits as
  `∑ᵢ ∑ⱼ cᵢ dⱼ · re tr(P Aᵢ P Bⱼ)`.

* `AxQM.State.expectation_re_trace_confusion_prettyGood_le` — the **expected confusion
  trace** for a message pair `M ≠ M'`: averaged over the random codebook, the confusion trace of the
  per-code bound is at most `exp(-n (S(σ̄) - s - 2ε))` (N&C eq. (12.82), one summand of the
  `2^{nR} - 1` in the confusion sum).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eqs. (12.79)–(12.82).
-/

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **Bilinear ℝ-linearity of the sandwiched trace over two real-weighted operator sums.**  For
operators on a complex normed space `E`, a projector-like `P`, and finite real-weighted sums
`∑ᵢ cᵢ Aᵢ`, `∑ⱼ dⱼ Bⱼ`,

`re tr(P (∑ᵢ cᵢ Aᵢ) P (∑ⱼ dⱼ Bⱼ))  =  ∑ᵢ ∑ⱼ cᵢ dⱼ · re tr(P Aᵢ P Bⱼ)`.

Pure ℝ-bilinearity: composition distributes over the finite sums and the scalars, and `re ∘ trace`
is ℝ-linear (`re_trace_finsetSum_real_smul`).  Stated over an abstract `E` so that, applied to the
HSW confusion trace, the unifier bridges the definitionally-equal `S ^⊗ₛ n` / `piTensor` framings of
its operands. -/
theorem re_trace_comp_finsetSum_comp_comp_finsetSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} [Fintype ι] [Fintype κ] (P : E →L[ℂ] E)
    (c : ι → ℝ) (d : κ → ℝ) (A : ι → E →L[ℂ] E) (B : κ → E →L[ℂ] E) :
    RCLike.re ((LinearMap.trace ℂ E)
        ((P.comp ((∑ i, (c i : ℂ) • A i).comp P)).comp (∑ j, (d j : ℂ) • B j) : E →ₗ[ℂ] E))
      = ∑ i, ∑ j, c i * d j *
          RCLike.re ((LinearMap.trace ℂ E)
            (P.comp ((A i).comp (P.comp (B j))) : E →ₗ[ℂ] E)) := by
  simp only [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_smul,
    re_trace_finsetSum_real_smul, Finset.mul_sum, ContinuousLinearMap.comp_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {S : QSystem} {α : Type*} [Fintype α]

/-- **The random-coding expectation of the HSW confusion trace** (Nielsen & Chuang, Theorem 12.8,
Box 12.5, eqs. (12.80)–(12.82)).  Fix the input ensemble `{pₐ, ρₐ}`, the channel `E`, the block
length `n`, thresholds `s`, `ε`, and let `P = σ̄.typicalSubspaceProj n ε` be the typical projector
of the average output `σ̄ = ∑ₐ pₐ E(ρₐ)` (transported to `P`'s `piTensor` framing via the
`rfl`-identity `QSystem.tensorPow_eq`).  For two *distinct* messages `M ≠ M'` of a `K`-message code,
the confusion
trace `tr(P σ_M P P_{M'})` — averaged over the random codebook `w : Fin K → Fin n → α` with the
i.i.d. product weight `∏_{M''} ∏ᵢ p((w M'') i)` — is at most the confusion exponent:

`𝔼[ tr(P σ_M P P_{M'}) ]  ≤  exp(-n (S(σ̄) - s - 2ε))`.

Because `M ≠ M'`, the two codewords are independent, so the two-codeword marginal
`Real.sum_pi_weight_mul_apply₂` factors the expectation into `re tr(P σ̄^⊗n P 𝔼(P_M))` — the average
output `𝔼[σ_M] = σ̄^⊗n` (`State.tensorPow_mix`) sandwiched between `P`, weighted by the expected
conditional typical projector `𝔼[P_{M'}] = 𝔼(P_M)` (`State.expectedCondTypicalSubspaceProj`).  The
recombination of the resulting double sum into that single sandwiched trace is the ℝ-bilinearity
`re_trace_comp_finsetSum_comp_comp_finsetSum`, and the final bound is the confusion decay
`State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_expectedCondTypicalSubspaceProj_le`
(eq. (12.82)).  Summed over the `K - 1` confusing messages `M' ≠ M` this yields the
`(2^{nR} - 1)·exp(...)` confusion contribution of N&C's eq. (12.82). -/
theorem State.expectation_re_trace_confusion_prettyGood_le
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (n : ℕ) (s ε : ℝ)
    (P : (QSystem.piTensor fun _ : Fin n => S).space →L[ℂ]
        (QSystem.piTensor fun _ : Fin n => S).space)
    (hP : P = QSystem.tensorPow_eq S n ▸
      (State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceProj n ε)
    {K : ℕ} {M M' : Fin K} (hMM' : M ≠ M') :
    ∑ w : Fin K → Fin n → α, (∏ M'' : Fin K, ∏ i, p (w M'' i)) *
        RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
          (↑(P.comp ((State.piTensor fun i => E (ρ (w M i))).op.comp
                (P.comp (State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε))))))
      ≤ Real.exp (-(n : ℝ) *
          ((State.mix p hp hsum fun a => E (ρ a)).vonNeumannEntropy - s - 2 * ε)) := by
  classical
  -- Two-codeword independence marginal: collapse the codebook sum to a double sum over the two
  -- independent codewords `v = w M`, `v' = w M'`.
  rw [Real.sum_pi_weight_mul_apply₂ (fun c : Fin n → α => ∏ i, p (c i))
      (sum_iidProdWeight p hsum n)
      (fun v v' => RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
        (↑(P.comp ((State.piTensor fun i => E (ρ (v i))).op.comp
              (P.comp (State.condTypicalSubspaceProj (fun i => E (ρ (v' i))) s ε)))))))
      hMM']
  -- `σ̄^⊗n.op = E(σ_M)` as an i.i.d. mixture of product ops (`tensorPow_mix`, `mix_op`).
  have hop : ((State.mix p hp hsum fun a => E (ρ a)).tensorPow n).op
      = ∑ v : Fin n → α, (↑(∏ i, p (v i)) : ℂ) • (State.piTensor fun i => E (ρ (v i))).op := by
    rw [State.tensorPow_mix p hp hsum (fun a => E (ρ a)) n, State.mix_op]
  -- Recombine the double sum into the single sandwiched trace (bilinear ℝ-linearity), fold the two
  -- codeword sums back into `σ̄^⊗n.op` (`hop`) and `𝔼(P_M)`, and rewrite `P` to the typical
  -- projector (`hP`) — exactly the confusion-decay trace.
  rw [← re_trace_comp_finsetSum_comp_comp_finsetSum P (fun v : Fin n → α => ∏ i, p (v i))
      (fun t : Fin n → α => ∏ i, p (t i)) (fun v => (State.piTensor fun i => E (ρ (v i))).op)
      (fun t => State.condTypicalSubspaceProj (fun i => E (ρ (t i))) s ε),
    ← hop, ← State.expectedCondTypicalSubspaceProj, hP]
  exact State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_expectedCondTypicalSubspaceProj_le
    p hp hsum E ρ n s ε

end AxQM
