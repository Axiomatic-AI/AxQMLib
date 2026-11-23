/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspace
import AxQM.Postulates.API.TensorPowMix
import AxQM.Postulates.API.TypicalSubspaceEquipartition
import AxQM.Postulates.API.Mixture

/-!
# The expected conditional typical subspace projector `𝔼(P_M)` (N&C Thm 12.8, eqs. 12.76–77)

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability) the decoding POVM is built from the **conditional typical subspace
projectors** `P_M` of the output codewords `σ_M = ⨂ᵢ E(ρ_{Mᵢ})`
(`Postulates/API/CondTypicalSubspace`).  The error estimate of Box 12.5 averages over the random
choice of codewords, and the **false-decoding** (confusion) term (N&C eqs. (12.80)–(12.82)) is
controlled through the *expected* conditional typical projector of a single random codeword,

`Q := 𝔼(P_{M'}) = ∑_{t : Fin n → ι} (∏ᵢ p_{tᵢ}) • P_t`,

where the codeword's `n` letters `t : Fin n → ι` are drawn i.i.d. from the a-priori distribution
`pⱼ` (weight `∏ᵢ p_{tᵢ}`, `Postulates/API/TensorPowMix`) and `P_t = P(σ_t)` is the conditional
typical projector of the resulting output `σ_t = ⨂ᵢ E(ρ_{tᵢ})`.

Two facts about `Q` are exactly the random-coding inputs N&C uses:

* `0 ≤ Q` (each `P_t` is an orthogonal projector, hence positive; a nonnegative combination stays
  positive) — the positivity the false-decoding decay
  `State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le` requires of its positive weight; and
* `re tr(Q) ≤ exp(n(s + ε))` (N&C eq. (12.77) in expectation, `s = S̄ = ∑ⱼ pⱼ S(E(ρⱼ))`) — the
  expectation of the deterministic per-codeword dimension bound `tr(P_M) ≤ exp(n(S̄+ε))`
  (`State.condTypicalSubspaceDim_le`, N&C eq. (12.77)), averaged against the probability weights.

This file defines `Q`, proves these two facts, and proves their product with the equipartition
false-decoding decay `re tr(P σ̄^⊗n P · Q) ≤ exp(-n(S(σ̄)-ε)) · re tr Q`
(`State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le_of_trace_le`,
`Postulates/API/TypicalSubspaceEquipartition`): the two factors combine into the exponent
`exp(-n(S(σ̄) - S̄ - 2ε))` of the HSW confusion bound (eq. (12.82)).  Weaving in the random-coding
average `𝔼(σ_M) = σ̄^⊗n` through the middle factor, scaling by the `2^{nR} - 1` confusing messages,
and assembling the other two terms of eq. (12.79) are not carried out in this file.

## Main results

* `AxQM.re_trace_finsetSum_real_smul` — a general linearity helper: the real part of the
  trace of a **real-weighted operator sum** splits as `re tr(∑ₖ cₖ • Mₖ) = ∑ₖ cₖ · re tr(Mₖ)`.  The
  vehicle for pushing the codeword average through `re ∘ tr`.

* `AxQM.State.expectedCondTypicalSubspaceProj` — the expected conditional typical subspace
  projector `Q = ∑_t (∏ᵢ p_{tᵢ}) • P_t`.

* `AxQM.State.expectedCondTypicalSubspaceProj_nonneg` — `0 ≤ Q`.

* `AxQM.State.re_trace_expectedCondTypicalSubspaceProj_le` — `re tr(Q) ≤ exp(n(s+ε))`
  (N&C eq. (12.77) in expectation).

* `State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_expectedCondTypicalSubspaceProj_le` — the
  **HSW confusion (false-decoding) term decay** `re tr(P σ̄^⊗n P · Q) ≤ exp(-n(S(σ̄) - s - 2ε))`
  (N&C eq. (12.82) exponent), the product of the equipartition decay with the two facts above.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, eqs. (12.76), (12.77), Box 12.5.
-/

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The real part of the trace of a real-weighted operator sum splits over the sum.**  For a
finite family of operators `Mₖ` on a complex normed space `E` and real weights `cₖ`,

`re tr(∑ₖ cₖ • Mₖ)  =  ∑ₖ cₖ · re tr(Mₖ)`

(the scalars being the complex coercions `(cₖ : ℂ)`).  Pure linearity — `LinearMap.trace` is
`ℂ`-linear and `RCLike.re` is `ℝ`-additive with `re(↑c · z) = c · re z` — with no use of any
`QSystem` structure, so it is stated over an abstract `E` (matching the sibling trace helpers
`AxQM.trace_smul_left`/`trace_smul_right`).  It is the vehicle for pushing the
random-coding average of the HSW error estimate through `re ∘ tr` (its consumers here instantiate
at `E := (⨂ₛ _ : Fin n, S).space`). -/
theorem re_trace_finsetSum_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ : Type*} (fs : Finset κ) (c : κ → ℝ) (M : κ → E →L[ℂ] E) :
    RCLike.re (LinearMap.trace ℂ E
        ((∑ k ∈ fs, (c k : ℂ) • M k : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = ∑ k ∈ fs, c k * RCLike.re (LinearMap.trace ℂ E ((M k : E →ₗ[ℂ] E))) := by
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum, RCLike.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
  exact RCLike.re_ofReal_mul _ _

variable {ι : Type*} [Fintype ι]

/-- **The expected conditional typical subspace projector** `𝔼(P_M)` (Nielsen & Chuang,
Theorem 12.8, the random-coding average of eqs. (12.76)–(12.77)).  For an a-priori distribution
`{pⱼ, ρⱼ}` of channel inputs, the quantum operation `E`, block length `n`, and thresholds `s`, `ε`,
it is the average — over the i.i.d. random choice of the codeword's `n` letters `t : Fin n → ι`
(weight `∏ᵢ p_{tᵢ}`) — of the conditional typical subspace projector `P_t` of the output codeword
`σ_t = ⨂ᵢ E(ρ_{tᵢ})`:

`𝔼(P_M) = ∑_{t : Fin n → ι} (∏ᵢ p_{tᵢ}) • P_t`.

It is the positive weight through which the false-decoding term of the HSW random-coding error
estimate is controlled (N&C eqs. (12.80)–(12.82)). -/
def State.expectedCondTypicalSubspaceProj (p : ι → ℝ) (E : State S → State S) (ρ : ι → State S)
    (n : ℕ) (s ε : ℝ) : (⨂ₛ _ : Fin n, S).space →L[ℂ] (⨂ₛ _ : Fin n, S).space :=
  ∑ t : Fin n → ι, ((∏ i, p (t i) : ℝ) : ℂ) •
    State.condTypicalSubspaceProj (fun i => E (ρ (t i))) s ε

/-- **The expected conditional typical projector is positive**, `0 ≤ 𝔼(P_M)` (Nielsen & Chuang,
Theorem 12.8).  Each conditional typical projector `P_t` is an orthonormal (self-adjoint idempotent)
projector, hence positive (`IsStarProjection.nonneg`); the average with the nonnegative i.i.d.
weights `∏ᵢ p_{tᵢ}` is therefore a nonnegative combination of positive operators.  This is the
positivity the false-decoding decay `State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le`
demands of its positive weight in the HSW random-coding estimate. -/
theorem State.expectedCondTypicalSubspaceProj_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (E : State S → State S) (ρ : ι → State S) (n : ℕ) (s ε : ℝ) :
    0 ≤ State.expectedCondTypicalSubspaceProj p E ρ n s ε := by
  unfold State.expectedCondTypicalSubspaceProj
  refine Finset.sum_nonneg fun t _ => ?_
  rw [Complex.coe_smul]
  refine smul_nonneg (Finset.prod_nonneg fun i _ => hp (t i)) ?_
  exact (isStarProjection_orthonormalProjector
    (State.piTensorEigenbasis (fun i => E (ρ (t i)))).orthonormal _).nonneg

/-- **The expected conditional typical subspace dimension bound**, `re tr(𝔼(P_M)) ≤ exp(n(s+ε))`
(Nielsen & Chuang, Theorem 12.8, eq. (12.77) in expectation).  The trace of the expected projector
is the expected rank `∑_t (∏ᵢ p_{tᵢ}) · dim(P_t)`; each `dim(P_t) ≤ exp(n(s+ε))` by the
deterministic per-codeword dimension bound `State.condTypicalSubspaceDim_le` (N&C eq. (12.77)), and
the weights sum to one (`sum_iidProdWeight`), so the expectation obeys the same bound.  With
`s = S̄ = ∑ⱼ pⱼ S(E(ρⱼ))` this is N&C's `𝔼(tr(P_M)) ≤ 2^{n(S̄+ε)}` (natural-log/nats convention),
the term feeding the `exp(n(S̄+ε))` factor of the confusion bound (eq. (12.82)).

The proof pushes the trace through the average (`re_trace_finsetSum_real_smul`), rewrites each
`re tr(P_t)` to `dim(P_t)` (`State.trace_condTypicalSubspaceProj_eq_condTypicalSubspaceDim`), bounds
each summand, and collapses `∑_t (∏ᵢ p_{tᵢ}) · exp(n(s+ε)) = exp(n(s+ε))`. -/
theorem State.re_trace_expectedCondTypicalSubspaceProj_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (E : State S → State S) (ρ : ι → State S) (n : ℕ) (s ε : ℝ) :
    RCLike.re (LinearMap.trace ℂ (⨂ₛ _ : Fin n, S).space
        ((State.expectedCondTypicalSubspaceProj p E ρ n s ε :
          (⨂ₛ _ : Fin n, S).space →ₗ[ℂ] (⨂ₛ _ : Fin n, S).space)))
      ≤ Real.exp ((n : ℝ) * (s + ε)) := by
  unfold State.expectedCondTypicalSubspaceProj
  rw [re_trace_finsetSum_real_smul]
  have hdim : ∀ t : Fin n → ι, RCLike.re (LinearMap.trace ℂ (⨂ₛ _ : Fin n, S).space
      ((State.condTypicalSubspaceProj (fun i => E (ρ (t i))) s ε :
        (⨂ₛ _ : Fin n, S).space →ₗ[ℂ] (⨂ₛ _ : Fin n, S).space)))
        = (State.condTypicalSubspaceDim (fun i => E (ρ (t i))) s ε : ℝ) := fun t => by
    rw [State.trace_condTypicalSubspaceProj_eq_condTypicalSubspaceDim]
    simp
  calc ∑ t : Fin n → ι, (∏ i, p (t i)) * RCLike.re (LinearMap.trace ℂ (⨂ₛ _ : Fin n, S).space
          ((State.condTypicalSubspaceProj (fun i => E (ρ (t i))) s ε :
            (⨂ₛ _ : Fin n, S).space →ₗ[ℂ] (⨂ₛ _ : Fin n, S).space)))
        ≤ ∑ t : Fin n → ι, (∏ i, p (t i)) * Real.exp ((n : ℝ) * (s + ε)) := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [hdim t]
          refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => hp (t i))
          have hle := State.condTypicalSubspaceDim_le (fun i => E (ρ (t i))) s ε
          rwa [Fintype.card_fin] at hle
    _ = (∑ t : Fin n → ι, ∏ i, p (t i)) * Real.exp ((n : ℝ) * (s + ε)) := by rw [Finset.sum_mul]
    _ = Real.exp ((n : ℝ) * (s + ε)) := by rw [sum_iidProdWeight p hsum n, one_mul]

/-- **The HSW confusion (false-decoding) term decay** (Nielsen & Chuang, Theorem 12.8, the confusion
exponent of eq. (12.82)).  For the average channel output `σ̄ = ∑ⱼ pⱼ E(ρⱼ)` (`State.mix`), the
projector `P = σ̄.typicalSubspaceProj n ε` onto its `ε`-typical subspace, and the expected
conditional typical projector `Q = 𝔼(P_M)` of a single random codeword,

`re tr(P σ̄^⊗n P · Q)  ≤  exp(-n (S(σ̄) - s - 2ε))`

(in nats; N&C's base-`2` `tr(P σ̄^⊗n P E(P₁)) ≤ 2^{-n(S(σ̄) - S̄ - 2ε)}`, with the threshold
`s = S̄ = ∑ⱼ pⱼ S(σⱼ)` defining `Q`).  This is the middle, false-decoding contribution to the
random-coding
average error: in N&C's estimate the confusion of message `M` with a *different* random codeword
`M'` is governed by `tr(P 𝔼(σ_M) P 𝔼(P_{M'}))`, whose middle factor `𝔼(σ_M) = σ̄^⊗n` is the
random-coding average and whose weight `𝔼(P_{M'}) = Q` is the expected conditional typical
projector.

It is the exact product of the two ingredients recorded above with the equipartition decay in
`Postulates/API/TypicalSubspaceEquipartition`:

* the **equipartition false-decoding decay**
  `State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le_of_trace_le`,
  `re tr(P σ̄^⊗n P · Q) ≤ exp(-n(S(σ̄) - ε)) · D` for any `0 ≤ Q` with `re tr Q ≤ D`;
  instantiated at
* `Q = 𝔼(P_M)` (`State.expectedCondTypicalSubspaceProj`), positive
  (`State.expectedCondTypicalSubspaceProj_nonneg`) with `re tr Q ≤ D = exp(n(s + ε))`
  (`State.re_trace_expectedCondTypicalSubspaceProj_le`, N&C eq. (12.77) in expectation).

The two exponential factors multiply into a single exponent,
`exp(-n(S(σ̄) - ε)) · exp(n(s + ε)) = exp(-n(S(σ̄) - s - 2ε))`.  Provided `s = S̄` and
`R < S(σ̄) - S̄`, this exponent (scaled by the `2^{nR} - 1` confusing messages) decays to `0`, the
heart of the HSW achievability estimate (N&C eqs. (12.82)–(12.83)); that union-bound scaling and
the assembly of the other two terms of eq. (12.79) are not carried out in this file.

`Q` lives on the constant-family system `⨂ₛ _ : Fin n, S` (its native form) while the equipartition
factor lives on `S ^⊗ₛ n`; the two systems are definitionally equal (`QSystem.tensorPow` *is*
`piTensor` of the constant family), so `Q` is transported along `QSystem.tensorPow_eq` (a `rfl`
identity) to sit on `S ^⊗ₛ n` for the product. -/
theorem State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_expectedCondTypicalSubspaceProj_le
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (E : State S → State S)
    (ρ : ι → State S) (n : ℕ) (s ε : ℝ) :
    RCLike.re (LinearMap.trace ℂ (S ^⊗ₛ n).space
        ((((State.mix p hp hsum fun i => E (ρ i)).typicalSubspaceProj n ε).comp
              (((State.mix p hp hsum fun i => E (ρ i)).tensorPow n).op.comp
                ((State.mix p hp hsum fun i => E (ρ i)).typicalSubspaceProj n ε)) *
            ((QSystem.tensorPow_eq S n).symm ▸
              State.expectedCondTypicalSubspaceProj p E ρ n s ε) : _ →L[ℂ] _) : _ →ₗ[ℂ] _))
      ≤ Real.exp (-(n : ℝ) *
          ((State.mix p hp hsum fun i => E (ρ i)).vonNeumannEntropy - s - 2 * ε)) := by
  have hkey := State.re_trace_typicalSubspaceProj_tensorPow_comp_mul_le_of_trace_le
    (State.mix p hp hsum fun i => E (ρ i)) n ε
    (State.expectedCondTypicalSubspaceProj_nonneg p hp E ρ n s ε)
    (State.re_trace_expectedCondTypicalSubspaceProj_le p hp hsum E ρ n s ε)
  refine hkey.trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  ring

end AxQM
