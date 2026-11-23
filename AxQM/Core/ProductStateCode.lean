/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import AxQM.Postulates.API.TensorPowState

/-!
# The product-state coding model for a noisy quantum channel (N&C §12.3.2)

This file sets up the operational model behind the **product-state capacity** `C⁽¹⁾(E)` of a
trace-preserving quantum operation `E`, the object on the right-hand side of the
Holevo–Schumacher–Westmoreland (HSW) theorem (Nielsen & Chuang, Theorem 12.8). It is the quantum
analogue of the classical noisy-channel coding setup (N&C §12.2.2): Alice encodes a message using a
**product state** of single-use channel inputs, Bob decodes the channel output with a measurement,
and the figures of merit are the resulting error probabilities.

A **product-state code** `ProductStateCode E n K` for the channel `E`, block length `n`, and message
set `{0, …, K−1}` consists of

* an **encoder** `Fin K → Fin n → State S`, associating to each message `M` the `n` single-use input
  states `ρ_{M₁}, …, ρ_{Mₙ}` whose product `ρ_M = ρ_{M₁} ⊗ ⋯ ⊗ ρ_{Mₙ}` is the codeword (Alice may
  only prepare *product* inputs — this is the defining restriction of the product-state capacity);
* a **decoder** `Measurement (Option (Fin K)) (S ^⊗ₛ n)` on the `n`-fold output system, whose
  outcome `some M` means "decoded `M`" and whose outcome `none` is the extra POVM element `E₀` that
  N&C allows for inconclusive results.

## Design: the memoryless output codeword

Because the channel is *memoryless* (applied independently to each of the `n` uses) and Alice's
inputs are *product* states, the channel output for message `M`,

`σ_M = E⊗ⁿ(ρ_M) = E(ρ_{M₁}) ⊗ ⋯ ⊗ E(ρ_{Mₙ})`,

is itself a product state — the product of the individual single-use outputs `E(ρ_{Mᵢ})`. We
therefore *define* the output codeword directly as this product (`outputCodeword`), which avoids
introducing a separate `n`-fold channel object `E⊗ⁿ` and its `IsChannel` proof: the product form is
exactly what N&C uses throughout the proof (eqs. (12.74)–(12.83)), and it is the form the converse
and achievability arguments consume.

The success probability for message `M` is the Born probability `tr(σ_M E_M)` of Bob's decoding
measurement returning `some M` on `σ_M` (`successProb`, via the Born rule
`Measurement.bornProb`); the error probability is `pᵉ_M = 1 − tr(σ_M E_M)` (`errorProb`, N&C's
`pᵉ_M`). The two operational error measures are the **average** error `p_av` over a uniform message
(N&C eq. (12.72)) and the **maximum** error over all messages; the converse bounds `p_av` from
below, while achievability produces codes with small maximum error.

The channel `E` enters only as an arbitrary state-map `State S → State S`; codes are defined for
any such `E`, and the trace-preserving/`IsChannel` hypothesis is imposed at the capacity theorems
that need it.

## Main definitions and results

* `AxQM.ProductStateCode` — a product-state code (encoder + POVM decoder).
* `AxQM.ProductStateCode.outputCodeword` — the channel output `σ_M = ⊗ᵢ E(ρ_{Mᵢ})`.
* `AxQM.ProductStateCode.successProb` / `errorProb` — `tr(σ_M E_M)` and its
  complement `pᵉ_M = 1 − tr(σ_M E_M)`.
* `AxQM.ProductStateCode.avgError` / `maxError` — average (N&C eq. (12.72)) and maximum
  error probability, with their `[0,1]` bounds and `avgError ≤ maxError`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A **product-state code** for a channel `E`, block length `n`, and message set `Fin K`
(Nielsen & Chuang §12.3.2). Alice's `encoder` sends each message to the `n` single-use input states
whose tensor product is the codeword; Bob's `decoder` is a measurement (POVM) on the `n`-fold output
system `S ^⊗ₛ n`, with outcome `some M` decoding to message `M` and `none` the inconclusive element
`E₀`. Codes are defined for an arbitrary state-map `E`; the trace-preserving hypothesis is imposed
at the capacity theorems. -/
structure ProductStateCode (E : State S → State S) (n K : ℕ) where
  /-- The encoder: message `M ↦ (ρ_{M₁}, …, ρ_{Mₙ})`, the single-use inputs whose product
  `ρ_{M₁} ⊗ ⋯ ⊗ ρ_{Mₙ}` is Alice's codeword for `M`. -/
  encoder : Fin K → Fin n → State S
  /-- Bob's decoding measurement on the `n`-fold output system: outcome `some M` = "decoded `M`",
  outcome `none` = the extra inconclusive POVM element `E₀`. -/
  decoder : Measurement (Option (Fin K)) (S.tensorPow n)

namespace ProductStateCode

variable {E : State S → State S} {n K : ℕ}

/-- The **channel output for message `M`**, `σ_M = E⊗ⁿ(ρ_M) = E(ρ_{M₁}) ⊗ ⋯ ⊗ E(ρ_{Mₙ})`. Because
the channel is memoryless and the input codeword is a product state, `σ_M` is the product of the
single-use outputs `E(ρ_{Mᵢ})`, defined here directly (no separate `E⊗ⁿ` object is needed). -/
def outputCodeword (c : ProductStateCode E n K) (m : Fin K) : State (S.tensorPow n) :=
  State.piTensor fun i => E (c.encoder m i)

/-- The **probability that Bob correctly decodes message `M`**, `tr(σ_M E_M)`: the Born probability
that the decoding measurement returns the outcome `some M` on the channel output `σ_M`. -/
def successProb (c : ProductStateCode E n K) (m : Fin K) : ℝ :=
  c.decoder.bornProb (c.outputCodeword m) (some m)

/-- The **error probability for message `M`**, `pᵉ_M = 1 − tr(σ_M E_M)` (Nielsen & Chuang, the
quantity just below eq. (12.71)): the probability Bob's decoding measurement does *not* return
`some M` on the channel output `σ_M`. -/
def errorProb (c : ProductStateCode E n K) (m : Fin K) : ℝ :=
  1 - c.successProb m

/-- The **average error probability** `p_av = (1/K) ∑_M pᵉ_M` over a uniformly random message
(Nielsen & Chuang, eq. (12.72)). -/
def avgError (c : ProductStateCode E n K) : ℝ :=
  (∑ m, c.errorProb m) / (K : ℝ)

/-- The **maximum error probability** `max_M pᵉ_M` over all messages. -/
def maxError (c : ProductStateCode E n K) : ℝ :=
  ⨆ m, c.errorProb m

/-- The success probability is nonnegative (a Born probability). -/
theorem successProb_nonneg (c : ProductStateCode E n K) (m : Fin K) : 0 ≤ c.successProb m :=
  c.decoder.bornProb_nonneg _ _

/-- The success probability is at most `1` (a Born probability). -/
theorem successProb_le_one (c : ProductStateCode E n K) (m : Fin K) : c.successProb m ≤ 1 :=
  c.decoder.bornProb_le_one _ _

/-- The error probability is nonnegative. -/
theorem errorProb_nonneg (c : ProductStateCode E n K) (m : Fin K) : 0 ≤ c.errorProb m := by
  have := c.successProb_le_one m
  simp only [errorProb]; linarith

/-- The error probability is at most `1`. -/
theorem errorProb_le_one (c : ProductStateCode E n K) (m : Fin K) : c.errorProb m ≤ 1 := by
  have := c.successProb_nonneg m
  simp only [errorProb]; linarith

/-- Each message's error probability is at most the maximum error probability. -/
theorem errorProb_le_maxError (c : ProductStateCode E n K) (m : Fin K) :
    c.errorProb m ≤ c.maxError :=
  le_ciSup (Finite.bddAbove_range _) m

/-- The maximum error probability is nonnegative. -/
theorem maxError_nonneg (c : ProductStateCode E n K) : 0 ≤ c.maxError := by
  simp only [maxError]; exact Real.iSup_nonneg c.errorProb_nonneg

/-- The maximum error probability is at most `1`. -/
theorem maxError_le_one (c : ProductStateCode E n K) : c.maxError ≤ 1 :=
  Real.iSup_le (fun m => c.errorProb_le_one m) (by norm_num)

/-- The average error probability is nonnegative. -/
theorem avgError_nonneg (c : ProductStateCode E n K) : 0 ≤ c.avgError := by
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun m _ => c.errorProb_nonneg m

/-- The **average error is at most the maximum error**: `p_av ≤ max_M pᵉ_M`. -/
theorem avgError_le_maxError (c : ProductStateCode E n K) : c.avgError ≤ c.maxError := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp [avgError, maxError]
  · rw [avgError, div_le_iff₀ (by exact_mod_cast hK)]
    calc ∑ m, c.errorProb m
        ≤ ∑ _m : Fin K, c.maxError := Finset.sum_le_sum fun m _ => c.errorProb_le_maxError m
      _ = c.maxError * (K : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_comm]

/-- The average error probability is at most `1`. -/
theorem avgError_le_one (c : ProductStateCode E n K) : c.avgError ≤ 1 :=
  c.avgError_le_maxError.trans c.maxError_le_one

end ProductStateCode

end AxQM
