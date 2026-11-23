/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ProductStateCode
import AxQM.Postulates.API.CertainMeasurement
import AxQM.Postulates.API.Distinguishability
import AxQM.Postulates.API.TensorPowDim

/-!
# The product-state capacity `C⁽¹⁾(E)` of a noisy quantum channel (N&C §12.3.2)

This file defines the **product-state capacity** `C⁽¹⁾(E)` of a trace-preserving quantum operation
`E` — the quantity on the *right-hand side* of the Holevo–Schumacher–Westmoreland (HSW) theorem
(Nielsen & Chuang, Theorem 12.8, `χ(E) = C⁽¹⁾(E)`). It is the quantum analogue of Shannon's
operational channel capacity `C(N)` (N&C p. 552): the supremum of the rates at which Alice can
reliably send classical information to Bob using **product-state** codewords through the memoryless
channel `E`.

Building on the product-state coding model of `AxQM.ProductStateCode` (encoder + POVM
decoder, with `maxError` the maximum error probability), this file supplies:

* `IsProductStateAchievableRate E R` — a rate `R` is **achievable** when there is a family of
  product-state codes `codeₙ : ProductStateCode E n ⌈exp (n · R)⌉₊`, one per block length `n`, whose
  maximum error probability tends to `0` as `n → ∞` (N&C p. 552, transcribed to the memoryless
  quantum channel);
* `productStateCapacity E` — the capacity `C⁽¹⁾(E)`, the supremum of the achievable rates.

## Design

**Units — nats, not bits.** N&C states the coding problem with `2ⁿᴿ` messages and entropy in bits.
This library measures von Neumann entropy with the *natural* logarithm (`vonNeumannEntropy` uses
`Real.log`), so the Holevo χ quantity `channelHolevoChi E` is in nats. To keep
the HSW equality `χ(E) = C⁽¹⁾(E)` a *verbatim* identity — with no stray `log 2` conversion factor —
the capacity here is defined in the same units: a code of block length `n` with `K` messages carries
`(ln K)/n` nats per channel use, so a rate-`R` family has `K = ⌈exp (n · R)⌉₊` messages (at least
`eⁿᴿ`). This mirrors the classical `Real.channelOpCapacity` (Theorem 12.7) with
`2ⁿᴿ = exp (n R log 2)` replaced by `eⁿᴿ = exp (n R)` — i.e. the classical `log 2` factor dropped,
exactly the bits→nats change. It is a faithful reformulation, not a weakening.

**Well-formedness `[Nonempty (State S)]`.** Building even the trivial one-message code needs an
input state to encode; a genuine quantum system has states (the same well-formedness hypothesis
the Chapter 9 fixed-point exercises carry). It is not a weakening: on a `0`-dimensional system no
state
exists and the whole communication setup is vacuous, so N&C's presupposition of a real channel is
recorded here as `[Nonempty (State S)]`.

**Supremum well-definedness.** `productStateCapacity` is `sSup` of the achievable-rate set. Its
`nonneg` property is proved unconditionally (rate `0` is achievable via a certain-outcome decoder;
on the pathological unbounded set `sSup` is `0` by convention, so `0 ≤ C⁽¹⁾(E)` in either case). The
set is also bounded above (`bddAbove_isProductStateAchievableRate`): every achievable rate is at
most `log d` nats, `d = dim S`, by the elementary **distinguishability bound** — a code with `K`
messages
on the `n`-fold output has `∑_M tr(σ_M E_M) ≤ dⁿ`, forcing `K(1 − max error) ≤ dⁿ`, so a rate
`R > log d` (whose `K = ⌈eⁿᴿ⌉₊` outgrows `dⁿ`) cannot keep the error small. Boundedness makes the
supremum a genuine maximum and yields the maximization property `le_productStateCapacity` (every
achievable rate `≤ C⁽¹⁾(E)`). This is the crude *dimensional* bound `C⁽¹⁾(E) ≤ log d` (the Ex. 12.3
route); the **tight** converse `C⁽¹⁾(E) ≤ χ(E)` — the Fano/Holevo/subadditivity argument, N&C eqs.
(12.96)–(12.102) — is `productStateCapacity_le_channelHolevoChi`, stated in
`AxQM/NC/Ch12/Theorem12_8.lean`.

The channel `E` enters only as an arbitrary state-map `State S → State S`. The trivial zero-error
decoder is `AxQM.certainMeasurement`; the `BddAbove` proof uses the distinguishability bound
`Measurement.sum_bornProb_self_le_finrank`, with the dimension `dⁿ` given by
`finrank (Sⁿ) = (finrank S)ⁿ`.

## Main definitions and results

* `AxQM.IsProductStateAchievableRate` — achievability of a rate `R` (N&C p. 552).
* `AxQM.productStateCapacity` — the product-state capacity `C⁽¹⁾(E)`.
* `AxQM.isProductStateAchievableRate_zero` — rate `0` is achievable.
* `AxQM.productStateCapacity_nonneg` — `0 ≤ C⁽¹⁾(E)`.
* `AxQM.bddAbove_isProductStateAchievableRate` — the achievable-rate set is bounded above
  (distinguishability bound), so `C⁽¹⁾(E)` is a genuine supremum.
* `AxQM.le_productStateCapacity` — every achievable rate is `≤ C⁽¹⁾(E)`.
-/

open ContinuousLinearMap InnerProductSpace Filter Topology
open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A rate `R` (in **nats** per channel use) is **achievable** for the memoryless channel `E` when
there is a family of product-state codes `codeₙ : ProductStateCode E n ⌈exp (n · R)⌉₊`, one for each
block length `n`, whose maximum error probability `maxError` tends to `0` as `n → ∞` (Nielsen &
Chuang, p. 552, for the quantum product-state model). The message count `⌈exp (n · R)⌉₊` is at least
`eⁿᴿ`, i.e. a rate of `R` nats per use over `n` uses — the natural-log analogue of N&C's `2ⁿᴿ` (see
the module docstring on the nats convention). -/
def IsProductStateAchievableRate (E : State S → State S) (R : ℝ) : Prop :=
  ∃ code : (n : ℕ) → ProductStateCode E n ⌈Real.exp ((n : ℝ) * R)⌉₊,
    Tendsto (fun n => (code n).maxError) atTop (𝓝 0)

/-- The **product-state capacity** `C⁽¹⁾(E)` of the channel `E` (Nielsen & Chuang §12.3.2): the
supremum of all achievable rates for communication using product-state inputs. It is the right-hand
side of the HSW theorem `χ(E) = C⁽¹⁾(E)` (Theorem 12.8), whose left-hand side is
`channelHolevoChi E`. -/
def productStateCapacity (E : State S → State S) : ℝ :=
  sSup {R | IsProductStateAchievableRate E R}

/-- **Rate `0` is achievable.** Use the one-message code (`⌈exp (n · 0)⌉₊ = 1` message) whose
decoder is the certain-outcome measurement announcing that sole message: every message is decoded
correctly, so the maximum error probability is `0` for every block length, and a fortiori tends to
`0`. Requires `[Nonempty (State S)]` only to supply the (irrelevant) input state the encoder must
name. -/
theorem isProductStateAchievableRate_zero [Nonempty (State S)] (E : State S → State S) :
    IsProductStateAchievableRate E 0 := by
  have hpos : ∀ n : ℕ, 0 < ⌈Real.exp ((n : ℝ) * 0)⌉₊ := fun n => Nat.ceil_pos.mpr (Real.exp_pos _)
  have hle : ∀ n : ℕ, ⌈Real.exp ((n : ℝ) * 0)⌉₊ ≤ 1 := by
    intro n; rw [mul_zero, Real.exp_zero, Nat.ceil_one]
  refine ⟨fun n => { encoder := fun _ _ => Classical.arbitrary (State S)
                     decoder := certainMeasurement (some ⟨0, hpos n⟩) }, ?_⟩
  refine tendsto_const_nhds.congr fun n => ?_
  have : Subsingleton (Fin ⌈Real.exp ((n : ℝ) * 0)⌉₊) :=
    Fin.subsingleton_iff_le_one.mpr (hle n)
  refine (le_antisymm (Real.iSup_le (fun m => ?_) le_rfl)
    (ProductStateCode.maxError_nonneg _)).symm
  have hm : m = ⟨0, hpos n⟩ := Subsingleton.elim _ _
  simp only [ProductStateCode.errorProb, ProductStateCode.successProb, hm,
    certainMeasurement_bornProb_self, sub_self, le_refl]

/-- **The product-state capacity is non-negative**, `0 ≤ C⁽¹⁾(E)`. When the achievable-rate set is
bounded above, rate `0` lies in it (`isProductStateAchievableRate_zero`), so the supremum is `≥ 0`;
otherwise `sSup` is `0` by convention. -/
theorem productStateCapacity_nonneg [Nonempty (State S)] (E : State S → State S) :
    0 ≤ productStateCapacity E := by
  by_cases h : BddAbove {R | IsProductStateAchievableRate E R}
  · exact le_csSup h (isProductStateAchievableRate_zero E)
  · rw [productStateCapacity, Real.sSup_of_not_bddAbove h]

/-- **The achievable-rate set is bounded above**, so `C⁽¹⁾(E)` is a genuine supremum. Every
achievable rate `R` is at most `log d` nats, `d = dim S`, by the **distinguishability bound**: for a
product-state code with `K = ⌈eⁿᴿ⌉₊` messages, the total success probability of the decoder is
`∑_M tr(σ_M E_M) ≤ dⁿ` (`Measurement.sum_bornProb_self_le_finrank` applied to the output codewords,
using `finrank (Sⁿ) = dⁿ`). Since the average error `p_av` obeys `∑_M tr(σ_M E_M) = K(1 − p_av)` and
`p_av ≤ max error`, this gives `K(1 − max error) ≤ dⁿ`, hence `eⁿᴿ(1 − max errorₙ) ≤ dⁿ` and
`1 − max errorₙ ≤ (d / eᴿ)ⁿ`. If `R > log d` then `d / eᴿ < 1`, so the right side `→ 0` while the
left `→ 1` (max errorₙ `→ 0` by achievability) — a contradiction. Thus every achievable rate is
`≤ log d`. This is the crude dimensional half of the HSW converse (N&C Exercise 12.3 route);
`[Nonempty (State S)]` supplies the input state the codes name and forces `d ≥ 1`. -/
theorem bddAbove_isProductStateAchievableRate [Nonempty (State S)] (E : State S → State S) :
    BddAbove {R | IsProductStateAchievableRate E R} := by
  have : Nontrivial S.space := (Classical.arbitrary (State S)).nontrivial_space
  set d : ℕ := Module.finrank ℂ S.space with hd_def
  have hd_pos : 0 < d := Module.finrank_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd_pos
  refine ⟨Real.log d, ?_⟩
  rintro R ⟨code, hcode⟩
  by_contra hlt
  rw [not_le] at hlt
  -- Distinguishability: the total decoder success probability is at most `dⁿ`.
  have hdist : ∀ n : ℕ, ∑ M, (code n).successProb M ≤ (d : ℝ) ^ n := by
    intro n
    have hle := (code n).decoder.sum_bornProb_self_le_finrank
      (fun o => match o with
        | none => State.tensorPow (Classical.arbitrary (State S)) n
        | some M => (code n).outputCodeword M)
    rw [Fintype.sum_option,
      show Module.finrank ℂ (S.tensorPow n).space = d ^ n from QSystem.finrank_tensorPow_space S n,
      Nat.cast_pow] at hle
    have hnn : 0 ≤ (code n).decoder.bornProb
        (State.tensorPow (Classical.arbitrary (State S)) n) none :=
      (code n).decoder.bornProb_nonneg _ _
    have hcongr : ∑ M, (code n).decoder.bornProb ((code n).outputCodeword M) (some M)
        = ∑ M, (code n).successProb M := rfl
    rw [hcongr] at hle
    linarith
  -- The geometric ratio `q = d / eᴿ` is in `[0, 1)` exactly because `log d < R`.
  set q : ℝ := (d : ℝ) / Real.exp R with hq_def
  have hq0 : 0 ≤ q := div_nonneg hdR.le (Real.exp_pos R).le
  have hdexp : (d : ℝ) < Real.exp R := by
    rw [← Real.exp_log hdR]; exact Real.exp_lt_exp.mpr hlt
  have hq1 : q < 1 := (div_lt_one (Real.exp_pos R)).mpr hdexp
  -- Per block length: `1 − max errorₙ ≤ qⁿ`.
  have hpern : ∀ n : ℕ, 1 - (code n).maxError ≤ q ^ n := by
    intro n
    set K : ℕ := ⌈Real.exp ((n : ℝ) * R)⌉₊ with hK_def
    have hKpos : 0 < K := Nat.ceil_pos.mpr (Real.exp_pos _)
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hmaxle : (code n).avgError ≤ (code n).maxError := (code n).avgError_le_maxError
    have hmax1 : (code n).maxError ≤ 1 := (code n).maxError_le_one
    have hexpK : Real.exp ((n : ℝ) * R) ≤ (K : ℝ) := Nat.le_ceil _
    have herr : (code n).avgError * (K : ℝ) = ∑ M, (code n).errorProb M := by
      rw [ProductStateCode.avgError, div_mul_cancel₀ _ (ne_of_gt hKR)]
    have hsum_succ : ∑ M, (code n).successProb M = (K : ℝ) - ∑ M, (code n).errorProb M := by
      have hse : ∀ M, (code n).successProb M = 1 - (code n).errorProb M := fun M => by
        simp [ProductStateCode.errorProb]
      simp only [hse, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, ← hK_def]
    -- `eⁿᴿ (1 − max error) ≤ K(1 − max error) ≤ K(1 − p_av) = ∑ success ≤ dⁿ`.
    have hCeq : (K : ℝ) * (1 - (code n).avgError) = ∑ M, (code n).successProb M := by
      rw [hsum_succ, ← herr]; ring
    have hchain : Real.exp ((n : ℝ) * R) * (1 - (code n).maxError) ≤ (d : ℝ) ^ n := by
      calc Real.exp ((n : ℝ) * R) * (1 - (code n).maxError)
          ≤ (K : ℝ) * (1 - (code n).maxError) :=
            mul_le_mul_of_nonneg_right hexpK (by linarith)
        _ ≤ (K : ℝ) * (1 - (code n).avgError) :=
            mul_le_mul_of_nonneg_left (by linarith) hKR.le
        _ = ∑ M, (code n).successProb M := hCeq
        _ ≤ (d : ℝ) ^ n := hdist n
    have hdivq : (d : ℝ) ^ n / Real.exp ((n : ℝ) * R) = q ^ n := by
      rw [hq_def, div_pow, Real.exp_natCast_mul]
    rw [← hdivq, le_div_iff₀ (Real.exp_pos _)]
    linarith [hchain]
  -- The two sides converge to `1` and `0`, contradiction.
  have hL : Tendsto (fun n => 1 - (code n).maxError) atTop (𝓝 1) := by
    simpa using hcode.const_sub (1 : ℝ)
  have hR0 : Tendsto (fun n => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hcontra : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto' hL hR0 hpern
  linarith

/-- **The maximization property of the product-state capacity**: every achievable rate is at most
`C⁽¹⁾(E)`. Immediate from `bddAbove_isProductStateAchievableRate`, since `C⁽¹⁾(E)` is the supremum
of the achievable rates (`le_csSup`). -/
theorem le_productStateCapacity [Nonempty (State S)] {E : State S → State S} {R : ℝ}
    (hR : IsProductStateAchievableRate E R) : R ≤ productStateCapacity E :=
  le_csSup (bddAbove_isProductStateAchievableRate E) hR

end AxQM
