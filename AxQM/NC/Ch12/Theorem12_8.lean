/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChi
import AxQM.Core.PiTensorSuccHead
import AxQM.Core.ProductStateCode
import AxQM.Core.ProductStateCapacity
import AxQM.Core.ProductStateAvgAchievable
import AxQM.Postulates.API.TensorPowDim
import AxQM.Postulates.API.MeasurementReindex
import AxQM.NC.Ch12.Problem12_1
import AxQM.NC.Ch11.Subadditivity
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.API.ArakiLiebEqualityConditions
import AxQM.Postulates.PartialTraceTensor
import ToMathlib.InformationTheory.Fano

/-!
# The HSW theorem `χ(E) = C⁽¹⁾(E)` (N&C Theorem 12.8): converse steps + achievability assembly

Nielsen & Chuang's **Holevo–Schumacher–Westmoreland (HSW) theorem** (Theorem 12.8) states that the
Holevo χ quantity `χ(E)` of a trace-preserving quantum operation `E` equals its product-state
capacity `C⁽¹⁾(E)`:  `χ(E) = C⁽¹⁾(E)`.  Both objects are already in the library —
`channelHolevoChi E` (the left-hand side, N&C eq. (12.71), `AxQM/Core/ChannelHolevoChi.lean`) and
`productStateCapacity E` (the right-hand side, N&C §12.3.2, `AxQM/Core/ProductStateCapacity.lean`).

This file assembles the **complete theorem**: the equality
`channelHolevoChi_eq_productStateCapacity` is `le_antisymm` of its two directions.  It first
collects the **steps of the converse** `C⁽¹⁾(E) ≤ χ(E)` (below), then assembles the
random-coding **achievability** `χ(E) ≤ C⁽¹⁾(E)` from the development in `AxQM/Core/`
(`isProductStateAvgAchievableRate_of_lt_channelHolevoChi`) and the equality.
In N&C's converse
(eqs. (12.96)–(12.102)) the accessible information `H(M:Y)` that Bob's decoding measurement extracts
about Alice's message is controlled via the Holevo bound, the **subadditivity of the von Neumann
entropy**, and the maximisation property of `χ(E)`:

`H(M:Y)  ≤  χ({p_M, σ_M})  ≤  ∑ⱼ χ({p_M, σ_Mⱼ})  ≤  n·χ(E)`   (N&C eqs. (12.99)–(12.101)),

where `σ_M = σ_{M₁} ⊗ ⋯ ⊗ σ_{Mₙ}` is the memoryless product output of a length-`n` codeword.

## What this file provides

* `AxQM.mutualInfo_channelOutput_le_channelHolevoChi` — the **single channel use** core
  (eq. (12.99), first inequality composed with (12.71)): for any input ensemble `{pₓ, ρₓ}` and any
  decoding measurement `m`, the classical mutual information between the input label `X` and Bob's
  outcome `Y` is at most `χ(E)`.  Chains the **Holevo bound** (`holevoBound_of_chi_monotone`, N&C
  Theorem 12.1) with the **maximisation property** `le_channelHolevoChi`.

* `AxQM.State.holevoChi_tmul_le` — the **subadditivity of the Holevo χ quantity over
  product ensembles** (the reusable content of eq. (12.99)→(12.100)): for an ensemble `{pₓ, ρₓ⊗σₓ}`
  of *product* states on `S ⊗ T`,

  `χ({pₓ, ρₓ⊗σₓ})  ≤  χ({pₓ, ρₓ})  +  χ({pₓ, σₓ})`.

  This is the bipartite (`n = 2`) case of the single-letterisation collapse, and the inductive
  ingredient for its `n`-fold generalisation.  It rests on the subadditivity of the von
  Neumann entropy (`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`, N&C §11.3.4) together
  with the additivity of entropy over products (`State.vonNeumannEntropy_tmul`).

* `AxQM.mutualInfo_channelOutput_tmul_le_two_mul_channelHolevoChi` — the **two-use channel
  single-letterisation** (the `n = 2` instance of eq. (12.101)): for a two-letter product-state code
  with inputs `ρₓ`, `σₓ` and any joint decoding measurement `m` on the two-use output `S ⊗ S`,

  `H(X:Y)  ≤  2·χ(E)`.

  Composes the single-use ingredients — the Holevo bound `holevoBound_of_chi_monotone`, the
  χ-subadditivity `State.holevoChi_tmul_le`, and `le_channelHolevoChi` applied to each of the two
  output marginal ensembles — exactly as N&C's eqs. (12.99)–(12.101) do at `n = 2`.

* `AxQM.State.holevoChi_piTensor_le` — the **`n`-fold subadditivity of the Holevo χ over
  product ensembles** (eq. (12.100), general `n`): `χ({pₓ, ⨂ⱼ ρₓⱼ}) ≤ ∑ⱼ χ({pₓ, ρₓⱼ})`.  The
  `n`-factor generalisation of `State.holevoChi_tmul_le`, proved by induction on the number of
  tensor factors via the `State.piTensor` head-peel recursion
  (`State.tmul_piTensor_congr_tensorPowSuccHead_symm`, `AxQM/Core/PiTensorSuccHead.lean`).

* `AxQM.mutualInfo_channelOutput_piTensor_le_nsmul_channelHolevoChi` — the **full `n`-use
  channel single-letterisation** (eqs. (12.99)–(12.101), general `n`): for a length-`n`
  product-state code with memoryless output `⨂ⱼ E(ρ_{X,j})` and *any* joint decoding measurement `m`
  on `S ^⊗ₛ n`,

  `H(X:Y)  ≤  n·χ(E)`.

  Of this, `mutualInfo_channelOutput_tmul_le_two_mul_channelHolevoChi` is the `n = 2` instance.  It
  is the accessible-information ceiling underlying the operational converse `C⁽¹⁾(E) ≤ χ(E)`.

* `AxQM.one_sub_maxError_mul_log_card_le_log_two_add_nsmul_channelHolevoChi` — the
  **per-block converse inequality** (eqs. (12.97)–(12.101)): for a length-`n` product-state code `c`
  with `K ≥ 1` messages,

  `(1 − p̄)·log K  ≤  log 2  +  n·χ(E)`,

  where `p̄ = c.maxError`.  This is the accessible-information ceiling of the previous bullet, now
  closed against the code's operational error via **classical Fano** — it forms the joint law of a
  uniform message and Bob's decoding outcome (whose `Option (Fin K)` outcomes are relabelled to
  `Fin (K + 1)` by `Measurement.reindexOutcome`), applies the single-letterisation and Fano's
  uniform-input converse `Real.one_sub_fanoErrorProb_mul_log_card_le`, then bounds the Fano error
  by `p̄`.

* `AxQM.IsProductStateAchievableRate.le_channelHolevoChi` — **every achievable rate is at
  most `χ(E)`**: if a rate `R` (nats/use) is achievable, then `R ≤ χ(E)`.  The short limiting
  argument on the per-block bound: for `n ≥ 1`, `log Kₙ ≥ nR` and `1 − maxErrorₙ ≥ 0` turn the
  per-block inequality into `(1 − maxErrorₙ)·R ≤ (log 2)/n + χ(E)`, whose two sides tend to `R` and
  `χ(E)` as `n → ∞`.

* `AxQM.productStateCapacity_le_channelHolevoChi` — the **operational converse of the HSW
  theorem** (eqs. (12.96)–(12.102)): `C⁽¹⁾(E) ≤ χ(E)`.  The supremum of the achievable rates is
  `≤ χ(E)` because each achievable rate is (previous bullet) and `χ(E) ≥ 0` (`Real.sSup_le`); no
  `[Nonempty (State S)]` is needed (the empty case is `sSup ∅ = 0 ≤ χ(E)`).  This closes the whole
  converse direction of Theorem 12.8.

* `AxQM.channelHolevoChi_le_productStateCapacity` — the **achievability direction**
  `χ(E) ≤ C⁽¹⁾(E)` (N&C Box 12.5): the operational payoff of the random-coding development in
  `AxQM/Core/`.
  For any `R < χ(E)`, `isProductStateAvgAchievableRate_of_lt_channelHolevoChi` makes `R`
  average-achievable, the expurgation bridge
  `IsProductStateAvgAchievableRate.isProductStateAchievableRate_of_lt` makes every `R' < R`
  achievable, and `le_productStateCapacity` gives `R' ≤ C⁽¹⁾(E)`; two nested
  `le_of_forall_lt_imp_le_of_dense` (over `R'` then `R`) bridge the two strict inequalities and pass
  to the supremum.

* `AxQM.channelHolevoChi_eq_productStateCapacity` — the **HSW theorem** itself,
  `χ(E) = C⁽¹⁾(E)` (the headline top-level claim of §12.3): `le_antisymm` of the converse
  `productStateCapacity_le_channelHolevoChi` with the achievability
  `channelHolevoChi_le_productStateCapacity`.

The channel `E` enters only as an arbitrary state-map `State S → State S`.  The proofs use the
Holevo bound `holevoBound_of_chi_monotone` (`AxQM/NC/Ch12/Problem12_1.lean`) and the entropy
subadditivity `State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`
(`AxQM/NC/Ch11/Subadditivity.lean`).
-/

open scoped BigOperators Topology

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The Holevo-bound step of the HSW converse** (Nielsen & Chuang, Theorem 12.8, eq. (12.99),
single channel use).  For a trace-preserving quantum operation `E`, an input ensemble `{pₓ, ρₓ}`
(indexed by `Fin n`), and any decoding measurement `m` on the channel output, the classical mutual
information `H(X:Y)` between Alice's input label `X` (distribution `p`) and Bob's measurement
outcome `Y` is at most the channel Holevo χ quantity:

`H(X:Y)  ≤  χ(E)`.

Chaining Nielsen & Chuang's two inequalities:

* the **Holevo bound** `holevoBound_of_chi_monotone` (Theorem 12.1) bounds `H(X:Y)` by the Holevo χ
  of the *output* ensemble `{pₓ, E(ρₓ)}`, `H(X:Y) ≤ χ({pₓ, E(ρₓ)})`; and
* `le_channelHolevoChi` (the maximisation property of `χ(E)`, eq. (12.71)) bounds that
  output-ensemble χ by `χ(E)`.

No decoding measurement of a single channel use can extract more than `χ(E)` bits of classical
information about a product-state input — the per-use ceiling underlying the operational converse
`C⁽¹⁾(E) ≤ χ(E)`. -/
theorem mutualInfo_channelOutput_le_channelHolevoChi (E : State S → State S) {n r : ℕ} [NeZero r]
    (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (ρ : Fin n → State S)
    (m : Measurement (Fin r) S) :
    (Real.mutualInfo fun xy => p xy.1 * m.bornProb (E (ρ xy.1)) xy.2) ≤ channelHolevoChi E :=
  le_trans (holevoBound_of_chi_monotone p hp hsum (fun i => E (ρ i)) m)
    (le_channelHolevoChi E p hp hsum ρ)

/-- **Subadditivity of the Holevo χ quantity over product ensembles** (Nielsen & Chuang,
Theorem 12.8, the content of eqs. (12.99)→(12.100)).  For an ensemble `{pₓ, ρₓ ⊗ σₓ}` whose states
are *products* on a bipartite system `S ⊗ T`, the Holevo χ is subadditive over the two factors:

`χ({pₓ, ρₓ ⊗ σₓ})  ≤  χ({pₓ, ρₓ})  +  χ({pₓ, σₓ})`.

This is the bipartite (`n = 2`) case of the single-letterisation collapse that turns the χ of a
memoryless product-output ensemble into a per-use sum, and the inductive step for its `n`-fold
generalisation.

The proof is the ensemble form of the entropy-subadditivity argument.  Write
`ω = ∑ₓ pₓ (ρₓ ⊗ σₓ)` for the ensemble mixture.  Its marginals are the factor-wise mixtures,
`ω_S = ∑ₓ pₓ ρₓ` and `ω_T = ∑ₓ pₓ σₓ` (partial trace commutes with mixing,
`State.reducedLeft_mix`/`State.reducedRight_mix`, and kills the opposite factor of a product,
`State.reducedLeft_tmul`/`State.reducedRight_tmul`).  Subadditivity of the von Neumann entropy
(`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`, N&C §11.3.4) gives
`S(ω) ≤ S(ω_S) + S(ω_T)`; additivity of entropy over each product component
(`State.vonNeumannEntropy_tmul`) gives `S(ρₓ ⊗ σₓ) = S(ρₓ) + S(σₓ)`, so the average-component term
splits.  Subtracting, the two χ's separate. -/
theorem State.holevoChi_tmul_le {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) (σ : ι → State T) :
    State.holevoChi p hp hsum (fun i => (ρ i).tmul (σ i)) ≤
      State.holevoChi p hp hsum ρ + State.holevoChi p hp hsum σ := by
  simp only [State.holevoChi_def]
  -- the two factor marginals of the product-ensemble mixture are the factor-wise mixtures
  have hL : (State.mix p hp hsum fun i => (ρ i).tmul (σ i)).reducedLeft
      = State.mix p hp hsum ρ := by
    rw [State.reducedLeft_mix]; simp only [State.reducedLeft_tmul]
  have hR :
      (State.mix p hp hsum fun i => (ρ i).tmul (σ i)).reducedRight = State.mix p hp hsum σ := by
    rw [State.reducedRight_mix]; simp only [State.reducedRight_tmul]
  -- subadditivity of the von Neumann entropy of the mixture, read off through the marginals
  have hsub : (State.mix p hp hsum fun i => (ρ i).tmul (σ i)).vonNeumannEntropy ≤
      (State.mix p hp hsum ρ).vonNeumannEntropy + (State.mix p hp hsum σ).vonNeumannEntropy := by
    have h := State.vonNeumannEntropy_le_reducedLeft_add_reducedRight
      (State.mix p hp hsum fun i => (ρ i).tmul (σ i))
    rwa [hL, hR] at h
  -- the average component entropy splits over each product state
  have hcomp : ∑ i, p i * ((ρ i).tmul (σ i)).vonNeumannEntropy =
      ∑ i, p i * (ρ i).vonNeumannEntropy + ∑ i, p i * (σ i).vonNeumannEntropy := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [State.vonNeumannEntropy_tmul]; ring
  rw [hcomp]
  linarith [hsub]

/-- **The two-use channel single-letterisation of the HSW converse** (Nielsen & Chuang,
Theorem 12.8, the `n = 2` instance of eqs. (12.99)–(12.101)).  Alice sends a two-letter codeword: to
label `X` she assigns the product input `ρ_X ⊗ σ_X` (each factor a single-use input to the channel
`E`), so the two-use output is `E(ρ_X) ⊗ E(σ_X)`.  Bob applies any joint decoding measurement `m` on
the two-use output system `S ⊗ S`.  Then the classical mutual information between `X` and Bob's
outcome `Y` is at most twice the channel Holevo χ quantity:

`H(X:Y)  ≤  2·χ(E)`.

Composes the three single-use ingredients exactly as N&C's derivation does at `n = 2`:

* the **Holevo bound** `holevoBound_of_chi_monotone` bounds `H(X:Y)` by the Holevo χ of the two-use
  output ensemble `{pₓ, E(ρₓ) ⊗ E(σₓ)}` (eq. (12.99));
* **subadditivity of χ over products** `State.holevoChi_tmul_le` splits that into the sum of the two
  marginal-ensemble χ's `χ({pₓ, E(ρₓ)}) + χ({pₓ, E(σₓ)})` (eq. (12.100)); and
* the **maximisation property** `le_channelHolevoChi` bounds each marginal-ensemble χ by `χ(E)`
  (eq. (12.101)).

This is the bipartite (`n = 2`) instance of the converse single-letterisation; the general `n`-use
bound `H(X:Y) ≤ n·χ(E)` is proved below as
`mutualInfo_channelOutput_piTensor_le_nsmul_channelHolevoChi`, via the `n`-fold χ-subadditivity
`State.holevoChi_piTensor_le`. -/
theorem mutualInfo_channelOutput_tmul_le_two_mul_channelHolevoChi (E : State S → State S)
    {n r : ℕ} [NeZero r] (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (ρ σ : Fin n → State S) (m : Measurement (Fin r) (S ⊗ S)) :
    (Real.mutualInfo fun xy => p xy.1 * m.bornProb ((E (ρ xy.1)).tmul (E (σ xy.1))) xy.2) ≤
      2 * channelHolevoChi E := by
  refine (holevoBound_of_chi_monotone p hp hsum (fun x => (E (ρ x)).tmul (E (σ x))) m).trans ?_
  refine (State.holevoChi_tmul_le p hp hsum (fun x => E (ρ x)) (fun x => E (σ x))).trans ?_
  have hL := le_channelHolevoChi E p hp hsum ρ
  have hR := le_channelHolevoChi E p hp hsum σ
  linarith

/-- **`n`-fold subadditivity of the Holevo χ quantity over product ensembles** (Nielsen & Chuang,
Theorem 12.8, the general form of eqs. (12.99)→(12.100)).  For an ensemble `{pₓ, ⨂ⱼ ρₓⱼ}` whose
states are `n`-fold *products* on `S ^⊗ₛ n`, the Holevo χ is subadditive over the `n` factors:

`χ({pₓ, ⨂ⱼ ρₓⱼ})  ≤  ∑ⱼ χ({pₓ, ρₓⱼ})`.

The `n`-factor generalisation of the bipartite `State.holevoChi_tmul_le`, proved by induction on the
number of factors: the head-peel recursion `State.tmul_piTensor_congr_tensorPowSuccHead_symm`
rewrites `⨂ⱼ ρₓⱼ` as the transport of `(ρₓ 0) ⊗ (⨂ⱼ ρₓ,ⱼ₊₁)`, whose χ is bounded — via invariance
under system isomorphism (`State.holevoChi_congr`) and the bipartite subadditivity
(`State.holevoChi_tmul_le`) — by `χ({pₓ, ρₓ 0}) + χ({pₓ, ⨂ⱼ ρₓ,ⱼ₊₁})`, and the second summand is
controlled by the inductive hypothesis.  The `n = 0` base is the trivial one-dimensional system
`S ^⊗ₛ 0`, on which every state has zero von Neumann entropy, so `χ = 0`. -/
theorem State.holevoChi_piTensor_le {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    ∀ {n : ℕ} (ρ : ι → Fin n → State S),
      State.holevoChi p hp hsum (fun x => State.piTensor fun j => ρ x j) ≤
        ∑ j, State.holevoChi p hp hsum fun x => ρ x j
  | 0, ρ => by
      -- `S ^⊗ₛ 0` is one-dimensional: every state has zero entropy, so `χ = 0 ≤ 0`.
      have hz : ∀ σ : State (S ^⊗ₛ 0), σ.vonNeumannEntropy = 0 := by
        intro σ
        have h := σ.vonNeumannEntropy_le_log_finrank
        rw [QSystem.finrank_tensorPow_space, pow_zero, Nat.cast_one, Real.log_one] at h
        exact le_antisymm h σ.vonNeumannEntropy_nonneg
      rw [State.holevoChi_of_forall_vonNeumannEntropy_zero p hp hsum
          (fun x => State.piTensor fun j : Fin 0 => ρ x j) fun x => hz _,
        Finset.univ_eq_empty, Finset.sum_empty]
      exact (hz _).le
  | n + 1, ρ => by
      have heq : State.holevoChi p hp hsum (fun x => State.piTensor fun j : Fin (n + 1) => ρ x j) =
          State.holevoChi p hp hsum
            (fun x => (ρ x 0).tmul (State.piTensor fun j : Fin n => ρ x j.succ)) := by
        rw [show (fun x => State.piTensor fun j : Fin (n + 1) => ρ x j) =
            (fun x => State.congr (QSystem.tensorPowSuccHead S n).symm
              ((ρ x 0).tmul (State.piTensor fun j : Fin n => ρ x j.succ))) from
          funext fun x => (State.tmul_piTensor_congr_tensorPowSuccHead_symm (ρ x)).symm]
        exact State.holevoChi_congr p hp hsum _ (QSystem.tensorPowSuccHead S n).symm
      rw [heq, Fin.sum_univ_succ]
      refine (State.holevoChi_tmul_le p hp hsum (fun x => ρ x 0)
        (fun x => State.piTensor fun j : Fin n => ρ x j.succ)).trans ?_
      gcongr
      exact State.holevoChi_piTensor_le p hp hsum fun x j => ρ x j.succ

/-- **The `n`-use channel single-letterisation of the HSW converse** (Nielsen & Chuang,
Theorem 12.8, eqs. (12.99)–(12.101)).  Alice sends an `n`-letter codeword: to label `X` she assigns
the product input `ρ_{X,0} ⊗ ⋯ ⊗ ρ_{X,n-1}` (each factor a single-use input to the channel `E`), so
the `n`-use output is the memoryless product `⨂ⱼ E(ρ_{X,j})`.  Bob applies any joint decoding
measurement `m` on the `n`-use output system `S ^⊗ₛ n`.  Then the classical mutual information
between `X` and Bob's outcome `Y` is at most `n` times the channel Holevo χ quantity:

`H(X:Y)  ≤  n·χ(E)`.

This is the full converse single-letterisation, of which
`mutualInfo_channelOutput_tmul_le_two_mul_channelHolevoChi` was the `n = 2` instance.  It composes
the three ingredients exactly as N&C's derivation does: the **Holevo bound**
`holevoBound_of_chi_monotone` (eq. (12.99)), the **`n`-fold subadditivity of χ over products**
`State.holevoChi_piTensor_le` (eq. (12.100)), and the **maximisation property**
`le_channelHolevoChi` applied to each of the `n` output marginal ensembles (eq. (12.101)).  It is
the accessible-information ceiling on which the operational converse `C⁽¹⁾(E) ≤ χ(E)` rests, ready
to be combined with classical Fano's inequality over an `n`-use block code. -/
theorem mutualInfo_channelOutput_piTensor_le_nsmul_channelHolevoChi (E : State S → State S)
    {n K r : ℕ} [NeZero r] (p : Fin K → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (ρ : Fin K → Fin n → State S) (m : Measurement (Fin r) (S ^⊗ₛ n)) :
    (Real.mutualInfo fun xy => p xy.1 * m.bornProb (State.piTensor fun j => E (ρ xy.1 j)) xy.2) ≤
      n * channelHolevoChi E := by
  refine (holevoBound_of_chi_monotone p hp hsum
    (fun x => State.piTensor fun j => E (ρ x j)) m).trans ?_
  refine (State.holevoChi_piTensor_le p hp hsum fun x j => E (ρ x j)).trans ?_
  calc ∑ _j : Fin n, State.holevoChi p hp hsum (fun x => E (ρ x _j))
        ≤ ∑ _j : Fin n, channelHolevoChi E :=
        Finset.sum_le_sum fun j _ => le_channelHolevoChi E p hp hsum fun x => ρ x j
    _ = n * channelHolevoChi E := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The per-block converse inequality of the HSW theorem** (Nielsen & Chuang, eqs.
(12.97)–(12.101)).  For a length-`n` product-state code `c` with `K ≥ 1` messages on the memoryless
channel `E`, the reliably conveyable block rate `log K` is controlled by the accessible information
the channel provides over the `n` uses:

`(1 − p̄)·log K  ≤  log 2  +  n·χ(E)`,

stated here with the maximum error `p̄ = maxError` (average error `≤ maxError`, so the bound with
the average error holds a fortiori).  This is a single block of the operational converse
`C⁽¹⁾(E) ≤ χ(E)`: combined with `log K ≥ nR` and `maxErrorₙ → 0` for an achievable rate `R`,
dividing by `n` and letting `n → ∞` yields `R ≤ χ(E)` (the remaining, separate step).

The proof forms the joint distribution of a uniformly random message `M` and Bob's decoding outcome
`Y`, `P(M, Y) = (1/K)·Tr(σ_M E_Y)`.  Bob's decoder has `Option (Fin K)` outcomes (the `K` messages
plus the inconclusive element `E₀`); relabelling them to `Fin (K + 1)` via
`Measurement.reindexOutcome` along `finSuccEquiv` lets the two ingredients apply to the same law:

* the **`n`-use single-letterisation** `mutualInfo_channelOutput_piTensor_le_nsmul_channelHolevoChi`
  bounds the classical mutual information `H(M : Y) ≤ n·χ(E)`;
* **Fano's converse for a uniform input** `Real.one_sub_fanoErrorProb_mul_log_card_le` gives
  `(1 − pₑ)·log K ≤ log 2 + H(M : Y)`, where `pₑ` is the Fano error probability of the guess
  `Ŷ ↦ (message the decoder announces)`.

Finally `pₑ ≤ p_av ≤ maxError`: guessing the announced message errs at most as often as the code
does, since the correct-guess probability `(1/K)∑_M Tr(σ_M E_M) = 1 − p_av` only grows when the
inconclusive branch carries mass.  As `log K ≥ 0`, the maximum-error form follows. -/
theorem one_sub_maxError_mul_log_card_le_log_two_add_nsmul_channelHolevoChi
    (E : State S → State S) {n K : ℕ} [NeZero K] (c : ProductStateCode E n K) :
    (1 - c.maxError) * Real.log K ≤ Real.log 2 + n * channelHolevoChi E := by
  classical
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  -- The relabelled decoder, with its `Option (Fin K)` outcomes carried to `Fin (K + 1)`.
  set d : Measurement (Fin (K + 1)) (S ^⊗ₛ n) := c.decoder.reindexOutcome (finSuccEquiv K) with hd
  -- The joint law of the uniform message `M` and the decoding outcome `Y`.
  set P : Fin K × Fin (K + 1) → ℝ :=
    fun xy => (K : ℝ)⁻¹ * d.bornProb (c.outputCodeword xy.1) xy.2 with hP
  have hPnn : ∀ q, 0 ≤ P q := by
    intro q; simp only [hP]; exact mul_nonneg (by positivity) (d.bornProb_nonneg _ _)
  -- Each message row of the joint law carries the uniform mass `1/K`.
  have hmarg : ∀ x : Fin K, ∑ y, P (x, y) = (K : ℝ)⁻¹ := by
    intro x
    simp only [hP]
    rw [← Finset.mul_sum, d.sum_bornProb_eq_one, mul_one]
  have hPsum : ∑ q, P q = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hmarg]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hK0]
  have hPuniform : ∀ i, Real.marginalFst P i = (Fintype.card (Fin K) : ℝ)⁻¹ := fun i => by
    rw [Real.marginalFst_apply, Fintype.card_fin]; exact hmarg i
  -- Single-letterisation: `H(M : Y) ≤ n·χ(E)`.
  have hsl : Real.mutualInfo P ≤ (n : ℝ) * channelHolevoChi E := by
    have hpu : ∀ _x : Fin K, (0 : ℝ) ≤ (K : ℝ)⁻¹ := fun _ => by positivity
    have hsu : ∑ _x : Fin K, (K : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hK0]
    have h := mutualInfo_channelOutput_piTensor_le_nsmul_channelHolevoChi
      E (fun _ => (K : ℝ)⁻¹) hpu hsu c.encoder d
    simpa only [hP, ProductStateCode.outputCodeword] using h
  -- The guess: read off the message the decoder announces (`none` guesses an arbitrary message).
  set z : Fin K := ⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩ with hz
  set g : Fin (K + 1) → Fin K := fun j => ((finSuccEquiv K) j).getD z with hg
  -- Fano error probability `≤` average `≤` maximum error probability.
  have hfano_le : Real.fanoErrorProb P g ≤ c.avgError := by
    have hstep : ∑ j, P (g j, j)
        = (K : ℝ)⁻¹ * c.decoder.bornProb (c.outputCodeword z) none
          + ∑ m, (K : ℝ)⁻¹ * c.successProb m := by
      simp only [hP, hg, hd, Measurement.reindexOutcome_bornProb]
      rw [Fintype.sum_equiv (finSuccEquiv K)
          (fun j => (K : ℝ)⁻¹ *
            c.decoder.bornProb (c.outputCodeword (((finSuccEquiv K) j).getD z))
              ((finSuccEquiv K) j))
          (fun y => (K : ℝ)⁻¹ * c.decoder.bornProb (c.outputCodeword (y.getD z)) y)
          (fun j => rfl),
        Fintype.sum_option]
      simp only [Option.getD_none, Option.getD_some, ProductStateCode.successProb]
    have hsucc : ∑ m, (K : ℝ)⁻¹ * c.successProb m = 1 - c.avgError := by
      have hse : ∀ m, c.successProb m = 1 - c.errorProb m := fun m => by
        rw [ProductStateCode.errorProb]; ring
      simp_rw [hse, mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hK0,
        ← Finset.mul_sum, ProductStateCode.avgError, div_eq_inv_mul]
    have hnn : 0 ≤ (K : ℝ)⁻¹ * c.decoder.bornProb (c.outputCodeword z) none :=
      mul_nonneg (by positivity) (c.decoder.bornProb_nonneg _ _)
    rw [Real.fanoErrorProb, hstep, hsucc]
    linarith
  -- Fano's converse for the uniform message, and the assembly.
  have hfano := Real.one_sub_fanoErrorProb_mul_log_card_le hPnn hPsum hPuniform g
  rw [Fintype.card_fin] at hfano
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hmono : (1 - c.maxError) * Real.log K ≤ (1 - Real.fanoErrorProb P g) * Real.log K :=
    mul_le_mul_of_nonneg_right (by linarith [c.avgError_le_maxError]) hlogK
  linarith [hfano, hsl]

/-- **Every achievable rate is at most `χ(E)`** — the analytic core of the HSW converse (Nielsen &
Chuang, eqs. (12.97)–(12.102)).  If a rate `R` (in nats per channel use) is achievable for the
memoryless channel `E` — i.e. there is a family of product-state codes
`codeₙ : ProductStateCode E n ⌈eⁿᴿ⌉₊` with `maxErrorₙ → 0` — then `R ≤ χ(E)`.

This is the short limiting argument sitting on top of the finite-block converse bound
`one_sub_maxError_mul_log_card_le_log_two_add_nsmul_channelHolevoChi`.  For each block length
`n ≥ 1` the code has `Kₙ = ⌈eⁿᴿ⌉₊ ≥ 1` messages, so `log Kₙ ≥ n·R` (as `Kₙ ≥ eⁿᴿ`).  Since
`1 − maxErrorₙ ≥ 0`, the per-block inequality gives

`(1 − maxErrorₙ)·(n·R)  ≤  (1 − maxErrorₙ)·log Kₙ  ≤  log 2 + n·χ(E)`,

and dividing by `n`,

`(1 − maxErrorₙ)·R  ≤  (log 2)/n + χ(E)`.

As `n → ∞` the left side tends to `R` (because `maxErrorₙ → 0`) and the right side to `χ(E)`
(because `(log 2)/n → 0`), whence `R ≤ χ(E)` by comparison of limits. -/
theorem IsProductStateAchievableRate.le_channelHolevoChi {E : State S → State S} {R : ℝ}
    (hR : IsProductStateAchievableRate E R) : R ≤ channelHolevoChi E := by
  obtain ⟨code, hcode⟩ := hR
  -- The message count `Kₙ = ⌈eⁿᴿ⌉₊` is positive (`Kₙ ≥ 1`), supplying `[NeZero Kₙ]`.
  have hKpos : ∀ n : ℕ, 0 < ⌈Real.exp ((n : ℝ) * R)⌉₊ :=
    fun n => Nat.ceil_pos.mpr (Real.exp_pos _)
  -- The per-block inequality, divided by `n`, holds eventually in `n`.
  have hab : ∀ᶠ n : ℕ in Filter.atTop,
      (1 - (code n).maxError) * R ≤ Real.log 2 / (n : ℝ) + channelHolevoChi E := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have : NeZero ⌈Real.exp ((n : ℝ) * R)⌉₊ := ⟨(hKpos n).ne'⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    -- `log Kₙ ≥ n·R`, from `eⁿᴿ ≤ Kₙ`.
    have hKR : (0 : ℝ) < (⌈Real.exp ((n : ℝ) * R)⌉₊ : ℝ) := by exact_mod_cast hKpos n
    have hlogK : (n : ℝ) * R ≤ Real.log (⌈Real.exp ((n : ℝ) * R)⌉₊ : ℝ) :=
      (Real.le_log_iff_exp_le hKR).mpr (Nat.le_ceil _)
    -- The finite-block converse bound, and `1 − maxErrorₙ ≥ 0`.
    have hblock := one_sub_maxError_mul_log_card_le_log_two_add_nsmul_channelHolevoChi E (code n)
    have hmax1 : (code n).maxError ≤ 1 := (code n).maxError_le_one
    have hstep : (1 - (code n).maxError) * ((n : ℝ) * R)
        ≤ Real.log 2 + (n : ℝ) * channelHolevoChi E :=
      (mul_le_mul_of_nonneg_left hlogK (by linarith)).trans hblock
    -- Divide by `n > 0`.
    refine le_of_mul_le_mul_right ?_ hnpos
    have eL : (1 - (code n).maxError) * R * (n : ℝ)
        = (1 - (code n).maxError) * ((n : ℝ) * R) := by ring
    have eR : (Real.log 2 / (n : ℝ) + channelHolevoChi E) * (n : ℝ)
        = Real.log 2 + (n : ℝ) * channelHolevoChi E := by field_simp
    rw [eL, eR]; exact hstep
  -- Comparison of the two limits.
  have hlimL : Filter.Tendsto (fun n : ℕ => (1 - (code n).maxError) * R) Filter.atTop (𝓝 R) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 - (code n).maxError) Filter.atTop (𝓝 1) := by
      simpa using Filter.Tendsto.const_sub (1 : ℝ) hcode
    simpa using h1.mul_const R
  have hlimR : Filter.Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ) + channelHolevoChi E)
      Filter.atTop (𝓝 (channelHolevoChi E)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) Filter.atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
    simpa using h0.add_const (channelHolevoChi E)
  exact le_of_tendsto_of_tendsto hlimL hlimR hab

/-- **The operational converse of the HSW theorem**, `C⁽¹⁾(E) ≤ χ(E)` (Nielsen & Chuang,
Theorem 12.8, eqs. (12.96)–(12.102)).  The product-state capacity of any memoryless channel `E` is
at most its channel Holevo χ quantity: no product-state code family can reliably carry more than
`χ(E)` nats per channel use.

Immediate from `IsProductStateAchievableRate.le_channelHolevoChi`: every achievable rate is
`≤ χ(E)`, and `χ(E) ≥ 0` (`channelHolevoChi_nonneg`), so their supremum — which is `C⁽¹⁾(E)` by
definition — is `≤ χ(E)` (`Real.sSup_le`, which also covers the degenerate empty case
`sSup ∅ = 0 ≤ χ(E)`, so no `[Nonempty (State S)]` hypothesis is needed).

Together with the achievability direction `χ(E) ≤ C⁽¹⁾(E)` (random coding, N&C Box 12.5) —
`channelHolevoChi_le_productStateCapacity` below — this gives the HSW equality `χ(E) = C⁽¹⁾(E)`,
assembled by `le_antisymm` as `channelHolevoChi_eq_productStateCapacity` (both proved below in this
file). -/
theorem productStateCapacity_le_channelHolevoChi (E : State S → State S) :
    productStateCapacity E ≤ channelHolevoChi E :=
  Real.sSup_le (fun _ hR => IsProductStateAchievableRate.le_channelHolevoChi hR)
    (channelHolevoChi_nonneg E)

/-- **The achievability direction of the HSW theorem**, `χ(E) ≤ C⁽¹⁾(E)` (Nielsen & Chuang,
Theorem 12.8, the random-coding half, Box 12.5).  The channel Holevo χ quantity of any memoryless
channel `E` is at most its product-state capacity: rates arbitrarily close to `χ(E)` nats per
channel use are achievable with product-state codes.

This is the operational payoff of the whole random-coding development
(`isProductStateAvgAchievableRate_of_lt_channelHolevoChi`, N&C eqs. (12.72)–(12.83)).  Fixing any
rate `R < χ(E)`, and any strictly smaller `R' < R`:

* `R < χ(E)` makes `R` **average-achievable**
  (`isProductStateAvgAchievableRate_of_lt_channelHolevoChi`): a random product-state codebook has
  expected per-block error tending to `0`, so some codebook family realises rate `R` with
  `avgError → 0`;
* the average→maximum error bridge
  (`IsProductStateAvgAchievableRate.isProductStateAchievableRate_of_lt`, expurgation + truncation)
  then makes every strictly smaller `R' < R` **achievable** (`maxError → 0`);
* hence `R' ≤ C⁽¹⁾(E)` by the maximisation property `le_productStateCapacity`.

`R'` was an arbitrary rate below `R`, so `R ≤ C⁽¹⁾(E)` (`le_of_forall_lt_imp_le_of_dense`, `ℝ`
densely ordered); and `R` was an arbitrary rate below `χ(E)`, so `χ(E) ≤ C⁽¹⁾(E)` by the same
denseness lemma.  The two nested applications bridge the two strict
inequalities the random-coding argument leaves (average-achievability at `R`, achievability only
strictly below `R`).  Needs `[Nonempty (State S)]` — the encoder must name an input state. -/
theorem channelHolevoChi_le_productStateCapacity [Nonempty (State S)] (E : State S → State S) :
    channelHolevoChi E ≤ productStateCapacity E :=
  le_of_forall_lt_imp_le_of_dense fun _ hR =>
    have hav := isProductStateAvgAchievableRate_of_lt_channelHolevoChi hR
    le_of_forall_lt_imp_le_of_dense fun _ hR' =>
      le_productStateCapacity (hav.isProductStateAchievableRate_of_lt hR')

/-- **The Holevo–Schumacher–Westmoreland (HSW) theorem** (Nielsen & Chuang, Theorem 12.8):  the
channel Holevo χ quantity of a memoryless quantum channel equals its product-state capacity,

`χ(E) = C⁽¹⁾(E)`.

The headline result of §12.3: the maximal rate of classical communication over `E` using
product-state inputs (and joint decoding measurements) is exactly the Holevo χ quantity `χ(E)`
(N&C eq. (12.71)).  `le_antisymm` of the two directions just established —

* the operational **converse** `C⁽¹⁾(E) ≤ χ(E)` (`productStateCapacity_le_channelHolevoChi`,
  eqs. (12.96)–(12.102): Holevo bound + subadditivity single-letterisation + Fano); and
* the random-coding **achievability** `χ(E) ≤ C⁽¹⁾(E)`
  (`channelHolevoChi_le_productStateCapacity`, Box 12.5).

Needs `[Nonempty (State S)]` for the achievability direction (the encoder must name an input state);
the converse holds with no such hypothesis. -/
theorem channelHolevoChi_eq_productStateCapacity [Nonempty (State S)] (E : State S → State S) :
    channelHolevoChi E = productStateCapacity E :=
  le_antisymm (channelHolevoChi_le_productStateCapacity E)
    (productStateCapacity_le_channelHolevoChi E)

end AxQM
