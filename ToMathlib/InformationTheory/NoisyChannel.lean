/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.JointEntropy
public import ToMathlib.Analysis.SpecialFunctions.EntropySubadditive
public import ToMathlib.Analysis.SpecialFunctions.DataProcessingInequality
public import ToMathlib.InformationTheory.Fano
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order.Compact

/-!
# Discrete memoryless channels and the information capacity

For finite input and output alphabets `ι`, `κ` a **discrete memoryless channel** (Nielsen &
Chuang, *Quantum Computation and Quantum Information*, p. 551) is a family of conditional
probabilities `q : ι → κ → ℝ`, `q x y = p(y | x)`, satisfying `q x y ≥ 0` and `∑ y, q x y = 1`
for every input `x` (`Real.IsChannel`). Fed an input distribution `p : ι → ℝ` for a random
variable `X`, the channel produces the joint input–output law
`Real.channelJoint q p (x, y) = p x · q x y` of `(X, Y)`, whose second marginal is the induced
**output distribution** `Real.channelOutput q p y = ∑ x, p x · q x y` of `Y`.

The **channel mutual information** for input distribution `p` is the mutual information of that
joint law,

`Real.channelMutualInfo q p := Real.mutualInfo (Real.channelJoint q p) = H(X : Y)`,

and the **(information) capacity** of the channel is the maximum of `H(X : Y)` over all input
distributions,

`Real.channelCapacity q := sSup (Real.channelMutualInfo q '' probSimplex ι) = max_{p(x)} H(X : Y)`.

This is exactly the right-hand side of **Shannon's noisy channel coding theorem**
(N&C Theorem 12.7, eq. (12.67)),

`C(N) = max_{p(x)} H(X : Y)`,

whose left-hand side `C(N)` is the *operational* capacity: the supremum of rates achievable by
encoding/decoding schemes with vanishing error. Following N&C (p. 552) a rate `R` is achievable
when there is a family of block codes `ChannelCode ι κ n ⌈2 ^ (n R)⌉` — an encoder `Cₙ` and decoder
`Dₙ` — whose block error probability `Real.ChannelCode.maxErrorProb` (N&C eq. (12.66)) tends to `0`,
and `Real.channelOpCapacity q` is the supremum of the achievable rates. This file develops both the
information-theoretic right-hand side and the operational left-hand side, together with the trivial
converse `channelOpCapacity q ≤ log₂ |ι|`; the coding theorem `C(N) = max_{p(x)} H(X : Y)`
identifying the two — whose proof N&C defers to the quantum HSW theorem of the next section — is
built in subsequent files.

## Main declarations

* `Real.IsChannel` — a conditional distribution `q : ι → κ → ℝ` is a channel.
* `Real.channelOutput`, `Real.channelJoint` — the induced output and joint distributions.
* `Real.channelMutualInfo` — `H(X : Y)` for a given input distribution.
* `Real.channelMutualInfo_eq` — `H(X : Y) = H(Y) − ∑ₓ p(x) H(Y | X = x)` (N&C eq. (12.68)).
* `Real.channelMutualInfo_eq_entropy_add_entropy_sub_entropy` — the three-entropy decomposition
  `H(X : Y) = H(X) + H(Y) − H(X, Y)`, with `Real.channelJoint_marginalFst` /
  `Real.channelJoint_marginalSnd` identifying the joint law's marginals as `p` and `channelOutput`.
* `Real.channelCapacity` — the information capacity `max_{p(x)} H(X : Y)`.
* `Real.exists_isMaxOn_channelMutualInfo` — the capacity is a genuine maximum, attained at some
  input distribution: the `max` of eq. (12.67) is well-defined (the simplex is compact and
  `channelMutualInfo` is continuous).
* `Real.ChannelCode` — a length-`n`, `M`-message block code (encoder `Cₙ` and decoder `Dₙ`).
* `Real.ChannelCode.maxErrorProb` — the block error probability `max_m p(Dₙ(Y) ≠ m | X = Cₙ(m))`
  (N&C eq. (12.66)), with `maxErrorProb_nonneg` / `maxErrorProb_le_one`.
* `Real.IsAchievableRate`, `Real.channelOpCapacity` — achievable rates and the operational capacity
  `C(N)`, the supremum of achievable rates, with `channelOpCapacity_nonneg`, `le_channelOpCapacity`
  and the trivial converse `channelOpCapacity_le_log_card_div` (`C(N) ≤ log₂ |ι|`).
* `Real.channelMutualInfo_channelSeqProb_le` — the **single-letterization bound**
  `H(Xⁿ : Yⁿ) ≤ n · max_{p(x)} H(X : Y)` for the memoryless `n`-use channel `channelSeqProb q`, the
  entropy input to the converse half of the coding theorem (with `isChannel_channelSeqProb`, that
  the `n`-use channel is itself a channel).
* `Real.ChannelCode.jointLaw` — the joint law of a uniform message `W`, its codeword `Xⁿ = Cₙ(W)`
  and the channel output `Yⁿ`, with its uniform message marginal (`entropy_marginalFst_jointLaw`,
  `H(W) = log M`), channel `(Xⁿ, Yⁿ)`-marginal (`marginalSnd_jointLaw`) and Markov structure
  (`isMarkovChain_jointLaw`).
* `Real.ChannelCode.one_sub_fanoErrorProb_mul_log_le` — the **per-`n` converse inequality**
  `(1 − P̄ₑ) · log M ≤ log 2 + n · max_{p(x)} H(X : Y)`, combining Fano's inequality, the data
  processing inequality and the single-letterization bound on `jointLaw`.

## Context

This is pure classical information theory, quantifying over functions `q : ι → κ → ℝ` and
`p : ι → ℝ`, built on the `Real.mutualInfo` development. These declarations are the statement of
N&C Theorem 12.7.

Entropies are measured in *nats* (natural logarithm), as elsewhere in the library; N&C uses *bits*.
The capacity bound `channelMutualInfo q p ≤ log (card κ)` and the identity (12.68) are
base-independent, so this is a faithful reformulation, not a weakening.
-/

@[expose] public section

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The probability distributions on a finite type `ι`, as functions `ι → ℝ`: nonnegative weights
summing to `1`. -/
def probSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}

theorem isClosed_probSimplex (ι : Type*) [Fintype ι] : IsClosed (probSimplex ι) := by
  have h : probSimplex ι = (⋂ x, {p : ι → ℝ | 0 ≤ p x}) ∩ {p | ∑ x, p x = 1} := by
    ext p
    simp [probSimplex]
  rw [h]
  exact (isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)).inter
    (isClosed_eq (continuous_finsetSum _ fun x _ => continuous_apply x) continuous_const)

theorem probSimplex_subset_Icc (ι : Type*) [Fintype ι] : probSimplex ι ⊆ Set.Icc 0 1 := by
  classical
  refine fun p hp => ⟨fun x => hp.1 x, fun x => ?_⟩
  rw [Pi.one_apply, ← hp.2]
  exact Finset.single_le_sum (fun y _ => hp.1 y) (Finset.mem_univ x)

theorem isCompact_probSimplex (ι : Type*) [Fintype ι] : IsCompact (probSimplex ι) :=
  isCompact_Icc.of_isClosed_subset (isClosed_probSimplex ι) (probSimplex_subset_Icc ι)

/-! ### The channel and its induced distributions -/

/-- A **discrete memoryless channel** with input alphabet `ι` and output alphabet `κ`: a family of
conditional probabilities `q x y = p(y | x)` that is nonnegative and normalized over the output for
each input (Nielsen & Chuang, p. 551, eqs. (12.64)–(12.65)). -/
structure IsChannel (q : ι → κ → ℝ) : Prop where
  /-- Conditional probabilities are nonnegative. -/
  nonneg : ∀ x y, 0 ≤ q x y
  /-- For each input the conditional distribution over outputs sums to one. -/
  row_sum : ∀ x, ∑ y, q x y = 1

/-- The **output distribution** `p_Y(y) = ∑ₓ p(x) q(y | x)` induced by feeding a channel `q` an
input distribution `p`. -/
noncomputable def channelOutput (q : ι → κ → ℝ) (p : ι → ℝ) : κ → ℝ := fun y => ∑ x, p x * q x y

omit [Fintype κ] in
@[simp] theorem channelOutput_apply (q : ι → κ → ℝ) (p : ι → ℝ) (y : κ) :
    channelOutput q p y = ∑ x, p x * q x y := rfl

/-- The **joint input–output distribution** `p_{XY}(x, y) = p(x) q(y | x)` of the input random
variable `X` and the channel output `Y`. -/
noncomputable def channelJoint (q : ι → κ → ℝ) (p : ι → ℝ) : ι × κ → ℝ :=
  fun xy => p xy.1 * q xy.1 xy.2

omit [Fintype ι] [Fintype κ] in
@[simp] theorem channelJoint_apply (q : ι → κ → ℝ) (p : ι → ℝ) (xy : ι × κ) :
    channelJoint q p xy = p xy.1 * q xy.1 xy.2 := rfl

omit [Fintype κ] in
/-- The second marginal of the joint law is the output distribution. -/
theorem channelJoint_marginalSnd (q : ι → κ → ℝ) (p : ι → ℝ) :
    marginalSnd (channelJoint q p) = channelOutput q p := by
  funext y; rfl

omit [Fintype ι] in
/-- The first marginal of the joint law is the input distribution `p`: summing `p(x) q(y | x)` over
the output leaves `p(x) · ∑_y q(y | x) = p(x)`, using that each channel row sums to `1`. -/
theorem channelJoint_marginalFst {q : ι → κ → ℝ} (hN : IsChannel q) (p : ι → ℝ) :
    marginalFst (channelJoint q p) = p := by
  funext x
  calc marginalFst (channelJoint q p) x
      = ∑ y, p x * q x y := by simp_rw [marginalFst_apply, channelJoint_apply]
    _ = p x * ∑ y, q x y := by rw [Finset.mul_sum]
    _ = p x := by rw [hN.row_sum, mul_one]

omit [Fintype ι] in
/-- The joint distribution `p(x) q(y | x)` is nonnegative when the input distribution is. -/
theorem channelJoint_nonneg {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) : ∀ xy, 0 ≤ channelJoint q p xy :=
  fun xy => mul_nonneg (hp0 xy.1) (hN.nonneg xy.1 xy.2)

/-- The output distribution is nonnegative when the input distribution is. -/
theorem channelOutput_nonneg {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) : ∀ y, 0 ≤ channelOutput q p y :=
  fun y => Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hN.nonneg x y)

/-- The joint distribution `p(x) q(y | x)` is normalized when the input distribution is. -/
theorem sum_channelJoint {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp1 : ∑ x, p x = 1) : ∑ xy, channelJoint q p xy = 1 := by
  rw [Fintype.sum_prod_type]
  calc ∑ x, ∑ y, channelJoint q p (x, y)
      = ∑ x, p x * ∑ y, q x y := by simp_rw [channelJoint_apply, Finset.mul_sum]
    _ = ∑ x, p x := by simp_rw [hN.row_sum, mul_one]
    _ = 1 := hp1

/-- The output distribution is normalized when the input distribution is. -/
theorem sum_channelOutput {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp1 : ∑ x, p x = 1) : ∑ y, channelOutput q p y = 1 := by
  calc ∑ y, channelOutput q p y
      = ∑ x, ∑ y, p x * q x y := by simp_rw [channelOutput_apply]; rw [Finset.sum_comm]
    _ = ∑ x, p x * ∑ y, q x y := by simp_rw [Finset.mul_sum]
    _ = ∑ x, p x := by simp_rw [hN.row_sum, mul_one]
    _ = 1 := hp1

/-- The output distribution of a channel fed an input distribution in the input simplex lies in the
output simplex: it is nonnegative and normalized. -/
theorem channelOutput_mem_probSimplex {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp : p ∈ probSimplex ι) : channelOutput q p ∈ probSimplex κ :=
  ⟨channelOutput_nonneg hN hp.1, sum_channelOutput hN hp.2⟩

/-! ### Channel mutual information -/

/-- The **channel mutual information** `H(X : Y)` between a channel `q`'s input `X`, distributed as
`p`, and its output `Y`: the mutual information of the joint input–output law. -/
noncomputable def channelMutualInfo (q : ι → κ → ℝ) (p : ι → ℝ) : ℝ :=
  mutualInfo (channelJoint q p)

/-- **Mutual information as output entropy minus noise entropy** (Nielsen & Chuang eq. (12.68)):
`H(X : Y) = H(Y) − ∑ₓ p(x) H(Y | X = x)`, where `H(Y)` is the output entropy and each `H(Y | X = x)`
is the entropy of the channel's conditional distribution `q(· | x)`. -/
theorem channelMutualInfo_eq (q : ι → κ → ℝ) {p : ι → ℝ} (hq : ∀ x, ∑ y, q x y = 1) :
    channelMutualInfo q p = entropy (channelOutput q p) - ∑ x, p x * entropy (q x) :=
  mutualInfo_prod_conditional p q hq

/-- **Mutual information as the three-entropy decomposition** `H(X : Y) = H(X) + H(Y) − H(X, Y)`:
the input entropy plus the output entropy minus the joint entropy. This is the channel form of
`mutualInfo_eq`, obtained by identifying the two marginals of the joint law `channelJoint q p` as
the input distribution `p` (`channelJoint_marginalFst`) and the output distribution
`channelOutput q p` (`channelJoint_marginalSnd`). -/
theorem channelMutualInfo_eq_entropy_add_entropy_sub_entropy {q : ι → κ → ℝ} (hN : IsChannel q)
    (p : ι → ℝ) :
    channelMutualInfo q p
      = entropy p + entropy (channelOutput q p) - entropy (channelJoint q p) := by
  unfold channelMutualInfo
  rw [mutualInfo_eq, channelJoint_marginalFst hN, channelJoint_marginalSnd]

/-- The channel mutual information is nonnegative: `0 ≤ H(X : Y)`. -/
theorem channelMutualInfo_nonneg {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) : 0 ≤ channelMutualInfo q p :=
  mutualInfo_nonneg (channelJoint_nonneg hN hp0) (sum_channelJoint hN hp1)

/-- The channel mutual information is at most the logarithm of the output alphabet size:
`H(X : Y) ≤ H(Y) ≤ log |κ|`. -/
theorem channelMutualInfo_le_log_card [Nonempty κ] {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    channelMutualInfo q p ≤ Real.log (Fintype.card κ) :=
  calc channelMutualInfo q p
      ≤ entropy (marginalSnd (channelJoint q p)) :=
        mutualInfo_le_marginalSnd (channelJoint_nonneg hN hp0)
    _ = entropy (channelOutput q p) := by rw [channelJoint_marginalSnd]
    _ ≤ Real.log (Fintype.card κ) :=
        entropy_le_log_card (channelOutput_nonneg hN hp0) (sum_channelOutput hN hp1)

/-- The channel mutual information is a continuous function of the input distribution. -/
theorem continuous_channelMutualInfo (q : ι → κ → ℝ) : Continuous (channelMutualInfo q) := by
  have h : Continuous (channelJoint q) := by
    unfold channelJoint
    exact continuous_pi fun xy => (continuous_apply xy.1).mul continuous_const
  exact continuous_mutualInfo.comp h

/-! ### The information capacity -/

/-- The **information capacity** of a channel `q`: the maximum of the mutual information `H(X : Y)`
over all input distributions `p`, i.e. the right-hand side `max_{p(x)} H(X : Y)` of Shannon's noisy
channel coding theorem (Nielsen & Chuang Theorem 12.7, eq. (12.67)). -/
noncomputable def channelCapacity (q : ι → κ → ℝ) : ℝ :=
  sSup (channelMutualInfo q '' probSimplex ι)

/-- The uniform distribution lies in the standard simplex; a witness that the simplex (hence the set
of achievable mutual informations) is nonempty, and the canonical maximizer for capacities attained
at the uniform input. -/
theorem uniform_mem_probSimplex [Nonempty ι] :
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) ∈ probSimplex ι := by
  refine ⟨fun _ => by positivity, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- The set of achievable mutual informations is bounded above by `log |κ|`. -/
private theorem bddAbove_channelMutualInfo_image [Nonempty κ] {q : ι → κ → ℝ} (hN : IsChannel q) :
    BddAbove (channelMutualInfo q '' probSimplex ι) := by
  refine ⟨Real.log (Fintype.card κ), ?_⟩
  rintro z ⟨p, hp, rfl⟩
  exact channelMutualInfo_le_log_card hN hp.1 hp.2

/-- The capacity is an upper bound for the mutual information of every input distribution. -/
theorem le_channelCapacity [Nonempty κ] {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp : p ∈ probSimplex ι) : channelMutualInfo q p ≤ channelCapacity q :=
  le_csSup (bddAbove_channelMutualInfo_image hN) ⟨p, hp, rfl⟩

/-- **Upper bound for the capacity.** If the channel mutual information is bounded by `C` for every
input distribution in the simplex, then the capacity is bounded by `C`. -/
theorem channelCapacity_le [Nonempty ι] {q : ι → κ → ℝ} {C : ℝ}
    (h : ∀ p ∈ probSimplex ι, channelMutualInfo q p ≤ C) : channelCapacity q ≤ C := by
  refine csSup_le ⟨_, _, uniform_mem_probSimplex, rfl⟩ ?_
  rintro z ⟨p, hp, rfl⟩
  exact h p hp

/-- The capacity is bounded above by the logarithm of the output alphabet size. -/
theorem channelCapacity_le_log_card [Nonempty ι] [Nonempty κ] {q : ι → κ → ℝ} (hN : IsChannel q) :
    channelCapacity q ≤ Real.log (Fintype.card κ) := by
  refine csSup_le ⟨_, _, uniform_mem_probSimplex, rfl⟩ ?_
  rintro z ⟨p, hp, rfl⟩
  exact channelMutualInfo_le_log_card hN hp.1 hp.2

/-- The capacity is nonnegative. -/
theorem channelCapacity_nonneg [Nonempty ι] [Nonempty κ] {q : ι → κ → ℝ} (hN : IsChannel q) :
    0 ≤ channelCapacity q :=
  le_trans
    (channelMutualInfo_nonneg hN uniform_mem_probSimplex.1 uniform_mem_probSimplex.2)
    (le_channelCapacity hN uniform_mem_probSimplex)

/-- **The capacity as an attained maximum.** If the channel mutual information `channelMutualInfo q`
attains its maximum over the input simplex at `p₀` (an `IsMaxOn`), then the capacity equals that
maximal value `channelMutualInfo q p₀`. This packages the two-sided `sSup` argument — the `csSup_le`
upper bound and the `le_channelCapacity` attainment — once, so a concrete capacity computation
reduces to exhibiting a maximizer; it composes directly with `exists_isMaxOn_channelMutualInfo`,
which produces such a maximizer. -/
theorem channelCapacity_eq_of_isMaxOn [Nonempty κ] {q : ι → κ → ℝ} (hN : IsChannel q) {p₀ : ι → ℝ}
    (hp₀ : p₀ ∈ probSimplex ι) (hmax : IsMaxOn (channelMutualInfo q) (probSimplex ι) p₀) :
    channelCapacity q = channelMutualInfo q p₀ := by
  refine le_antisymm ?_ (le_channelCapacity hN hp₀)
  refine csSup_le ⟨_, ⟨p₀, hp₀, rfl⟩⟩ ?_
  rintro z ⟨p, hp, rfl⟩
  exact isMaxOn_iff.mp hmax p hp

/-- **The capacity is a genuine maximum** (Nielsen & Chuang eq. (12.67), the `max_{p(x)}`): there is
an input distribution `p` in the simplex at which the mutual information `H(X : Y)` attains its
supremum, so `channelCapacity q = channelMutualInfo q p` and `p` maximizes `channelMutualInfo q`
over the simplex. The maximum exists because the simplex of input distributions is compact and
`channelMutualInfo q` is continuous. -/
theorem exists_isMaxOn_channelMutualInfo [Nonempty ι] [Nonempty κ] (q : ι → κ → ℝ) :
    ∃ p ∈ probSimplex ι, IsMaxOn (channelMutualInfo q) (probSimplex ι) p ∧
      channelCapacity q = channelMutualInfo q p := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_probSimplex ι).exists_isMaxOn
    ⟨_, uniform_mem_probSimplex⟩ (continuous_channelMutualInfo q).continuousOn
  refine ⟨p, hp, hmax, ?_⟩
  have hg : IsGreatest (channelMutualInfo q '' probSimplex ι) (channelMutualInfo q p) :=
    ⟨⟨p, hp, rfl⟩, by rintro z ⟨p', hp', rfl⟩; exact isMaxOn_iff.mp hmax p' hp'⟩
  exact hg.csSup_eq

/-! ### Operational capacity: block codes, error probability, and achievable rates -/

section OperationalCapacity
open Finset Filter Topology

variable {n M : ℕ}

/-- A **block code** for `n` uses of a channel with input alphabet `ι`, output alphabet `κ` and `M`
messages (Nielsen & Chuang, p. 551): an `encode` (their `Cₙ`) assigning to each of the `M` messages
an input string `Fin n → ι` to be sent through `n` uses of the channel, and a `decode` (their `Dₙ`)
assigning a message to every possible output string `Fin n → κ`. The intended dependence of the
message count on the rate `R` is `M = ⌈2 ^ (n R)⌉`. -/
structure ChannelCode (ι κ : Type*) (n M : ℕ) where
  /-- The encoding map `Cₙ`: each message is assigned an input codeword of length `n`. -/
  encode : Fin M → (Fin n → ι)
  /-- The decoding map `Dₙ`: each length-`n` output string is decoded to a message. -/
  decode : (Fin n → κ) → Fin M

/-- The **memoryless `n`-use transition probability** `p(y | x) = ∏ⱼ q(yⱼ | xⱼ)` of receiving the
output string `y : Fin n → κ` given the input string `x : Fin n → ι`, for a channel `q` used `n`
times. The channel is memoryless, so the `n` uses are independent and the joint conditional
probability factorizes. -/
noncomputable def channelSeqProb (q : ι → κ → ℝ) (x : Fin n → ι) (y : Fin n → κ) : ℝ :=
  ∏ j, q (x j) (y j)

omit [Fintype ι] in
/-- The memoryless `n`-use transition probability is nonnegative for a channel. -/
theorem channelSeqProb_nonneg {q : ι → κ → ℝ} (hN : IsChannel q) (x : Fin n → ι) (y : Fin n → κ) :
    0 ≤ channelSeqProb q x y :=
  Finset.prod_nonneg fun _ _ => hN.nonneg _ _

omit [Fintype ι] in
/-- For a channel, the memoryless `n`-use law is a probability distribution over the output strings:
`∑_y ∏ⱼ q(yⱼ | xⱼ) = ∏ⱼ (∑_{yⱼ} q(yⱼ | xⱼ)) = 1`. -/
theorem sum_channelSeqProb {q : ι → κ → ℝ} (hN : IsChannel q) (x : Fin n → ι) :
    ∑ y : Fin n → κ, channelSeqProb q x y = 1 := by
  unfold channelSeqProb
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp [hN.row_sum]

/-- The **conditional block-error probability** for message `m` under channel `q`: the probability
`p(Dₙ(Y) ≠ m | X = Cₙ(m))` that the decoded channel output differs from `m`, given that the codeword
`code.encode m` was fed through `n` uses of the channel. -/
noncomputable def ChannelCode.condErrorProb (q : ι → κ → ℝ) (code : ChannelCode ι κ n M)
    (m : Fin M) : ℝ :=
  ∑ y ∈ univ.filter (fun y => code.decode y ≠ m), channelSeqProb q (code.encode m) y

omit [Fintype ι] in
/-- The conditional block-error probability is nonnegative. -/
theorem ChannelCode.condErrorProb_nonneg {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) (m : Fin M) : 0 ≤ code.condErrorProb q m :=
  Finset.sum_nonneg fun _ _ => channelSeqProb_nonneg hN _ _

omit [Fintype ι] in
/-- The conditional block-error probability is at most `1`: the erroneous outputs form a subset of
all outputs, whose total probability is `1`. -/
theorem ChannelCode.condErrorProb_le_one {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) (m : Fin M) : code.condErrorProb q m ≤ 1 := by
  rw [ChannelCode.condErrorProb, ← sum_channelSeqProb hN (code.encode m)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun y _ _ => channelSeqProb_nonneg hN _ _

/-- The **block error probability** of a code (Nielsen & Chuang, eq. (12.66)):
`p(Cₙ, Dₙ) = max_m p(Dₙ(Y) ≠ m | X = Cₙ(m))`, the maximum of the conditional error probability over
all messages. (For an empty message set the supremum is `0`.) -/
noncomputable def ChannelCode.maxErrorProb (q : ι → κ → ℝ) (code : ChannelCode ι κ n M) : ℝ :=
  ⨆ m, code.condErrorProb q m

omit [Fintype ι] in
/-- The block error probability is nonnegative. -/
theorem ChannelCode.maxErrorProb_nonneg {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) : 0 ≤ code.maxErrorProb q :=
  Real.iSup_nonneg fun m => code.condErrorProb_nonneg hN m

omit [Fintype ι] in
/-- The block error probability is at most `1`. -/
theorem ChannelCode.maxErrorProb_le_one {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) : code.maxErrorProb q ≤ 1 :=
  Real.iSup_le (fun m => code.condErrorProb_le_one hN m) (by norm_num)

omit [Fintype ι] in
/-- Each conditional error probability is bounded by the block error probability. -/
theorem ChannelCode.condErrorProb_le_maxErrorProb (q : ι → κ → ℝ) (code : ChannelCode ι κ n M)
    (m : Fin M) : code.condErrorProb q m ≤ code.maxErrorProb q :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range _)) m

/-- **Trivial converse / pigeonhole bound.** If a code has more messages than there are input
strings, `|ι|ⁿ < M`, then two distinct messages share the same codeword; the channel output cannot
distinguish them, so the block error probability is at least `1/2`.

Concretely, if `code.encode m₁ = code.encode m₂` with `m₁ ≠ m₂`, then the two conditional error
sets `{y : Dₙ(y) ≠ m₁}` and `{y : Dₙ(y) ≠ m₂}` cover all outputs (a single decoded message differs
from at least one of `m₁, m₂`), so with the shared codeword's output law of total mass `1` the two
conditional error probabilities sum to at least `1`, forcing the larger — hence the maximum — to be
at least `1/2`. -/
theorem ChannelCode.half_le_maxErrorProb_of_card_lt {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) (hlt : Fintype.card ι ^ n < M) :
    1 / 2 ≤ code.maxErrorProb q := by
  classical
  -- Two distinct messages share a codeword (pigeonhole: `M` messages, `|ι|ⁿ` codewords).
  obtain ⟨m₁, m₂, hne, heq⟩ : ∃ m₁ m₂ : Fin M, m₁ ≠ m₂ ∧ code.encode m₁ = code.encode m₂ := by
    have hcard : Fintype.card (Fin n → ι) < Fintype.card (Fin M) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; exact hlt
    exact Fintype.exists_ne_map_eq_of_card_lt code.encode hcard
  -- The two conditional error sets cover every output.
  have hcover : (univ.filter (fun y : Fin n → κ => code.decode y ≠ m₁)) ∪
      (univ.filter (fun y => code.decode y ≠ m₂)) = univ := by
    rw [← Finset.filter_or]
    refine Finset.filter_true_of_mem fun y _ => ?_
    rcases eq_or_ne (code.decode y) m₁ with h | h
    · exact Or.inr (h ▸ hne)
    · exact Or.inl h
  -- The two conditional error probabilities sum to at least the total mass `1`.
  have hkey : (1 : ℝ) ≤ code.condErrorProb q m₁ + code.condErrorProb q m₂ := by
    have hP2 : ∀ y, channelSeqProb q (code.encode m₂) y = channelSeqProb q (code.encode m₁) y :=
      fun y => by rw [heq]
    rw [ChannelCode.condErrorProb, ChannelCode.condErrorProb]
    simp_rw [hP2]
    set f := fun y => channelSeqProb q (code.encode m₁) y with hf
    set s₁ := univ.filter (fun y : Fin n → κ => code.decode y ≠ m₁) with hs₁
    set s₂ := univ.filter (fun y : Fin n → κ => code.decode y ≠ m₂) with hs₂
    have hunion := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
    have hinter : 0 ≤ ∑ y ∈ s₁ ∩ s₂, f y :=
      Finset.sum_nonneg fun _ _ => channelSeqProb_nonneg hN _ _
    have htot : ∑ y ∈ s₁ ∪ s₂, f y = 1 := by
      rw [hcover, hf]; exact sum_channelSeqProb hN (code.encode m₁)
    rw [htot] at hunion
    linarith
  -- Hence the maximum of the two is at least `1/2`.
  have h1 := code.condErrorProb_le_maxErrorProb q m₁
  have h2 := code.condErrorProb_le_maxErrorProb q m₂
  linarith

omit [Fintype ι] in
/-- A code whose message set has at most one element (`M ≤ 1`) has block error probability `0`:
there is no message to confuse the sole message with, so every output decodes correctly. -/
theorem ChannelCode.maxErrorProb_eq_zero_of_le_one {q : ι → κ → ℝ}
    (code : ChannelCode ι κ n M) (hM : M ≤ 1) : code.maxErrorProb q = 0 := by
  have hsub : ∀ a b : Fin M, a = b := fun a b => by
    have := a.isLt; have := b.isLt; ext; omega
  have hcond : ∀ m, code.condErrorProb q m = 0 := by
    intro m
    have hempty : univ.filter (fun y : Fin n → κ => code.decode y ≠ m) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      exact fun y _ => not_not.mpr (hsub _ _)
    rw [ChannelCode.condErrorProb, hempty, Finset.sum_empty]
  simp [ChannelCode.maxErrorProb, hcond]

/-- A rate `R` (in bits) is **achievable** for a channel `q` when there is a family of block codes
`codeₙ : ChannelCode ι κ n ⌈2 ^ (n R)⌉`, one per block length `n`, whose block error probability
`maxErrorProb` tends to `0` as `n → ∞` (Nielsen & Chuang, p. 552). The message count
`⌈exp (n · R · log 2)⌉₊` is `⌈2 ^ (n R)⌉` — at least `2 ^ (n R)` messages, corresponding to a rate
of `R` bits per channel use over `n` uses. -/
def IsAchievableRate (q : ι → κ → ℝ) (R : ℝ) : Prop :=
  ∃ code : (n : ℕ) → ChannelCode ι κ n ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊,
    Tendsto (fun n => (code n).maxErrorProb q) atTop (𝓝 0)

omit [Fintype ι] in
/-- Rate `0` is achievable (with a single-message code every output decodes correctly). -/
theorem isAchievableRate_zero [Nonempty ι] (q : ι → κ → ℝ) : IsAchievableRate q 0 := by
  have hle : ∀ n : ℕ, ⌈Real.exp ((n : ℝ) * 0 * Real.log 2)⌉₊ ≤ 1 := by
    intro n; simp
  have hpos : ∀ n : ℕ, 0 < ⌈Real.exp ((n : ℝ) * 0 * Real.log 2)⌉₊ :=
    fun n => Nat.ceil_pos.mpr (Real.exp_pos _)
  refine ⟨fun n => ⟨fun _ _ => Classical.arbitrary ι, fun _ => ⟨0, hpos n⟩⟩, ?_⟩
  exact tendsto_const_nhds.congr fun n =>
    (ChannelCode.maxErrorProb_eq_zero_of_le_one _ (hle n)).symm

/-- The **operational capacity** `C(N)` of a channel `q`: the supremum of all achievable rates
(Nielsen & Chuang, p. 552). Shannon's noisy channel coding theorem (Theorem 12.7) identifies this
with the information capacity `channelCapacity q = max_{p(x)} H(X : Y)`. -/
noncomputable def channelOpCapacity (q : ι → κ → ℝ) : ℝ :=
  sSup {R | IsAchievableRate q R}

/-- Every achievable rate is at most `log |ι| / log 2 = log₂ |ι|` (the trivial converse): a rate `R`
strictly above this would require, for every `n ≥ 1`, more than `|ι|ⁿ` messages, so the pigeonhole
bound forces block error `≥ 1/2`, contradicting that the error tends to `0`. -/
private theorem isAchievableRate_le [Nonempty ι] {q : ι → κ → ℝ} (hN : IsChannel q) {R : ℝ}
    (hR : IsAchievableRate q R) : R ≤ Real.log (Fintype.card ι) / Real.log 2 := by
  obtain ⟨code, hcode⟩ := hR
  by_contra hcon
  rw [not_le] at hcon
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcardpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlogcard : Real.log (Fintype.card ι) < R * Real.log 2 := by
    rw [div_lt_iff₀ hlog2] at hcon; linarith
  -- For every `n ≥ 1` the message count exceeds `|ι|ⁿ`, so block error is `≥ 1/2`.
  have hhalf : ∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 ≤ (code n).maxErrorProb q := by
    intro n hn
    apply ChannelCode.half_le_maxErrorProb_of_card_lt hN (code n)
    rw [Nat.lt_ceil]
    push_cast
    have e1 : Real.exp ((n : ℝ) * Real.log (Fintype.card ι)) = ((Fintype.card ι : ℝ)) ^ n := by
      rw [Real.exp_natCast_mul, Real.exp_log hcardpos]
    rw [← e1]
    refine Real.exp_lt_exp.mpr ?_
    have hpos_n : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    calc (n : ℝ) * Real.log (Fintype.card ι)
        < (n : ℝ) * (R * Real.log 2) := mul_lt_mul_of_pos_left hlogcard hpos_n
      _ = (n : ℝ) * R * Real.log 2 := by ring
  exact absurd (ge_of_tendsto hcode (eventually_atTop.mpr ⟨1, hhalf⟩)) (by norm_num)

omit [Fintype ι] in
/-- The set of achievable rates is bounded above (by `log₂ |ι|`), so the operational capacity is a
well-defined supremum. -/
private theorem bddAbove_setOf_isAchievableRate [Finite ι] [Nonempty ι] {q : ι → κ → ℝ}
    (hN : IsChannel q) : BddAbove {R | IsAchievableRate q R} := by
  have := Fintype.ofFinite ι
  exact ⟨Real.log (Fintype.card ι) / Real.log 2, fun _ hR => isAchievableRate_le hN hR⟩

omit [Fintype ι] in
/-- Every achievable rate is at most the operational capacity. -/
theorem le_channelOpCapacity [Finite ι] [Nonempty ι] {q : ι → κ → ℝ} (hN : IsChannel q) {R : ℝ}
    (hR : IsAchievableRate q R) : R ≤ channelOpCapacity q :=
  le_csSup (bddAbove_setOf_isAchievableRate hN) hR

omit [Fintype ι] in
/-- The operational capacity is nonnegative (rate `0` is achievable). -/
theorem channelOpCapacity_nonneg [Finite ι] [Nonempty ι] {q : ι → κ → ℝ} (hN : IsChannel q) :
    0 ≤ channelOpCapacity q :=
  le_channelOpCapacity hN (isAchievableRate_zero q)

/-- **Trivial converse.** The operational capacity is at most `log |ι| / log 2 = log₂ |ι|`, the
base-2 logarithm of the input alphabet size: you cannot reliably transmit more than `log₂ |ι|` bits
per channel use. (Shannon's theorem refines this to `max_{p(x)} H(X : Y) ≤ log₂ |ι|`.) -/
theorem channelOpCapacity_le_log_card_div [Nonempty ι] {q : ι → κ → ℝ} (hN : IsChannel q) :
    channelOpCapacity q ≤ Real.log (Fintype.card ι) / Real.log 2 :=
  csSup_le ⟨0, isAchievableRate_zero q⟩ fun _ hR => isAchievableRate_le hN hR

/-! ### Single-letterization of the channel mutual information -/

omit [Fintype ι] in
/-- The **memoryless `n`-use channel is itself a channel**: `channelSeqProb q`, with input alphabet
`Fin n → ι` and output alphabet `Fin n → κ`, is nonnegative and normalized over its output strings
(`channelSeqProb_nonneg`, `sum_channelSeqProb`). -/
theorem isChannel_channelSeqProb {q : ι → κ → ℝ} (hN : IsChannel q) :
    IsChannel (channelSeqProb q (n := n)) where
  nonneg x y := channelSeqProb_nonneg hN x y
  row_sum x := sum_channelSeqProb hN x

omit [Fintype ι] in
/-- **Marginalizing the memoryless product law over every output coordinate except the `j`-th**
leaves the single-use conditional distribution `q(· | xⱼ)`: for a fixed input string `x`,
`∑_{y : yⱼ = b} ∏ᵢ q(yᵢ | xᵢ) = q(b | xⱼ)`. Restricting the `j`-th output to `{b}` and letting the
other `n − 1` coordinates range freely factors the sum over the product structure
(`Finset.prod_univ_sum`); each of the other coordinates sums to one (`row_sum`), leaving only the
`j`-th factor. -/
private theorem sum_channelSeqProb_pin [DecidableEq κ] {q : ι → κ → ℝ} (hN : IsChannel q)
    (x : Fin n → ι) (j : Fin n) (b : κ) :
    ∑ y : Fin n → κ, (if y j = b then ∏ i, q (x i) (y i) else 0) = q (x j) b := by
  rw [← Finset.sum_filter]
  have hpi : (Finset.univ.filter fun y : Fin n → κ => y j = b)
      = Fintype.piFinset fun i => if i = j then {b} else Finset.univ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hy i
      by_cases hij : i = j
      · subst hij; simpa using hy
      · simp [hij]
    · intro hy; simpa using hy j
  rw [hpi, ← Finset.prod_univ_sum (fun i => if i = j then ({b} : Finset κ) else Finset.univ)
      fun i (y : κ) => q (x i) y]
  refine (Finset.prod_eq_single j (fun i _ hij => ?_)
      (fun h => absurd (Finset.mem_univ j) h)).trans ?_
  · simp [hij, hN.row_sum (x i)]
  · simp

/-- **The `j`-th output marginal of the memoryless `n`-use channel is the single-use output of the
`j`-th input marginal.** For a channel `q` fed an input-string distribution `P`, the marginal of the
`j`-th output coordinate `Yⱼ` of `channelOutput (channelSeqProb q) P` is `channelOutput q Pⱼ`, where
`Pⱼ = law P (·ⱼ)` is the `j`-th input marginal:

`law (channelOutput (channelSeqProb q) P) (·ⱼ) = channelOutput q (law P (·ⱼ))`.

Both sides evaluate at `b` to `∑ₓ P(x) q(b | xⱼ)`: the right-hand side by the push-forward
expectation `sum_law_mul`, the left-hand side by summing the joint output law over every coordinate
but the `j`-th (`sum_channelSeqProb_pin`). This is the memoryless-marginal fact that turns the
subadditive output bound `H(Yⁿ) ≤ ∑ⱼ H(Yⱼ)` into a per-use capacity bound in
`channelMutualInfo_channelSeqProb_le`. -/
theorem law_proj_channelOutput_channelSeqProb [DecidableEq ι] [DecidableEq κ] {q : ι → κ → ℝ}
    (hN : IsChannel q) (P : (Fin n → ι) → ℝ) (j : Fin n) :
    law (channelOutput (channelSeqProb q) P) (fun y => y j)
      = channelOutput q (law P (fun x => x j)) := by
  funext b
  rw [channelOutput_apply, sum_law_mul P (fun x => x j) fun a => q a b]
  simp only [law, channelOutput_apply, channelSeqProb]
  have push : ∀ y : Fin n → κ,
      (if y j = b then ∑ x, P x * ∏ i, q (x i) (y i) else 0)
      = ∑ x, if y j = b then P x * ∏ i, q (x i) (y i) else 0 := by
    intro y; split_ifs <;> simp
  simp_rw [push]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have factor : ∀ y : Fin n → κ,
      (if y j = b then P x * ∏ i, q (x i) (y i) else 0)
      = P x * (if y j = b then ∏ i, q (x i) (y i) else 0) := by
    intro y; rw [mul_ite, mul_zero]
  simp_rw [factor, ← Finset.mul_sum]
  rw [sum_channelSeqProb_pin hN x j b]

/-- **Single-letterization of the channel mutual information** — the entropy input to the converse
half of Nielsen & Chuang Theorem 12.7. For a discrete memoryless channel `q` used `n` times, the
mutual information `H(Xⁿ : Yⁿ)` between any input-string distribution `P` and the induced output
string is at most `n` times the single-use information capacity:

`channelMutualInfo (channelSeqProb q) P ≤ n • channelCapacity q`.

Writing `H(Xⁿ : Yⁿ) = H(Yⁿ) − ∑ₓ P(x) H(Yⁿ | Xⁿ = x)` (`channelMutualInfo_eq`), the noise term
single-letterizes *exactly* — `H(Yⁿ | Xⁿ = x) = ∑ⱼ H(q(·|xⱼ))` (`entropy_pi_prod`), which averages
over `P` to `∑ⱼ ∑ₐ Pⱼ(a) H(q(·|a))` for the coordinate input marginals `Pⱼ = law P (·ⱼ)` — while
the output term is only *subadditive* — `H(Yⁿ) ≤ ∑ⱼ H(Yⱼ)` (`entropy_le_sum_entropy_proj`), the
`j`-th output marginal being the single-use output `channelOutput q Pⱼ` (`sum_channelSeqProb_pin`).
Combining coordinatewise gives `∑ⱼ channelMutualInfo q Pⱼ ≤ ∑ⱼ channelCapacity q = n • C`, each term
bounded by `le_channelCapacity` since every `Pⱼ` is an input distribution. This is the bound N&C's
converse composes with Fano's inequality to cap the operational capacity `C(N)`. -/
theorem channelMutualInfo_channelSeqProb_le [Nonempty κ] {q : ι → κ → ℝ} (hN : IsChannel q)
    {P : (Fin n → ι) → ℝ} (hP : P ∈ probSimplex (Fin n → ι)) :
    channelMutualInfo (channelSeqProb q) P ≤ n • channelCapacity q := by
  classical
  set Pmarg : Fin n → ι → ℝ := fun j => law P (fun x => x j) with hPmarg
  -- Each coordinate input marginal `Pⱼ = law P (·ⱼ)` is again an input distribution.
  have hsimplex : ∀ j, Pmarg j ∈ probSimplex ι := by
    intro j
    simp only [hPmarg]
    exact ⟨fun a => law_nonneg hP.1 _ a, by rw [sum_law]; exact hP.2⟩
  -- The `n`-use channel is a channel.
  have hN' : IsChannel (channelSeqProb q (n := n)) := isChannel_channelSeqProb hN
  -- Noise term single-letterizes: `H(Yⁿ | Xⁿ = x) = ∑ⱼ H(q(·|xⱼ))`, then average over `P`.
  have hnoise : ∑ x, P x * entropy (channelSeqProb q x)
      = ∑ j, ∑ a, Pmarg j a * entropy (q a) := by
    have hper : ∀ x : Fin n → ι, entropy (channelSeqProb q x) = ∑ j, entropy (q (x j)) := by
      intro x
      have hx : channelSeqProb q x = fun y : Fin n → κ => ∏ j, q (x j) (y j) := rfl
      rw [hx]; exact entropy_pi_prod (r := fun j => q (x j)) fun j => hN.row_sum (x j)
    calc ∑ x, P x * entropy (channelSeqProb q x)
        = ∑ x, ∑ j, P x * entropy (q (x j)) := by simp_rw [hper, Finset.mul_sum]
      _ = ∑ j, ∑ x, P x * entropy (q (x j)) := Finset.sum_comm
      _ = ∑ j, ∑ a, Pmarg j a * entropy (q a) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hPmarg]
          exact (sum_law_mul P (fun x => x j) fun a => entropy (q a)).symm
  -- Output term is subadditive, and each output marginal is the single-use output of `Pⱼ`
  -- (`law_proj_channelOutput_channelSeqProb`).
  have hout : entropy (channelOutput (channelSeqProb q) P)
      ≤ ∑ j, entropy (channelOutput q (Pmarg j)) :=
    (entropy_le_sum_entropy_proj (channelOutput_nonneg hN' hP.1) (sum_channelOutput hN' hP.2)).trans
      (le_of_eq (Finset.sum_congr rfl fun j _ => by
        rw [law_proj_channelOutput_channelSeqProb hN P j, hPmarg]))
  -- Combine the output subadditivity with the exact noise split, coordinatewise.
  rw [channelMutualInfo_eq (channelSeqProb q) fun x => sum_channelSeqProb hN x, hnoise]
  calc entropy (channelOutput (channelSeqProb q) P) - ∑ j, ∑ a, Pmarg j a * entropy (q a)
      ≤ (∑ j, entropy (channelOutput q (Pmarg j))) - ∑ j, ∑ a, Pmarg j a * entropy (q a) := by
        linarith [hout]
    _ = ∑ j, (entropy (channelOutput q (Pmarg j)) - ∑ a, Pmarg j a * entropy (q a)) := by
        rw [← Finset.sum_sub_distrib]
    _ = ∑ j, channelMutualInfo q (Pmarg j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [channelMutualInfo_eq q hN.row_sum]
    _ ≤ ∑ _ : Fin n, channelCapacity q :=
        Finset.sum_le_sum fun j _ => le_channelCapacity hN (hsimplex j)
    _ = n • channelCapacity q := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-! ### The joint law of message, codeword and output (converse setup)

The converse of Shannon's coding theorem studies, for a fixed block code, the joint distribution of
a **uniform message** `W`, its deterministic **codeword** `Xⁿ = Cₙ(W)`, and the resulting channel
**output** `Yⁿ`. This subsection builds that tripartite distribution `ChannelCode.jointLaw` and its
structural marginals — the first marginal is the uniform message law (so `H(W) = log M`), the
`(Xⁿ, Yⁿ)`-marginal is a channel joint law fed the codeword pushforward `ChannelCode.inputLaw`, and
`W → Xⁿ → Yⁿ` is a Markov chain — which the next converse step feeds to Fano's inequality, the
data-processing inequality, and the single-letterization bound above. -/

section ConverseJointLaw

variable [DecidableEq ι]

/-- The **codeword input distribution** of a block code: the law of the codeword `Xⁿ = Cₙ(W)` when
the message `W` is uniform over the `M` messages, i.e. the push-forward of the uniform distribution
on `Fin M` along the encoder,
`ChannelCode.inputLaw code x = (#{m | Cₙ(m) = x}) / M`. It is the input distribution fed to the
memoryless `n`-use channel `channelSeqProb q` when a uniform message is transmitted, so its channel
mutual information `H(Xⁿ : Yⁿ)` is controlled by the single-letterization bound
`channelMutualInfo_channelSeqProb_le`. -/
noncomputable def ChannelCode.inputLaw (code : ChannelCode ι κ n M) : (Fin n → ι) → ℝ :=
  law (fun _ : Fin M => (M : ℝ)⁻¹) code.encode

omit [Fintype κ] in
/-- The codeword input distribution lies in the input simplex: it is nonnegative, and — with at
least one message (`0 < M`) — sums to one (`sum_law` of the uniform message law). -/
theorem ChannelCode.inputLaw_mem_probSimplex (code : ChannelCode ι κ n M) (hM : 0 < M) :
    code.inputLaw ∈ probSimplex (Fin n → ι) := by
  refine ⟨fun x => law_nonneg (fun _ => by positivity) _ x, ?_⟩
  rw [ChannelCode.inputLaw, sum_law, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hM.ne')

/-- The **joint law of message, codeword and output** `(W, Xⁿ, Yⁿ)` for a block code, the
tripartite distribution to which the converse of Shannon's noisy channel coding theorem applies
Fano's inequality and the data-processing inequality. The message `W` is uniform over the `M`
messages, the codeword `Xⁿ = Cₙ(W)` is the deterministic encoding, and the output `Yⁿ` is produced
by `n` memoryless uses of the channel `q`:

`jointLaw q code (m, x, y) = M⁻¹ · (if x = Cₙ(m) then ∏ⱼ q(yⱼ | xⱼ) else 0)`.

The `n`-use output law `channelSeqProb q x y` sits on the diagonal `x = Cₙ(m)` — off it the pair
`(W, Xⁿ)` has no mass — reflecting that `Xⁿ` is a deterministic function of `W`. -/
noncomputable def ChannelCode.jointLaw (q : ι → κ → ℝ) (code : ChannelCode ι κ n M) :
    Fin M × (Fin n → ι) × (Fin n → κ) → ℝ :=
  fun t => (M : ℝ)⁻¹ * (if t.2.1 = code.encode t.1 then channelSeqProb q t.2.1 t.2.2 else 0)

omit [Fintype ι] [Fintype κ] in
@[simp] theorem ChannelCode.jointLaw_apply (q : ι → κ → ℝ) (code : ChannelCode ι κ n M)
    (m : Fin M) (x : Fin n → ι) (y : Fin n → κ) :
    code.jointLaw q (m, x, y)
      = (M : ℝ)⁻¹ * (if x = code.encode m then channelSeqProb q x y else 0) := rfl

omit [Fintype ι] in
/-- The joint law is nonnegative (a nonnegative weight `M⁻¹` times the nonnegative `n`-use output
law on the diagonal, `0` off it). -/
theorem ChannelCode.jointLaw_nonneg {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) : ∀ t, 0 ≤ code.jointLaw q t := by
  rintro ⟨m, x, y⟩
  rw [ChannelCode.jointLaw_apply]
  refine mul_nonneg (by positivity) ?_
  split_ifs
  · exact channelSeqProb_nonneg hN x y
  · exact le_refl 0

omit [Fintype ι] in
/-- The **`(W, Xⁿ)`-marginal** of the joint law: summing out the output `Yⁿ` leaves the uniform mass
`M⁻¹` on the diagonal `x = Cₙ(m)` (each codeword's `n`-use output law has total mass one,
`sum_channelSeqProb`) and `0` off it:
`marginalFstMid (jointLaw q code) (m, x) = M⁻¹ · [x = Cₙ(m)]`. -/
theorem ChannelCode.marginalFstMid_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) (m : Fin M) (x : Fin n → ι) :
    marginalFstMid (code.jointLaw q) (m, x)
      = (M : ℝ)⁻¹ * (if x = code.encode m then (1 : ℝ) else 0) := by
  rw [marginalFstMid_apply]
  simp_rw [ChannelCode.jointLaw_apply, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite_irrel, Finset.sum_const_zero, sum_channelSeqProb hN x]

/-- The second marginal `∑ₘ jointLaw q code (m, ·)` of the joint law over the message `W`, packaged
for the first-marginal and total-mass computations: it equals `M⁻¹` for every message `m`. -/
private theorem ChannelCode.sum_snd_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) (m : Fin M) :
    ∑ xy : (Fin n → ι) × (Fin n → κ), code.jointLaw q (m, xy) = (M : ℝ)⁻¹ := by
  rw [Fintype.sum_prod_type]
  simp_rw [← marginalFstMid_apply, ChannelCode.marginalFstMid_jointLaw hN, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq' Finset.univ (code.encode m) fun _ => (1 : ℝ)]
  simp

/-- The joint law is a probability distribution (given at least one message, `0 < M`): summing over
all `(W, Xⁿ, Yⁿ)` gives `∑ₘ M⁻¹ = 1`. -/
theorem ChannelCode.sum_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q) (code : ChannelCode ι κ n M)
    (hM : 0 < M) : ∑ t, code.jointLaw q t = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [ChannelCode.sum_snd_jointLaw hN]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hM.ne')

/-- The **first marginal is the uniform message law**: marginalizing the joint law over the codeword
and output leaves `W` uniform on the `M` messages,
`marginalFst (jointLaw q code) = fun _ => M⁻¹`. -/
theorem ChannelCode.marginalFst_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) : marginalFst (code.jointLaw q) = fun _ : Fin M => (M : ℝ)⁻¹ := by
  funext m
  rw [marginalFst_apply]
  exact ChannelCode.sum_snd_jointLaw hN code m

/-- The message entropy is `H(W) = log M`: the first marginal is uniform on `Fin M`
(`marginalFst_jointLaw`), whose entropy is `log |Fin M| = log M` (`entropy_uniform`). This is the
`H(W)` that the converse expands as `H(W | Yⁿ) + H(W : Yⁿ)`. -/
theorem ChannelCode.entropy_marginalFst_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) :
    entropy (marginalFst (code.jointLaw q)) = Real.log M := by
  rw [ChannelCode.marginalFst_jointLaw hN]
  simpa [Fintype.card_fin] using entropy_uniform (ι := Fin M)

omit [Fintype ι] [Fintype κ] in
/-- The **`(Xⁿ, Yⁿ)`-marginal is the channel joint law of the codeword pushforward**: marginalizing
the joint law over the message `W` leaves the input–output law of the memoryless `n`-use channel
`channelSeqProb q` fed the codeword input distribution `inputLaw`,
`marginalSnd (jointLaw q code) = channelJoint (channelSeqProb q) (inputLaw code)`. Hence
`H(Xⁿ : Yⁿ) = channelMutualInfo (channelSeqProb q) (inputLaw code)`, to which the
single-letterization bound applies. Pointwise, `∑ₘ M⁻¹ [x = Cₙ(m)] · ∏ⱼ q(yⱼ | xⱼ)` factors the
codeword-independent `∏ⱼ q(yⱼ | xⱼ)` out of the message sum, leaving `inputLaw x` times it. -/
theorem ChannelCode.marginalSnd_jointLaw {q : ι → κ → ℝ} (code : ChannelCode ι κ n M) :
    marginalSnd (code.jointLaw q) = channelJoint (channelSeqProb q) code.inputLaw := by
  funext xy
  obtain ⟨x, y⟩ := xy
  rw [marginalSnd_apply, channelJoint_apply, ChannelCode.inputLaw, law, mul_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ChannelCode.jointLaw_apply]
  by_cases h : code.encode m = x
  · rw [ite_eq_left h.symm, ite_eq_left h]; ring
  · rw [ite_eq_right fun he => h he.symm, ite_eq_right h]; ring

omit [Fintype ι] in
/-- The **middle codeword marginal is the codeword input law**: summing the joint law over the
message `W` and output `Yⁿ` leaves `inputLaw`, `marginalMid (jointLaw q code) = inputLaw code`. Used
to discharge the `p_Y(y)` factor of the Markov-chain identity. -/
theorem ChannelCode.marginalMid_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) : marginalMid (code.jointLaw q) = code.inputLaw := by
  funext x
  rw [marginalMid, ChannelCode.marginalSnd_jointLaw, marginalFst_apply]
  simp_rw [channelJoint_apply, ← Finset.mul_sum, sum_channelSeqProb hN x, mul_one]

omit [Fintype ι] in
/-- **`W → Xⁿ → Yⁿ` is a Markov chain**: the message, its codeword and the channel output form a
Markov chain, because the codeword `Xⁿ = Cₙ(W)` is a deterministic function of `W` and the output
`Yⁿ` depends on `W` only through `Xⁿ`. Concretely the conditional-independence identity
`jointLaw (m, x, y) · marginalMid (x) = marginalFstMid (m, x) · marginalSnd (x, y)` holds pointwise:
both sides are `M⁻¹ · [x = Cₙ(m)] · inputLaw x · ∏ⱼ q(yⱼ | xⱼ)`. This is the hypothesis the
data-processing inequality needs to bound `H(W : Yⁿ) ≤ H(Xⁿ : Yⁿ)`. -/
theorem ChannelCode.isMarkovChain_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) : IsMarkovChain (code.jointLaw q) := by
  intro m x y
  rw [ChannelCode.marginalMid_jointLaw hN, ChannelCode.marginalFstMid_jointLaw hN,
    ChannelCode.marginalSnd_jointLaw, ChannelCode.jointLaw_apply, channelJoint_apply]
  by_cases h : x = code.encode m
  · simp only [ite_eq_left h]; ring
  · simp only [ite_eq_right h]; ring

/-- **The per-`n` converse inequality of Shannon's noisy channel coding theorem.** For a block code
with a uniform message `W` over `M` messages, deterministic codeword `Xⁿ = Cₙ(W)`, and channel
output `Yⁿ` (the joint law `jointLaw`), the average decoding error `P̄ₑ` obeys

`(1 − P̄ₑ) · log M ≤ log 2 + n · max_{p(x)} H(X : Y)`,

where `P̄ₑ = fanoErrorProb (marginalFstLast (jointLaw q code)) Dₙ` is the probability that the
decoder's guess `Dₙ(Yⁿ)` differs from the true message. This is the quantitative core of the
converse: it forces the rate to obey `R ≲ C` once the error `P̄ₑ → 0` (developed in the limit step).

The proof assembles three ingredients on the tripartite law `(W, Xⁿ, Yⁿ)`:
* `H(W) = log M` (`entropy_marginalFst_jointLaw`), expanded as `H(W) = H(W | Yⁿ) + H(W : Yⁿ)`;
* **Fano's inequality** (`condEntropy_le_binEntropy_add_mul_log`) on the `(W, Yⁿ)`-marginal with the
  decoder as guess: `H(W | Yⁿ) ≤ binEntropy P̄ₑ + P̄ₑ · log (M − 1) ≤ log 2 + P̄ₑ · log M`, using
  `binEntropy P̄ₑ ≤ log 2` (`binEntropy_le_log_two`) and `log (M − 1) ≤ log M`;
* the **data-processing inequality** `mutualInfo_marginalFstLast_le_marginalSnd`, applied to the
  Markov chain `W → Xⁿ → Yⁿ` (`isMarkovChain_jointLaw`) — its last-vs-second-marginal form, which
  internalises the outer reversal — giving
  `H(W : Yⁿ) ≤ H(Xⁿ : Yⁿ) = channelMutualInfo (channelSeqProb q) (inputLaw code)`
  (`marginalSnd_jointLaw`), then bounded by `n · channelCapacity q` via the single-letterization
  bound `channelMutualInfo_channelSeqProb_le`.

Rearranging `log M = H(W : Yⁿ) + H(W | Yⁿ) ≤ n · C + log 2 + P̄ₑ · log M` gives the claim. Entropy
is in nats; the bound is base-independent. -/
theorem ChannelCode.one_sub_fanoErrorProb_mul_log_le [Nonempty κ] {q : ι → κ → ℝ}
    (hN : IsChannel q) (code : ChannelCode ι κ n M) (hM : 0 < M) :
    (1 - fanoErrorProb (marginalFstLast (code.jointLaw q)) code.decode) * Real.log M
      ≤ Real.log 2 + n • channelCapacity q := by
  classical
  set J := code.jointLaw q with hJ
  set Pe := fanoErrorProb (marginalFstLast J) code.decode with hPe
  have hJnonneg : ∀ t, 0 ≤ J t := code.jointLaw_nonneg hN
  have hJsum : ∑ t, J t = 1 := code.sum_jointLaw hN hM
  -- The `(W, Yⁿ)`-marginal `marginalFstLast J` is a probability distribution.
  have hWY_nonneg : ∀ w, 0 ≤ marginalFstLast J w := by
    rintro ⟨m, y⟩; rw [marginalFstLast_apply]
    exact Finset.sum_nonneg fun x _ => hJnonneg _
  have hWY_sum : ∑ w, marginalFstLast J w = 1 := by
    rw [← sum_marginalFst (marginalFstLast J), marginalFst_marginalFstLast, sum_marginalFst]
    exact hJsum
  -- `H(W) = log M` via the uniform first marginal.
  have hlogM : entropy (marginalFst (marginalFstLast J)) = Real.log M := by
    rw [marginalFst_marginalFstLast, hJ]; exact code.entropy_marginalFst_jointLaw hN
  -- Fano's inequality: `H(W | Yⁿ) ≤ binEntropy P̄ₑ + P̄ₑ · log (M − 1)`.
  have hFano : condEntropy (marginalFstLast J)
      ≤ binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
    have h := condEntropy_le_binEntropy_add_mul_log hWY_nonneg hWY_sum code.decode
    simpa only [Fintype.card_fin, ← hPe] using h
  have hPe_nonneg : 0 ≤ Pe := fanoErrorProb_nonneg hWY_nonneg hWY_sum code.decode
  -- `log (M − 1) ≤ log M`.
  have hlogmono : Real.log ((M : ℝ) - 1) ≤ Real.log M := by
    rcases Nat.lt_or_ge M 2 with hlt | hge
    · have hM1 : M = 1 := by omega
      subst hM1; simp
    · have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hge
      exact Real.log_le_log (by linarith) (by linarith)
  -- Mutual information as `H(W) − H(W | Yⁿ)`.
  have hmi_eq : mutualInfo (marginalFstLast J)
      = entropy (marginalFst (marginalFstLast J)) - condEntropy (marginalFstLast J) := by
    rw [mutualInfo_eq, condEntropy_eq]; ring
  -- Data-processing inequality on the Markov chain `W → Xⁿ → Yⁿ` (`isMarkovChain_jointLaw`); the
  -- second-marginal form internalises the outer reversal, giving `H(W : Yⁿ) ≤ H(Xⁿ : Yⁿ)`.
  have hDPI : mutualInfo (marginalFstLast J) ≤ mutualInfo (marginalSnd J) :=
    mutualInfo_marginalFstLast_le_marginalSnd hJnonneg hJsum (code.isMarkovChain_jointLaw hN)
  -- Single-letterization: `H(Xⁿ : Yⁿ) ≤ n · channelCapacity q`.
  have hSL : mutualInfo (marginalSnd J) ≤ n • channelCapacity q := by
    rw [hJ, code.marginalSnd_jointLaw]
    exact channelMutualInfo_channelSeqProb_le hN (code.inputLaw_mem_probSimplex hM)
  -- Assemble.
  have hbin : binEntropy Pe ≤ Real.log 2 := binEntropy_le_log_two
  have hlogmul : Pe * Real.log ((M : ℝ) - 1) ≤ Pe * Real.log M :=
    mul_le_mul_of_nonneg_left hlogmono hPe_nonneg
  have hexp : (1 - Pe) * Real.log M = Real.log M - Pe * Real.log M := by ring
  rw [hexp]
  linarith [hmi_eq, hlogM, hFano, hDPI, hSL, hbin, hlogmul]

/-! ### The average error probability and the converse of the coding theorem -/

omit [Fintype κ] in
/-- The **`(W, Yⁿ)`-marginal** of the code joint law: summing out the codeword `Xⁿ` from `jointLaw`
leaves, on message `w` and output string `y`, the uniform weight `M⁻¹` times the `n`-use output law
of the codeword `Cₙ(w)`:
`marginalFstLast (jointLaw q code) (w, y) = M⁻¹ · channelSeqProb q (Cₙ w) y`. -/
theorem ChannelCode.marginalFstLast_jointLaw {q : ι → κ → ℝ} (code : ChannelCode ι κ n M)
    (m : Fin M) (y : Fin n → κ) :
    marginalFstLast (code.jointLaw q) (m, y) = (M : ℝ)⁻¹ * channelSeqProb q (code.encode m) y := by
  rw [marginalFstLast_apply]
  simp only [ChannelCode.jointLaw_apply, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq' Finset.univ (code.encode m) (fun x => channelSeqProb q x y)]
  simp

/-- **The average probability of error equals the Fano error probability of the code joint law.**
For a block code with `0 < M` messages and its joint law `jointLaw` (uniform message `W`, codeword
`Xⁿ = Cₙ(W)`, output `Yⁿ`), the Fano error probability of the `(W, Yⁿ)`-marginal under the decoder
`Dₙ` — the `P̄ₑ` of the per-`n` converse inequality `one_sub_fanoErrorProb_mul_log_le` — is exactly
the *average* of the conditional block-error probabilities over the `M` messages (Nielsen & Chuang,
p. 552, the average probability of error `p̄(Cₙ, Dₙ) = M⁻¹ ∑ₘ p(Dₙ(Y) ≠ m | Cₙ(m))`):
`fanoErrorProb (marginalFstLast (jointLaw q code)) Dₙ = (∑ₘ condErrorProb q m) / M`.

The Fano term expands, via the `(W, Yⁿ)`-marginal (`marginalFstLast_jointLaw`), to
`1 − M⁻¹ ∑_y channelSeqProb q (Cₙ(Dₙ y)) y`; each conditional error probability is `1 −` the
correct-decoding probability of its message (`sum_channelSeqProb`), and the correct-decoding
probabilities telescope over the decoder's fibers (`Finset.sum_fiberwise`) to the same
`∑_y channelSeqProb q (Cₙ(Dₙ y)) y`. -/
theorem ChannelCode.fanoErrorProb_marginalFstLast_jointLaw {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) (hM : 0 < M) :
    fanoErrorProb (marginalFstLast (code.jointLaw q)) code.decode
      = (∑ m, code.condErrorProb q m) / M := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  -- The Fano error term expands via the (W, Yⁿ)-marginal.
  have hfano : fanoErrorProb (marginalFstLast (code.jointLaw q)) code.decode
      = 1 - (M : ℝ)⁻¹ * ∑ y : Fin n → κ, channelSeqProb q (code.encode (code.decode y)) y := by
    unfold fanoErrorProb
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => code.marginalFstLast_jointLaw (code.decode y) y
  -- Each conditional error probability is `1 −` the correct-decoding probability of its message.
  have hcond : ∀ m, code.condErrorProb q m
      = 1 - ∑ y ∈ Finset.univ with code.decode y = m, channelSeqProb q (code.encode m) y := by
    intro m
    rw [ChannelCode.condErrorProb, eq_sub_iff_add_eq, add_comm,
      ← sum_channelSeqProb hN (code.encode m)]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => code.decode y = m) _
  -- The total correct-decoding probability telescopes over the decoder's fibers.
  have hsumcorr : ∑ m, ∑ y ∈ Finset.univ with code.decode y = m,
        channelSeqProb q (code.encode m) y
      = ∑ y : Fin n → κ, channelSeqProb q (code.encode (code.decode y)) y := by
    rw [← Finset.sum_fiberwise Finset.univ code.decode
      (fun y => channelSeqProb q (code.encode (code.decode y)) y)]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.mem_filter] at hy
    rw [hy.2]
  rw [hfano, Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => hcond m), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsumcorr]
  field_simp

/-- The Fano error probability of the code joint law — the average probability of error — is
nonnegative (an average of nonnegative conditional error probabilities). -/
theorem ChannelCode.fanoErrorProb_marginalFstLast_jointLaw_nonneg {q : ι → κ → ℝ} (hN : IsChannel q)
    (code : ChannelCode ι κ n M) (hM : 0 < M) :
    0 ≤ fanoErrorProb (marginalFstLast (code.jointLaw q)) code.decode := by
  rw [ChannelCode.fanoErrorProb_marginalFstLast_jointLaw hN code hM]
  exact div_nonneg (Finset.sum_nonneg fun m _ => code.condErrorProb_nonneg hN m) (by positivity)

/-- The **average probability of error is at most the block (maximum) error probability**: an
average of the conditional error probabilities cannot exceed their maximum. This is the bridge
turning the per-`n` converse inequality's `P̄ₑ` — the Fano error of the joint law — into a quantity
that vanishes whenever the block error probability does (`maxErrorProb → 0`). -/
theorem ChannelCode.fanoErrorProb_marginalFstLast_jointLaw_le_maxErrorProb {q : ι → κ → ℝ}
    (hN : IsChannel q) (code : ChannelCode ι κ n M) (hM : 0 < M) :
    fanoErrorProb (marginalFstLast (code.jointLaw q)) code.decode ≤ code.maxErrorProb q := by
  rw [ChannelCode.fanoErrorProb_marginalFstLast_jointLaw hN code hM,
    div_le_iff₀ (by exact_mod_cast hM)]
  calc ∑ m, code.condErrorProb q m
      ≤ ∑ _m : Fin M, code.maxErrorProb q :=
        Finset.sum_le_sum fun m _ => code.condErrorProb_le_maxErrorProb q m
    _ = code.maxErrorProb q * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

end ConverseJointLaw

/-- **The converse of Shannon's noisy channel coding theorem** (Nielsen & Chuang, Theorem 12.7,
eq. (12.67), one direction). The operational capacity is at most the information capacity: no rate
above `max_{p(x)} H(X : Y)` — in bits, `channelCapacity q / log 2` — is achievable, so
`channelOpCapacity q ≤ channelCapacity q / log 2`.

For an achievable rate `R` there is a family of `M(n) = ⌈2 ^ (n R)⌉`-message block codes whose block
error probability tends to `0`. Feeding the per-`n` converse inequality
`(1 − P̄ₑ) · log M ≤ log 2 + n · C` (`one_sub_fanoErrorProb_mul_log_le`) the message-count lower
bound `log M(n) ≥ n R log 2` (from `M(n) ≥ 2 ^ (n R)`, `Nat.le_ceil`) and the vanishing of the
average error `P̄ₑ(n) ≤ maxErrorProb → 0` (`fanoErrorProb_marginalFstLast_jointLaw_le_maxErrorProb`,
`squeeze_zero`) gives `n · (1 − P̄ₑ) · R log 2 ≤ log 2 + n · C`; dividing by `n` and letting
`n → ∞` (so `P̄ₑ → 0` and `log 2 / n → 0`, `le_of_tendsto_of_tendsto`) yields `R log 2 ≤ C`, i.e.
`R ≤ C / log 2`. As every achievable rate obeys this, so does their supremum `channelOpCapacity q`
(`csSup_le`).

Entropy is in nats; the operational rate `R` and the bound are in bits, hence the `/ log 2`. N&C
defers the matching achievability direction `channelCapacity q / log 2 ≤ channelOpCapacity q`
(random coding and the theorem of typical sequences) to the quantum HSW theorem (Theorem 12.8) of
the next section. -/
theorem channelOpCapacity_le_channelCapacity_div [Nonempty ι] [Nonempty κ] {q : ι → κ → ℝ}
    (hN : IsChannel q) :
    channelOpCapacity q ≤ channelCapacity q / Real.log 2 := by
  classical
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine csSup_le ⟨0, isAchievableRate_zero q⟩ ?_
  rintro R ⟨code, hcode⟩
  have hMpos : ∀ n : ℕ, 0 < ⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ :=
    fun n => Nat.ceil_pos.mpr (Real.exp_pos _)
  -- Abstract the average error `P̄ₑ(n)`: `≤ 1`, tends to `0`, and obeys the per-`n` bound.
  obtain ⟨Pe, hPe_le_one, hPe_tendsto, hpern⟩ :
      ∃ Pe : ℕ → ℝ, (∀ n, Pe n ≤ 1) ∧ Tendsto Pe atTop (𝓝 0) ∧
        (∀ n : ℕ, (1 - Pe n) * Real.log (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ)
          ≤ Real.log 2 + (n : ℝ) * channelCapacity q) := by
    refine ⟨fun n => fanoErrorProb (marginalFstLast ((code n).jointLaw q)) (code n).decode,
      fun n => le_trans
        ((code n).fanoErrorProb_marginalFstLast_jointLaw_le_maxErrorProb hN (hMpos n))
        ((code n).maxErrorProb_le_one hN),
      squeeze_zero
        (fun n => (code n).fanoErrorProb_marginalFstLast_jointLaw_nonneg hN (hMpos n))
        (fun n => (code n).fanoErrorProb_marginalFstLast_jointLaw_le_maxErrorProb hN (hMpos n))
        hcode, fun n => ?_⟩
    have h := (code n).one_sub_fanoErrorProb_mul_log_le hN (hMpos n)
    rwa [nsmul_eq_mul] at h
  -- `log M(n) ≥ n R log 2`.
  have hlogM : ∀ n : ℕ, (n : ℝ) * R * Real.log 2
      ≤ Real.log (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) := by
    intro n
    calc (n : ℝ) * R * Real.log 2
        = Real.log (Real.exp ((n : ℝ) * R * Real.log 2)) := (Real.log_exp _).symm
      _ ≤ Real.log (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) :=
          Real.log_le_log (Real.exp_pos _) (Nat.le_ceil _)
  -- Combine into `n · ((1 − P̄ₑ) · R log 2) ≤ log 2 + n · C`.
  have hstep : ∀ n : ℕ, (n : ℝ) * ((1 - Pe n) * (R * Real.log 2))
      ≤ Real.log 2 + (n : ℝ) * channelCapacity q := by
    intro n
    have hmul : (1 - Pe n) * ((n : ℝ) * R * Real.log 2)
        ≤ (1 - Pe n) * Real.log (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) :=
      mul_le_mul_of_nonneg_left (hlogM n) (by linarith [hPe_le_one n])
    calc (n : ℝ) * ((1 - Pe n) * (R * Real.log 2))
        = (1 - Pe n) * ((n : ℝ) * R * Real.log 2) := by ring
      _ ≤ (1 - Pe n) * Real.log (⌈Real.exp ((n : ℝ) * R * Real.log 2)⌉₊ : ℝ) := hmul
      _ ≤ Real.log 2 + (n : ℝ) * channelCapacity q := hpern n
  -- Divide by `n` (for `n ≥ 1`).
  have hab : ∀ n : ℕ, 1 ≤ n →
      (1 - Pe n) * (R * Real.log 2) ≤ Real.log 2 / (n : ℝ) + channelCapacity q := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    rw [← sub_nonneg, show Real.log 2 / (n : ℝ) + channelCapacity q - (1 - Pe n) * (R * Real.log 2)
        = (Real.log 2 + (n : ℝ) * channelCapacity q
            - (n : ℝ) * ((1 - Pe n) * (R * Real.log 2))) / (n : ℝ) by field_simp]
    exact div_nonneg (by linarith [hstep n]) hnpos.le
  -- Take the `atTop` limit.
  have ha : Tendsto (fun n => (1 - Pe n) * (R * Real.log 2)) atTop (𝓝 (R * Real.log 2)) := by
    have h1 : Tendsto (fun n => 1 - Pe n) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hPe_tendsto
    simpa using h1.mul_const (R * Real.log 2)
  have hb : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ) + channelCapacity q) atTop
      (𝓝 (channelCapacity q)) := by
    have h0 : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.const_div_atTop (Real.log 2)
    simpa using h0.add_const (channelCapacity q)
  have hRlog : R * Real.log 2 ≤ channelCapacity q :=
    le_of_tendsto_of_tendsto ha hb (eventually_atTop.mpr ⟨1, fun n hn => hab n hn⟩)
  rw [le_div_iff₀ hL]
  exact hRlog

end OperationalCapacity

end Real
