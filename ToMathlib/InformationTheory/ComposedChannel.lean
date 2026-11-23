/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.NoisyChannel
public import ToMathlib.InformationTheory.BinaryChannels
public import ToMathlib.Analysis.SpecialFunctions.DataProcessingInequality

/-!
# Series composition of discrete memoryless channels and its capacity

For channels `q₁ : ι → κ → ℝ` and `q₂ : κ → μ → ℝ`, feeding the output of `q₁` into `q₂` gives the
**series composition** `N₂ ∘ N₁`, the channel `Real.channelComp q₁ q₂ : ι → μ → ℝ` with conditional
law `p(z | x) = ∑_y q₁(y | x) q₂(z | y)` (matrix product of the two transition matrices). This file
proves the capacity bound of **Nielsen & Chuang, Exercise 12.10** (p. 553):

`Real.channelCapacity_channelComp_le_min` :
  `C(N₂ ∘ N₁) ≤ min (C(N₁)) (C(N₂))`.

The bound is the classical **data processing inequality**: for any input distribution `p`, the
random variables `X → Y → Z` (input, `q₁`-output, `q₂`-output) form a Markov chain, so
`H(X : Z) ≤ H(X : Y)` and `H(X : Z) ≤ H(Y : Z)`. Maximizing over `p`, the first gives
`C(N₂ ∘ N₁) ≤ C(N₁)` and the second `C(N₂ ∘ N₁) ≤ C(N₂)`.

Both halves are read off the tripartite joint law `Real.channelTriple p q₁ q₂ (x, y, z) =
p(x) q₁(y | x) q₂(z | y)`, whose `(X, Z)`-marginal (`marginalFstLast`) is the input–output law
of the composite `channelComp q₁ q₂`, and whose `(X, Y)`-marginal (`marginalFstMid`) is the
input–output law of `q₁`; its Markov-chain property holds by direct computation. The two bounds are
the two forms of the data processing inequality applied to it:
`Real.mutualInfo_marginalFstLast_le_marginalFstMid` (`H(X : Z) ≤ H(X : Y)`) and
`Real.mutualInfo_marginalFstLast_le_marginalSnd` (`H(X : Z) ≤ H(Y : Z)`), the latter identifying
`H(Y : Z)` with `channelMutualInfo q₂ (channelOutput q₁ p)`.

## Main declarations

* `Real.channelComp` — the series composition `q₁; q₂` of two channels.
* `Real.isChannel_channelComp` — the composition is again a discrete memoryless channel.
* `Real.channelTriple` — the tripartite joint law `p(x) q₁(y | x) q₂(z | y)`.
* `Real.channelMutualInfo_channelComp_le_left` / `..._le_right` — the per-input-distribution
  bounds `H(X : Z) ≤ H(X : Y)` and `H(X : Z) ≤ H(Y : Z)`.
* `Real.channelCapacity_channelComp_le_min` — **Exercise 12.10 (bound)**:
  `C(N₂ ∘ N₁) ≤ min (C(N₁)) (C(N₂))`.
* `Real.channelComp_bscChannel_self` — two identical binary symmetric channels in series compose to
  the binary symmetric channel with compounded crossover `2 p (1 - p)`.
* `Real.channelCapacity_channelComp_bscChannel_lt_min` — **Exercise 12.10 (strict example)**: for
  `0 < p < 1/2` the bound is *strict* for `N₁ = N₂ = bscChannel p`.

The capacities are the information capacities `max_{p(x)} H(X : Y)` of `NoisyChannel`, measured in
*nats* (natural log) as elsewhere in the library; the bound is base-independent.
-/

@[expose] public section

namespace Real

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-! ### The composed channel -/

/-- The **series composition** `N₂ ∘ N₁` of two discrete memoryless channels `q₁ : ι → κ → ℝ` and
`q₂ : κ → μ → ℝ`: feeding the output of `q₁` into `q₂` gives the conditional law
`p(z | x) = ∑_y q₁(y | x) q₂(z | y)` (the matrix product of the transition matrices). -/
noncomputable def channelComp (q₁ : ι → κ → ℝ) (q₂ : κ → μ → ℝ) : ι → μ → ℝ :=
  fun x z => ∑ y, q₁ x y * q₂ y z

omit [Fintype ι] [Fintype μ] in
@[simp] theorem channelComp_apply (q₁ : ι → κ → ℝ) (q₂ : κ → μ → ℝ) (x : ι) (z : μ) :
    channelComp q₁ q₂ x z = ∑ y, q₁ x y * q₂ y z := rfl

omit [Fintype ι] in
/-- The series composition of two channels is again a discrete memoryless channel. -/
theorem isChannel_channelComp {q₁ : ι → κ → ℝ} {q₂ : κ → μ → ℝ}
    (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) : IsChannel (channelComp q₁ q₂) where
  nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (h₁.nonneg x y) (h₂.nonneg y z)
  row_sum x := by
    simp only [channelComp_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h₂.row_sum, mul_one]
    exact h₁.row_sum x

/-! ### The tripartite input–output joint law and its marginals -/

/-- The **tripartite joint law** `p(x, y, z) = p(x) q₁(y | x) q₂(z | y)` of the input `X`, the
intermediate output `Y` of `q₁`, and the final output `Z` of `q₂`, for input distribution `p`. -/
noncomputable def channelTriple (p : ι → ℝ) (q₁ : ι → κ → ℝ) (q₂ : κ → μ → ℝ) : ι × κ × μ → ℝ :=
  fun t => p t.1 * q₁ t.1 t.2.1 * q₂ t.2.1 t.2.2

omit [Fintype ι] [Fintype κ] [Fintype μ] in
@[simp] theorem channelTriple_apply (p : ι → ℝ) (q₁ : ι → κ → ℝ) (q₂ : κ → μ → ℝ)
    (x : ι) (y : κ) (z : μ) :
    channelTriple p q₁ q₂ (x, y, z) = p x * q₁ x y * q₂ y z := rfl

omit [Fintype ι] [Fintype κ] in
/-- The `(X, Y)`-marginal of the tripartite law is the input–output law of `q₁`:
`∑_z p(x) q₁(y | x) q₂(z | y) = p(x) q₁(y | x)`. -/
theorem marginalFstMid_channelTriple {q₂ : κ → μ → ℝ} (h₂ : IsChannel q₂)
    (p : ι → ℝ) (q₁ : ι → κ → ℝ) :
    marginalFstMid (channelTriple p q₁ q₂) = channelJoint q₁ p := by
  funext t
  obtain ⟨x, y⟩ := t
  simp only [marginalFstMid_apply, channelJoint_apply, channelTriple_apply]
  rw [← Finset.mul_sum, h₂.row_sum, mul_one]

omit [Fintype ι] [Fintype μ] in
/-- The `(X, Z)`-marginal of the tripartite law is the input–output law of the composite channel:
`∑_y p(x) q₁(y | x) q₂(z | y) = p(x) (channelComp q₁ q₂)(z | x)`. -/
theorem marginalFstLast_channelTriple (p : ι → ℝ) (q₁ : ι → κ → ℝ) (q₂ : κ → μ → ℝ) :
    marginalFstLast (channelTriple p q₁ q₂) = channelJoint (channelComp q₁ q₂) p := by
  funext t
  obtain ⟨x, z⟩ := t
  simp only [marginalFstLast_apply, channelJoint_apply, channelComp_apply, channelTriple_apply,
    Finset.mul_sum, mul_assoc]

omit [Fintype κ] [Fintype μ] in
/-- The `(Y, Z)`-marginal of the tripartite law is the input–output law of `q₂` fed the induced
output distribution of `q₁`: `∑_x p(x) q₁(y | x) q₂(z | y) = (channelOutput q₁ p)(y) q₂(z | y)`. -/
theorem marginalSnd_channelTriple (p : ι → ℝ) (q₁ : ι → κ → ℝ) (q₂ : κ → μ → ℝ) :
    marginalSnd (channelTriple p q₁ q₂) = channelJoint q₂ (channelOutput q₁ p) := by
  funext t
  obtain ⟨y, z⟩ := t
  simp only [marginalSnd_apply, channelJoint_apply, channelOutput_apply, channelTriple_apply]
  rw [Finset.sum_mul]

omit [Fintype κ] in
/-- The middle `Y`-marginal of the tripartite law is the induced output distribution of `q₁`:
`∑_{x,z} p(x) q₁(y | x) q₂(z | y) = (channelOutput q₁ p)(y)`. -/
theorem marginalMid_channelTriple {q₂ : κ → μ → ℝ} (h₂ : IsChannel q₂)
    (p : ι → ℝ) (q₁ : ι → κ → ℝ) :
    marginalMid (channelTriple p q₁ q₂) = channelOutput q₁ p := by
  funext y
  rw [marginalMid_apply]
  simp only [marginalSnd_channelTriple, channelJoint_apply]
  rw [← Finset.mul_sum, h₂.row_sum, mul_one]

omit [Fintype κ] in
/-- The input `X`, intermediate output `Y` and final output `Z` form a **Markov chain**: `Z` depends
on `X` only through `Y`. Division-free, `p(x, y, z) · p_Y(y) = p_{XY}(x, y) · p_{YZ}(y, z)`. -/
theorem isMarkovChain_channelTriple {q₂ : κ → μ → ℝ} (h₂ : IsChannel q₂)
    (p : ι → ℝ) (q₁ : ι → κ → ℝ) :
    IsMarkovChain (channelTriple p q₁ q₂) := by
  intro x y z
  simp only [marginalMid_channelTriple h₂, marginalFstMid_channelTriple h₂,
    marginalSnd_channelTriple, channelTriple_apply, channelJoint_apply]
  ring

omit [Fintype ι] in
/-- The tripartite law is nonnegative when the input distribution is. -/
theorem channelTriple_nonneg {q₁ : ι → κ → ℝ} {q₂ : κ → μ → ℝ}
    (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) {p : ι → ℝ} (hp : ∀ x, 0 ≤ p x) :
    ∀ t, 0 ≤ channelTriple p q₁ q₂ t := by
  rintro ⟨x, y, z⟩
  rw [channelTriple_apply]
  exact mul_nonneg (mul_nonneg (hp x) (h₁.nonneg x y)) (h₂.nonneg y z)

/-- The tripartite law is normalized when the input distribution is. -/
theorem channelTriple_sum {q₁ : ι → κ → ℝ} {q₂ : κ → μ → ℝ}
    (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) {p : ι → ℝ} (hp : ∑ x, p x = 1) :
    ∑ t, channelTriple p q₁ q₂ t = 1 := by
  simp only [Fintype.sum_prod_type, channelTriple_apply, ← Finset.mul_sum, h₂.row_sum, mul_one,
    h₁.row_sum]
  exact hp

/-! ### The per-input-distribution data-processing bounds -/

/-- **Data processing inequality, first form** `H(X : Z) ≤ H(X : Y)`: for any input distribution
`p ∈ probSimplex ι`, the mutual information of the composite channel is at most that of the first
channel. -/
theorem channelMutualInfo_channelComp_le_left {q₁ : ι → κ → ℝ} {q₂ : κ → μ → ℝ}
    (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) {p : ι → ℝ} (hp : p ∈ probSimplex ι) :
    channelMutualInfo (channelComp q₁ q₂) p ≤ channelMutualInfo q₁ p := by
  have key := mutualInfo_marginalFstLast_le_marginalFstMid
    (channelTriple_nonneg h₁ h₂ hp.1) (channelTriple_sum h₁ h₂ hp.2)
    (isMarkovChain_channelTriple h₂ p q₁)
  rwa [marginalFstLast_channelTriple, marginalFstMid_channelTriple h₂] at key

/-- **Data processing inequality, second form** `H(X : Z) ≤ H(Y : Z)`: for any input distribution
`p ∈ probSimplex ι`, the mutual information of the composite channel is at most that of the second
channel fed the induced output distribution `channelOutput q₁ p`. Mirrors
`channelMutualInfo_channelComp_le_left`, using the general second-form data processing inequality
`mutualInfo_marginalFstLast_le_marginalSnd` on the tripartite law. -/
theorem channelMutualInfo_channelComp_le_right {q₁ : ι → κ → ℝ} {q₂ : κ → μ → ℝ}
    (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) {p : ι → ℝ} (hp : p ∈ probSimplex ι) :
    channelMutualInfo (channelComp q₁ q₂) p ≤ channelMutualInfo q₂ (channelOutput q₁ p) := by
  have key := mutualInfo_marginalFstLast_le_marginalSnd
    (channelTriple_nonneg h₁ h₂ hp.1) (channelTriple_sum h₁ h₂ hp.2)
    (isMarkovChain_channelTriple h₂ p q₁)
  rwa [marginalFstLast_channelTriple, marginalSnd_channelTriple] at key

/-! ### The capacity bound (Exercise 12.10) -/

/-- **Nielsen & Chuang, Exercise 12.10.** The capacity of the series composition `N₂ ∘ N₁` of two
channels is at most the minimum of the two individual capacities,
`C(N₂ ∘ N₁) ≤ min (C(N₁)) (C(N₂))`. This is the classical data processing inequality at the level of
capacities: composing channels can only lose information. -/
theorem channelCapacity_channelComp_le_min [Nonempty ι] [Nonempty κ] [Nonempty μ]
    {q₁ : ι → κ → ℝ} {q₂ : κ → μ → ℝ} (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) :
    channelCapacity (channelComp q₁ q₂) ≤ min (channelCapacity q₁) (channelCapacity q₂) := by
  refine le_min (channelCapacity_le fun p hp => ?_) (channelCapacity_le fun p hp => ?_)
  · exact (channelMutualInfo_channelComp_le_left h₁ h₂ hp).trans (le_channelCapacity h₁ hp)
  · exact (channelMutualInfo_channelComp_le_right h₁ h₂ hp).trans
      (le_channelCapacity h₂ (channelOutput_mem_probSimplex h₁ hp))

/-! ### A strict example (Exercise 12.10, second part)

Nielsen & Chuang also ask for an example where the capacity bound
`channelCapacity_channelComp_le_min` is *strict*. Two identical binary symmetric channels in series
provide one: `N₁ = N₂ = bscChannel p` composes to the binary symmetric channel with the *compounded*
crossover probability `2 p (1 - p)` (`channelComp_bscChannel_self`), and for a nondegenerate
crossover `0 < p < 1/2` the compounded crossover is strictly larger while staying in the noise
regime — `p < 2 p (1 - p) ≤ 1/2` — so, by the strict monotonicity of the binary entropy on
`[0, 1/2]`, the composite capacity `log 2 - H(2 p (1 - p))` is strictly below the common
single-channel capacity `log 2 - H(p)`. -/

/-- **Two identical binary symmetric channels in series form a binary symmetric channel with the
compounded crossover probability** `2 p (1 - p)`: `N₂ ∘ N₁ = bscChannel (2 p (1 - p))` when
`N₁ = N₂ = bscChannel p`. The composite flips a bit exactly when exactly one of the two uses flips
it, an event of probability `p (1 - p) + (1 - p) p = 2 p (1 - p)`; equivalently the matrix square of
`[[1 - p, p], [p, 1 - p]]` is `[[1 - 2p(1-p), 2p(1-p)], [2p(1-p), 1 - 2p(1-p)]]`. -/
theorem channelComp_bscChannel_self (p : ℝ) :
    channelComp (bscChannel p) (bscChannel p) = bscChannel (2 * p * (1 - p)) := by
  funext x z
  rw [channelComp_apply]
  fin_cases x <;> fin_cases z <;> simp [bscChannel_apply, Fin.sum_univ_two] <;> ring

/-- **Nielsen & Chuang, Exercise 12.10 (strict example).** The capacity bound
`channelCapacity_channelComp_le_min` can be *strict*: for a nondegenerate crossover probability
`0 < p < 1/2`, the series composition of two copies of the binary symmetric channel `bscChannel p`
has capacity strictly below the minimum of the two individual capacities,
`C(N₂ ∘ N₁) < min (C(N₁)) (C(N₂))` with `N₁ = N₂ = bscChannel p`. Composing compounds the crossover
to `2 p (1 - p) > p` (`channelComp_bscChannel_self`), still within `[0, 1/2]`, and the binary
entropy is strictly increasing there (`binEntropy_strictMonoOn`), so
`log 2 - H(2 p (1 - p)) < log 2 - H(p)`. -/
theorem channelCapacity_channelComp_bscChannel_lt_min {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    channelCapacity (channelComp (bscChannel p) (bscChannel p))
      < min (channelCapacity (bscChannel p)) (channelCapacity (bscChannel p)) := by
  have h0 : (0 : ℝ) ≤ p := hp0.le
  have h1 : p ≤ 1 := by linarith
  have hsub : (0 : ℝ) ≤ 1 - p := by linarith
  have hr0 : (0 : ℝ) ≤ 2 * p * (1 - p) := by nlinarith [mul_nonneg h0 hsub]
  have hr1 : 2 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  rw [min_self, channelComp_bscChannel_self, bscChannel_channelCapacity hr0 hr1,
    bscChannel_channelCapacity h0 h1]
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  have hmem_p : p ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨h0, by rw [hhalf]; linarith⟩
  have hmem_r : 2 * p * (1 - p) ∈ Set.Icc (0 : ℝ) 2⁻¹ :=
    ⟨hr0, by rw [hhalf]; nlinarith [sq_nonneg (1 - 2 * p)]⟩
  have hlt : p < 2 * p * (1 - p) := by
    nlinarith [mul_pos hp0 (show (0 : ℝ) < 1 - 2 * p by linarith)]
  linarith [binEntropy_strictMonoOn hmem_p hmem_r hlt]

end Real
