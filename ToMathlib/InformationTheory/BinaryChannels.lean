/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.NoisyChannel
public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The erasure and binary symmetric channels, and their capacities

The **erasure channel** (Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise
12.9, p. 553) has two inputs `0, 1` and three outputs `0, 1, e`: with probability `1 - r` the input
is transmitted unchanged, and with probability `r` it is *erased* and replaced by the special symbol
`e`. We model it as `Real.erasureChannel r : Fin 2 → Option (Fin 2) → ℝ`, where the output type
`Option (Fin 2)` uses `none` for the erasure symbol `e` and `some z` for the transmitted bit `z`.

The point of the exercise is that the receiver *knows* when an erasure has happened, so the only
information lost is a fraction `r` of the input. Concretely the channel mutual information
factors as

`Real.channelMutualInfo (erasureChannel r) p = (1 - r) · H(X)`

(`erasureChannel_channelMutualInfo`), and maximizing `H(X) ≤ log 2` over input distributions
gives the **capacity**

`Real.channelCapacity (erasureChannel r) = (1 - r) · log 2`

(`erasureChannel_channelCapacity`) — N&C's `1 - r`, in nats (N&C measures entropy in bits, so its
`1` is our `log 2`; the value is base-independent up to this global factor).

The **binary symmetric channel** `Real.bscChannel p : Fin 2 → Fin 2 → ℝ` transmits each bit
unchanged with probability `1 - p` and flips it with probability `p`. Every row has the same noise
entropy `H(p)`, so its mutual information is `H(Y) - H(p)`; maximizing `H(Y) ≤ log 2` (attained at
the uniform input, where the output is uniform) gives the capacity

`Real.channelCapacity (bscChannel p) = log 2 - H(p)`

(`bscChannel_channelCapacity`) — N&C's `1 - H(p)`, in nats. Part (2) of the exercise then compares
the two: `erasureChannel_capacity_gt_bsc` shows the erasure capacity `(1 - p)·log 2` exceeds the BSC
capacity `log 2 - H(p)`, which reduces to the binary-entropy inequality `H(p) > p·log 2`
(`binEntropy_gt_mul_log_two`). This holds on the standard noise regime `0 < p ≤ 1/2`; the claim is
*false* unrestricted (as `p → 1` the near-inverting BSC has capacity approaching `log 2` while the
erasure channel's approaches `0`), so we prove it on `0 < p ≤ 1/2`, where the binary symmetric
channel is conventionally defined. Intuitively (N&C's "why is this plausible?") the erasure receiver
is *told* which bits are lost, whereas the BSC's flips are silent and must be inferred — a strictly
harder situation, so the erasure channel carries strictly more information.

## Main declarations

* `Real.erasureChannel` — the erasure channel with erasure probability `r`.
* `Real.isChannel_erasureChannel` — it is a channel for `0 ≤ r ≤ 1`.
* `Real.erasureChannel_channelMutualInfo` — `H(X : Y) = (1 - r) · H(X)`.
* `Real.erasureChannel_channelCapacity` — the capacity is `(1 - r) · log 2`.
* `Real.bscChannel` — the binary symmetric channel with crossover probability `p`.
* `Real.isChannel_bscChannel` — it is a channel for `0 ≤ p ≤ 1`.
* `Real.bscChannel_channelMutualInfo` — `H(X : Y) = H(Y) - H(p)`.
* `Real.bscChannel_channelCapacity` — the capacity is `log 2 - H(p)`.
* `Real.binEntropy_gt_mul_log_two` — the inequality `H(p) > p · log 2` on `0 < p ≤ 1/2`.
* `Real.erasureChannel_capacity_gt_bsc` — the erasure capacity exceeds the BSC capacity on
  `0 < p ≤ 1/2` (Exercise 12.9 (2)).

## Context

This is pure classical information theory, stated for the functions
`Fin 2 → Option (Fin 2) → ℝ` and `Fin 2 → Fin 2 → ℝ`. It builds on the discrete-memoryless-channel
development of `ToMathlib/InformationTheory/NoisyChannel.lean` (Shannon's noisy channel coding
theorem, N&C Theorem 12.7).
-/

@[expose] public section

namespace Real

/-! ### The erasure channel -/

/-- The **erasure channel** with erasure probability `r`: on input `x : Fin 2` it outputs the bit
`x` (i.e. `some x`) with probability `1 - r`, and the erasure symbol `e` (i.e. `none`) with
probability `r`. -/
def erasureChannel (r : ℝ) : Fin 2 → Option (Fin 2) → ℝ :=
  fun x y =>
    match y with
    | none => r
    | some z => if z = x then 1 - r else 0

@[simp] theorem erasureChannel_none (r : ℝ) (x : Fin 2) : erasureChannel r x none = r := rfl

@[simp] theorem erasureChannel_some (r : ℝ) (x z : Fin 2) :
    erasureChannel r x (some z) = if z = x then 1 - r else 0 := rfl

/-- Each row of the erasure channel sums to `1` (it holds for every `r`, no bound needed). -/
theorem sum_erasureChannel (r : ℝ) (x : Fin 2) : ∑ y, erasureChannel r x y = 1 := by
  rw [Fintype.sum_option]
  simp only [erasureChannel_none, erasureChannel_some, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

/-- The erasure channel is a discrete memoryless channel when `0 ≤ r ≤ 1`. -/
theorem isChannel_erasureChannel {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsChannel (erasureChannel r) where
  nonneg x y := by
    cases y with
    | none => simpa using h0
    | some z =>
      simp only [erasureChannel_some]
      split
      · linarith
      · exact le_refl _
  row_sum x := sum_erasureChannel r x

/-! ### The mutual information and capacity of the erasure channel -/

/-- Each conditional distribution `erasureChannel r x` has entropy `H(Y | X = x) = H(r)`, the binary
entropy: the output is the input with probability `1 - r` and the erasure symbol with probability
`r`. -/
theorem entropy_erasureChannel (r : ℝ) (x : Fin 2) :
    entropy (erasureChannel r x) = binEntropy r := by
  rw [entropy_eq, Fintype.sum_option]
  have hz : (∑ z : Fin 2, negMulLog (erasureChannel r x (some z))) = negMulLog (1 - r) := by
    simp only [erasureChannel_some, apply_ite negMulLog, negMulLog_zero]
    simp [Finset.sum_ite_eq']
  rw [hz, erasureChannel_none, binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- Fed input distribution `p`, the erasure channel outputs `some z` with probability
`p z · (1 - r)`. -/
theorem channelOutput_erasureChannel_some (r : ℝ) (p : Fin 2 → ℝ) (z : Fin 2) :
    channelOutput (erasureChannel r) p (some z) = p z * (1 - r) := by
  simp only [channelOutput_apply, erasureChannel_some, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq]

/-- Fed a probability distribution `p`, the erasure channel outputs the erasure symbol with
probability `r`. -/
theorem channelOutput_erasureChannel_none {r : ℝ} {p : Fin 2 → ℝ} (hp1 : ∑ x, p x = 1) :
    channelOutput (erasureChannel r) p none = r := by
  simp only [channelOutput_apply, erasureChannel_none, ← Finset.sum_mul, hp1, one_mul]

/-- The output entropy of the erasure channel: `H(Y) = H(r) + (1 - r) · H(X)`. -/
theorem entropy_channelOutput_erasureChannel {r : ℝ} {p : Fin 2 → ℝ} (hp1 : ∑ x, p x = 1) :
    entropy (channelOutput (erasureChannel r) p) = binEntropy r + (1 - r) * entropy p := by
  rw [entropy_eq, Fintype.sum_option, channelOutput_erasureChannel_none hp1]
  simp only [channelOutput_erasureChannel_some, negMulLog_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp1, one_mul, ← entropy_eq,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- **Exercise 12.9 (1), mutual information.** The channel mutual information of the erasure channel
fed input distribution `p` is `H(X : Y) = (1 - r) · H(X)`: the erasure keeps a `1 - r` fraction of
the input information. (Holds for any `r`; only `p` being a distribution is used.) -/
theorem erasureChannel_channelMutualInfo {r : ℝ} {p : Fin 2 → ℝ} (hp1 : ∑ x, p x = 1) :
    channelMutualInfo (erasureChannel r) p = (1 - r) * entropy p := by
  rw [channelMutualInfo_eq _ (sum_erasureChannel r), entropy_channelOutput_erasureChannel hp1]
  simp only [entropy_erasureChannel]
  rw [← Finset.sum_mul, hp1, one_mul]
  ring

/-- **Exercise 12.9 (1).** The capacity of the erasure channel with erasure probability `0 ≤ r ≤ 1`
is `(1 - r) · log 2` — Nielsen & Chuang's `1 - r`, measured in nats (their `1` is `log 2`). The
maximum is attained at the uniform input distribution, where `H(X) = log 2`. -/
theorem erasureChannel_channelCapacity {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    channelCapacity (erasureChannel r) = (1 - r) * Real.log 2 := by
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  -- The uniform input maximizes `H(X : Y) = (1 - r) · H(X)`, since `H(X) ≤ log 2 = H(uniform)`.
  have hmax : IsMaxOn (channelMutualInfo (erasureChannel r)) (probSimplex (Fin 2))
      (fun _ => (Fintype.card (Fin 2) : ℝ)⁻¹) := by
    rw [isMaxOn_iff]
    intro p hp
    rw [erasureChannel_channelMutualInfo hp.2,
      erasureChannel_channelMutualInfo uniform_mem_probSimplex.2, entropy_uniform, hcard]
    have hle : entropy p ≤ Real.log 2 := by
      have := entropy_le_log_card (p := p) hp.1 hp.2
      rwa [hcard] at this
    exact mul_le_mul_of_nonneg_left hle (by linarith)
  rw [channelCapacity_eq_of_isMaxOn (isChannel_erasureChannel h0 h1) uniform_mem_probSimplex hmax,
    erasureChannel_channelMutualInfo uniform_mem_probSimplex.2, entropy_uniform, hcard]

/-! ### The binary symmetric channel -/

/-- The **binary symmetric channel** with crossover probability `p` (Nielsen & Chuang, p. 552): on
input `x : Fin 2` it outputs `x` unchanged with probability `1 - p` and the flipped bit `1 - x` with
probability `p` (i.e. it outputs `y` with probability `p` when `y ≠ x`). -/
def bscChannel (p : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun x y => if y = x then 1 - p else p

@[simp] theorem bscChannel_apply (p : ℝ) (x y : Fin 2) :
    bscChannel p x y = if y = x then 1 - p else p := rfl

/-- Each row of the binary symmetric channel sums to `1` (it holds for every `p`, no bound needed):
one output equals the input with probability `1 - p`, the other differs with probability `p`. -/
theorem sum_bscChannel (p : ℝ) (x : Fin 2) : ∑ y, bscChannel p x y = 1 := by
  fin_cases x <;> simp [Fin.sum_univ_two]

/-- The binary symmetric channel is a discrete memoryless channel when `0 ≤ p ≤ 1`. -/
theorem isChannel_bscChannel {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsChannel (bscChannel p) where
  nonneg x y := by
    rw [bscChannel_apply]; split
    · linarith
    · exact h0
  row_sum x := sum_bscChannel p x

/-- Each conditional distribution `bscChannel p x` has entropy `H(Y | X = x) = H(p)`, the binary
entropy: the output equals the input with probability `1 - p` and the flipped bit with probability
`p`, so the same two-point distribution `{1 - p, p}` occurs for either input. -/
theorem entropy_bscChannel (p : ℝ) (x : Fin 2) :
    entropy (bscChannel p x) = binEntropy p := by
  rw [entropy_eq, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  fin_cases x <;> simp [Fin.sum_univ_two, add_comm]

/-- **Mutual information of the binary symmetric channel.** Fed input distribution `p_in`, the BSC
has channel mutual information `H(X : Y) = H(Y) - H(p)`: every row has the same noise entropy
`H(p)`, so the averaged noise term `∑ₓ p_in(x) · H(Y | X = x)` collapses to `H(p)`. -/
theorem bscChannel_channelMutualInfo {p : ℝ} {p_in : Fin 2 → ℝ} (hp1 : ∑ x, p_in x = 1) :
    channelMutualInfo (bscChannel p) p_in
      = entropy (channelOutput (bscChannel p) p_in) - binEntropy p := by
  rw [channelMutualInfo_eq _ (sum_bscChannel p)]
  simp only [entropy_bscChannel, ← Finset.sum_mul, hp1, one_mul]

/-- Fed the uniform input, the binary symmetric channel outputs the uniform distribution: the BSC is
doubly stochastic (each column also sums to `1`, by symmetry), so the output of the uniform input is
`(1/2)·(column sum) = 1/2`. This is the equality case that pins the capacity's value. -/
theorem channelOutput_bscChannel_uniform (p : ℝ) :
    channelOutput (bscChannel p) (fun _ : Fin 2 => (Fintype.card (Fin 2) : ℝ)⁻¹)
      = fun _ => (Fintype.card (Fin 2) : ℝ)⁻¹ := by
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  funext y
  simp only [channelOutput_apply, bscChannel_apply, hcard]
  fin_cases y <;> simp [Fin.sum_univ_two] <;> ring

/-- **Exercise 12.9 (2), capacity of the binary symmetric channel.** The capacity of the BSC with
crossover probability `0 ≤ p ≤ 1` is `log 2 - H(p)` — Nielsen & Chuang's `1 - H(p)`, in nats (their
`1` is `log 2`). The mutual information is `H(Y) - H(p)`, and `H(Y) ≤ log 2` is maximized (equal to
`log 2`) at the uniform input, where the output is uniform. -/
theorem bscChannel_channelCapacity {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    channelCapacity (bscChannel p) = Real.log 2 - binEntropy p := by
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  -- The uniform input maximizes `H(X : Y) = H(Y) - H(p)`, since `H(Y) ≤ log 2 = H(uniform output)`.
  have hmax : IsMaxOn (channelMutualInfo (bscChannel p)) (probSimplex (Fin 2))
      (fun _ => (Fintype.card (Fin 2) : ℝ)⁻¹) := by
    rw [isMaxOn_iff]
    intro p_in hp
    rw [bscChannel_channelMutualInfo hp.2, bscChannel_channelMutualInfo uniform_mem_probSimplex.2,
      channelOutput_bscChannel_uniform, entropy_uniform, hcard]
    have hle : entropy (channelOutput (bscChannel p) p_in) ≤ Real.log 2 := by
      have := entropy_le_log_card (p := channelOutput (bscChannel p) p_in)
        (channelOutput_nonneg (isChannel_bscChannel h0 h1) hp.1)
        (sum_channelOutput (isChannel_bscChannel h0 h1) hp.2)
      rwa [hcard] at this
    linarith
  rw [channelCapacity_eq_of_isMaxOn (isChannel_bscChannel h0 h1) uniform_mem_probSimplex hmax,
    bscChannel_channelMutualInfo uniform_mem_probSimplex.2, channelOutput_bscChannel_uniform,
    entropy_uniform, hcard]

/-! ### Erasure capacity exceeds binary-symmetric-channel capacity -/

/-- A binary-entropy inequality on the standard noise regime `0 < p ≤ 1/2`: the binary entropy
strictly exceeds `p · log 2`. Writing `H(p) = negMulLog p + negMulLog (1 - p)`, the identity
`H(p) - p·log 2 = -p·log (2p) - (1 - p)·log (1 - p)` has both summands nonnegative, and the second
strictly positive: `2p ≤ 1` makes `log (2p) ≤ 0`, and `0 < 1 - p < 1` makes `log (1 - p) < 0`. -/
theorem binEntropy_gt_mul_log_two {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 2⁻¹) :
    p * Real.log 2 < binEntropy p := by
  have hp1' : p < 1 := lt_of_le_of_lt hp₁ (by norm_num)
  have h1p : 0 < 1 - p := by linarith
  have hkey : binEntropy p - p * Real.log 2
      = -(p * Real.log (2 * p)) - (1 - p) * Real.log (1 - p) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    rw [Real.log_mul (by norm_num) hp₀.ne']
    ring
  have t1 : Real.log (2 * p) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have t2 : Real.log (1 - p) < 0 := Real.log_neg h1p (by linarith)
  nlinarith [mul_nonneg hp₀.le (neg_nonneg.mpr t1), mul_pos h1p (neg_pos.mpr t2)]

/-- **Exercise 12.9 (2).** On the standard noise regime `0 < p ≤ 1/2`, the capacity of the erasure
channel exceeds the capacity of the binary symmetric channel with the *same* parameter `p`: the
erasure capacity `(1 - p)·log 2` beats the BSC capacity `log 2 - H(p)` precisely because
`H(p) > p·log 2` (`binEntropy_gt_mul_log_two`). The unrestricted claim as printed is false — for
`p → 1` the near-inverting BSC has capacity approaching `log 2` while the erasure capacity nears
`0` — so the natural `0 < p ≤ 1/2` regime, where the binary symmetric channel is conventionally
defined (a crossover `p > 1/2` is relabelled to `1 - p`), is required. -/
theorem erasureChannel_capacity_gt_bsc {p : ℝ} (h0 : 0 < p) (h1 : p ≤ 2⁻¹) :
    channelCapacity (bscChannel p) < channelCapacity (erasureChannel p) := by
  have h1' : p ≤ 1 := by linarith
  rw [bscChannel_channelCapacity h0.le h1', erasureChannel_channelCapacity h0.le h1',
    sub_mul, one_mul]
  linarith [binEntropy_gt_mul_log_two h0 h1]

/-- The **unrestricted** form of Exercise 12.9 (2) is *false*: `erasureChannel_capacity_gt_bsc`
genuinely needs its `0 < p ≤ 1/2` hypothesis. At `p = 1` the binary symmetric channel *always*
flips the bit — a perfect, invertible channel of capacity `log 2` — whereas the erasure channel
*always* erases and has capacity `0`. So there the erasure capacity is *strictly smaller* than the
BSC capacity, the exact reverse of the printed claim: a concrete counterexample to the universal
statement. -/
theorem channelCapacity_erasureChannel_lt_bscChannel_at_one :
    channelCapacity (erasureChannel 1) < channelCapacity (bscChannel 1) := by
  rw [erasureChannel_channelCapacity zero_le_one le_rfl,
    bscChannel_channelCapacity zero_le_one le_rfl, binEntropy_one]
  simpa using Real.log_pos (by norm_num)

end Real
