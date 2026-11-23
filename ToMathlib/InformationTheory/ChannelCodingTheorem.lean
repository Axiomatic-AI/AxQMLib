/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.ChannelAchievability

/-!
# Shannon's noisy channel coding theorem

This file closes **Shannon's noisy channel coding theorem** (Nielsen & Chuang, Theorem 12.7;
Cover–Thomas, Theorem 7.7.1): the *operational* capacity `C(N)` of a discrete memoryless channel
`q` equals its *information* capacity `max_{p(x)} H(X : Y)`,

`Real.channelOpCapacity_eq_channelCapacity_div` :
  `channelOpCapacity q = channelCapacity q / log 2`.

Here `channelOpCapacity q` is the supremum of achievable rates (in bits) and `channelCapacity q` is
`max_{p(x)} channelMutualInfo q p = max_{p(x)} H(X : Y)` (in nats); the factor `/ log 2` converts
the information capacity from nats to bits, so this is exactly N&C eq. (12.67) `C(N) = max_{p(x)}
H(X : Y)` under the base-2 convention of the operational rate.

## Proof

The two inequalities are the two halves of the theorem, both already developed upstream:

* **Converse** `channelOpCapacity q ≤ channelCapacity q / log 2`
  (`Real.channelOpCapacity_le_channelCapacity_div`, Fano + data-processing + single-letterization).
* **Achievability** `channelCapacity q / log 2 ≤ channelOpCapacity q`
  (`Real.channelCapacity_div_le_channelOpCapacity`, proved here): the *fixed-input* achievability
  `Real.isAchievableRate_of_lt_channelMutualInfo` (random coding + expurgation) says every rate `R`
  with `R · log 2 < channelMutualInfo q p` is achievable. Lifting it over the *capacity-attaining*
  input distribution `p⋆` (the `max_{p(x)}` of eq. (12.67), which exists by
  `Real.exists_isMaxOn_channelMutualInfo`), every rate `R < channelCapacity q / log 2` satisfies
  `R · log 2 < channelCapacity q = channelMutualInfo q p⋆`, hence is achievable, hence is
  `≤ channelOpCapacity q`; as this holds for all such `R`, `channelCapacity q / log 2 ≤
  channelOpCapacity q` (`exists_between`).

`le_antisymm` of the two directions gives the equality.

## Main declarations

* `Real.channelCapacity_div_le_channelOpCapacity` — the achievability direction
  `channelCapacity q / log 2 ≤ channelOpCapacity q`.
* `Real.channelOpCapacity_eq_channelCapacity_div` — **Shannon's noisy channel coding theorem**:
  `channelOpCapacity q = channelCapacity q / log 2`, i.e. `C(N) = max_{p(x)} H(X : Y)`.
-/

@[expose] public section

open Finset Filter Topology

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Achievability half of Shannon's noisy channel coding theorem** (Nielsen & Chuang,
Theorem 12.7): the information capacity is a lower bound for the operational capacity,
`channelCapacity q / log 2 ≤ channelOpCapacity q`.

Every rate `R` strictly below `channelCapacity q / log 2` is achievable: at the capacity-attaining
input `p⋆` (`exists_isMaxOn_channelMutualInfo`), `R · log 2 < channelCapacity q =
channelMutualInfo q p⋆`, so fixed-input achievability (`isAchievableRate_of_lt_channelMutualInfo`)
makes `R` achievable, whence `R ≤ channelOpCapacity q` (`le_channelOpCapacity`). Since this bounds
every `R` below `channelCapacity q / log 2`, so is their supremum. -/
theorem channelCapacity_div_le_channelOpCapacity [Nonempty ι] [Nonempty κ] {q : ι → κ → ℝ}
    (hN : IsChannel q) : channelCapacity q / Real.log 2 ≤ channelOpCapacity q := by
  obtain ⟨p, hp, _, hpeq⟩ := exists_isMaxOn_channelMutualInfo q
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Every rate `R < channelCapacity q / log 2` is achievable — at the capacity-attaining input `p`,
  -- `R · log 2 < channelMutualInfo q p` — hence `R ≤ channelOpCapacity q`; a dense-order bound
  -- lifts this to the supremum `channelCapacity q / log 2`.
  exact le_of_forall_lt_imp_le_of_dense fun R hR =>
    le_channelOpCapacity hN (isAchievableRate_of_lt_channelMutualInfo hN hp.1 hp.2
      (hpeq ▸ (lt_div_iff₀ hlog2).mp hR))

/-- **Shannon's noisy channel coding theorem** (Nielsen & Chuang, Theorem 12.7, eq. (12.67)): the
operational capacity `C(N)` of a discrete memoryless channel equals its information capacity
`max_{p(x)} H(X : Y)`,

`channelOpCapacity q = channelCapacity q / log 2`.

The operational rate is measured in bits and the mutual information in nats, so `channelCapacity q`
(in nats) is divided by `log 2` to convert to bits. `le_antisymm` of the converse
(`channelOpCapacity_le_channelCapacity_div`) and the achievability direction
(`channelCapacity_div_le_channelOpCapacity`). -/
theorem channelOpCapacity_eq_channelCapacity_div [Nonempty ι] [Nonempty κ] {q : ι → κ → ℝ}
    (hN : IsChannel q) : channelOpCapacity q = channelCapacity q / Real.log 2 :=
  le_antisymm (channelOpCapacity_le_channelCapacity_div hN)
    (channelCapacity_div_le_channelOpCapacity hN)

end Real
