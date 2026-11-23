/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch8.Problem8_3
import AxQM.NC.Ch9.Theorem9_2
import AxQM.Core.StrictContraction

/-!
# Nielsen & Chuang, Exercise 9.13 (Bit flip channel: contractive, not strictly; fixed points)

Show bit flip channel is contractive not strictly; find its fixed points.

The **bit flip channel** (N&C §8.3.3, eq. `(8.94)`) flips a qubit with probability `1 − p`; it has
operation elements `E₀ = √p I`, `E₁ = √(1−p) X`, so

`E(ρ) = p ρ + (1 − p) X ρ X`.

This is the qubit **Pauli channel** `∑ₖ pₖ σₖ ρ σₖ` (`AxQM.pauliChannel`, Problem 8.3) with
the weight distribution `![p, 1 − p, 0, 0]` over the four Paulis `I, X, Y, Z`. Its action on the
Bloch ball is the diagonal contraction with Pauli-transfer coefficients
`(mₓ, m_y, m_z) = (1, 2p − 1, 2p − 1)`:

`r⃗ = (r₀, r₁, r₂) ↦ (r₀, (2p − 1) r₁, (2p − 1) r₂)`

— the `x̂`-axis is left **exactly** fixed while the `ŷ`–`ẑ` plane is scaled by `2p − 1`
(magnitude `|2p − 1| ≤ 1`; N&C's figure 8.8 is the contraction factor `1 − 2p` for `p = 0.3`).

## What the exercise asks, and how it is delivered

* **Contractive** — `D(E(ρ), E(σ)) ≤ D(ρ, σ)` for all `ρ, σ` (`bitFlipChannel_traceDistance_le`).
  This is *not* special to the bit flip channel: it is the instance at this channel of **Theorem
  9.2** (`traceDistance_channel_le`, every trace-preserving quantum operation is contractive), the
  bit flip channel being a genuine CPTP map (`bitFlipChannel_isChannel`, it is a random-unitary
  Pauli channel).
* **Not strictly contractive** — `¬ StrictlyContractive E`
  (`not_strictlyContractive_bitFlipChannel`). Strict contraction (Exercise 9.10,
  `AxQM.StrictlyContractive`) would require `D(E(ρ), E(σ)) < D(ρ, σ)` for *every*
  `ρ ≠ σ`; but the two distinct pure states `|±⟩ = blochState (±1, 0, 0)` sit on the `x̂`-axis,
  which `E` fixes, so `D(E|+⟩, E|−⟩) = D(|+⟩, |−⟩)` — equality, not strict decrease. (The `x̂`-axis
  is preserved for **every** `p`, since `mₓ = p + (1−p) = 1`, so the bit flip channel is never
  strictly contractive — contrast the depolarizing channel of Exercise 9.12, which contracts *all
  three* axes.)
* **Fixed points** — the set of fixed points is exactly the **`x̂`-axis segment**
  `{½(I + r_x X) : r_x ∈ [−1, 1]}` (the states diagonal in the `X` eigenbasis, i.e. the mixtures of
  `|+⟩` and `|−⟩`), for the generic channel `p ≠ 1`. Delivered as:
  * `bitFlipChannel_isFixedPt_blochState` — *every* Bloch state with `r_y = r_z = 0` is a fixed
    point (**all** `p`): the `x̂`-axis is fixed;
  * `bitFlipChannel_isFixedPt_blochState_iff` — for `p < 1`, a Bloch state is a fixed point *iff*
    `r_y = r_z = 0`. Together with `State.exists_blochState` (every qubit state is a Bloch state,
    N&C Exercise 2.72), this pins the fixed-point set down to precisely the `x̂`-axis. For `p = 1`
    the channel is the identity `E(ρ) = ρ` and *every* state is fixed — the degenerate case the
    `p < 1` hypothesis excludes.

## Ingredients

The statements use the trace distance `State.traceDistance`, the strict-contraction predicate
`StrictlyContractive`, the CPTP predicate `IsChannel`, the Bloch state `blochState`, and the Mathlib
fixed-point API `Function.IsFixedPt`. They rest on the diagonal Bloch action of the Pauli channel,
`pauliChannel_apply_blochState`, from Problem 8.3 (`AxQM/NC/Ch8/Problem8_3.lean`).

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv.
ed.). Cambridge University Press. §8.3.3 (p. 376), §9.2.1, Exercise 9.13 (p. 409).

N&C Exercise 9.13, p. 409.
-/

open Matrix

noncomputable section

namespace AxQM

/-- The bit flip weights `![p, 1 − p, 0, 0]` form a **nonnegative** family, given `0 ≤ p ≤ 1`. -/
theorem bitFlipProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i, 0 ≤ (![p, 1 - p, 0, 0] : Fin 4 → ℝ) i := by
  intro i
  fin_cases i <;> simp <;> linarith

/-- The bit flip weights `![p, 1 − p, 0, 0]` **sum to one**: `p + (1 − p) + 0 + 0 = 1`. -/
theorem bitFlipProb_sum (p : ℝ) : ∑ i, (![p, 1 - p, 0, 0] : Fin 4 → ℝ) i = 1 := by
  simp [Fin.sum_univ_four]

/-- **The Pauli-transfer vector of the bit flip channel** is the diagonal contraction
`r⃗ ↦ (r₀, (2p − 1) r₁, (2p − 1) r₂)`. The transfer coefficients `mⱼ = ∑ₖ ±pₖ` of the weights
`![p, 1 − p, 0, 0]` are `mₓ = p + (1−p) = 1`, `m_y = m_z = p − (1−p) = 2p − 1`. -/
theorem pauliTwirlVec_bitFlip (p : ℝ) (r : Fin 3 → ℝ) :
    Concrete.pauliTwirlVec ![p, 1 - p, 0, 0] r = ![r 0, (2 * p - 1) * r 1, (2 * p - 1) * r 2] := by
  funext i
  fin_cases i <;>
    simp only [Concrete.pauliTwirlVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] <;> ring_nf

/-- **The bit flip channel keeps a Bloch vector inside the closed unit ball.** The image
`(r₀, (2p − 1) r₁, (2p − 1) r₂)` has squared norm `≤ r₀² + r₁² + r₂² ≤ 1` because `|2p − 1| ≤ 1` —
a direct consequence of the Pauli channel's Bloch-ball contraction
(`Concrete.pauliTwirlVec_sq_sum_le`). -/
theorem bitFlipVec_sq_sum_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : Fin 3 → ℝ)
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    r 0 ^ 2 + ((2 * p - 1) * r 1) ^ 2 + ((2 * p - 1) * r 2) ^ 2 ≤ 1 := by
  have hle := Concrete.pauliTwirlVec_sq_sum_le ![p, 1 - p, 0, 0] r
    (bitFlipProb_nonneg hp0 hp1) (bitFlipProb_sum p)
  rw [pauliTwirlVec_bitFlip] at hle
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hle
  linarith

/-- **The bit flip channel** `E(ρ) = p ρ + (1 − p) X ρ X` (Nielsen & Chuang §8.3.3, eq. `(8.94)`),
for flip probability `1 − p`, `0 ≤ p ≤ 1`. Realised as the qubit Pauli channel
(`AxQM.pauliChannel`, Problem 8.3) with weight distribution `![p, 1 − p, 0, 0]` over the
Paulis `I, X, Y, Z` — mixing `I` (weight `p`) and `X` (weight `1 − p`) only. -/
def bitFlipChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit → State qubit :=
  (pauliChannel ![p, 1 - p, 0, 0] (bitFlipProb_nonneg hp0 hp1) (bitFlipProb_sum p)).apply

/-- **The bit flip channel is a genuine CPTP quantum channel** (`IsChannel`) — being a
random-unitary Pauli channel (`pauliChannel_isChannel`). This is what makes Theorem 9.2's
contractivity apply to it. -/
theorem bitFlipChannel_isChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsChannel (bitFlipChannel p hp0 hp1) :=
  pauliChannel_isChannel _ _ _

/-- **The Bloch action of the bit flip channel is the diagonal contraction**
`blochState (r₀, r₁, r₂) ↦ blochState (r₀, (2p − 1) r₁, (2p − 1) r₂)`: the `x̂`-component is left
alone, the `ŷ`- and `ẑ`-components are scaled by `2p − 1`. Immediate from the Pauli channel's Bloch
action (`pauliChannel_apply_blochState`) and the transfer coefficients `pauliTwirlVec_bitFlip`. -/
theorem bitFlipChannel_apply_blochState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : Fin 3 → ℝ)
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    bitFlipChannel p hp0 hp1 (blochState r h)
      = blochState ![r 0, (2 * p - 1) * r 1, (2 * p - 1) * r 2]
          (bitFlipVec_sq_sum_le hp0 hp1 r h) := by
  simp only [bitFlipChannel]
  rw [pauliChannel_apply_blochState]
  exact blochState_congr (pauliTwirlVec_bitFlip p r)

/-- **The bit flip channel is contractive** (Nielsen & Chuang, Exercise 9.13, part 1): it never
increases the trace distance, `D(E(ρ), E(σ)) ≤ D(ρ, σ)`. This is the instance at the bit flip
channel of **Theorem 9.2** (`traceDistance_channel_le`) — every trace-preserving quantum operation
is contractive — using that the bit flip channel is a CPTP map (`bitFlipChannel_isChannel`). -/
theorem bitFlipChannel_traceDistance_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : State qubit) :
    (bitFlipChannel p hp0 hp1 ρ).traceDistance (bitFlipChannel p hp0 hp1 σ)
      ≤ ρ.traceDistance σ :=
  traceDistance_channel_le (bitFlipChannel_isChannel p hp0 hp1) ρ σ

/-- **Every Bloch state on the `x̂`-axis is a fixed point of the bit flip channel** (for *all*
`p`): if `r_y = r_z = 0` then `E(½(I + r_x X)) = ½(I + r_x X)`. The bit flip channel leaves the
`x̂`-component untouched and multiplies `r_y, r_z` by `2p − 1`, so a Bloch vector already on the
`x̂`-axis is preserved. -/
theorem bitFlipChannel_isFixedPt_blochState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {r : Fin 3 → ℝ}
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) (hy : r 1 = 0) (hz : r 2 = 0) :
    Function.IsFixedPt (bitFlipChannel p hp0 hp1) (blochState r h) := by
  change bitFlipChannel p hp0 hp1 (blochState r h) = blochState r h
  rw [bitFlipChannel_apply_blochState]
  refine blochState_congr ?_
  funext i
  fin_cases i <;> simp [hy, hz]

/-- **The fixed points of the bit flip channel are exactly the `x̂`-axis states** (Nielsen & Chuang,
Exercise 9.13, "find the set of fixed points"), for the generic channel `p < 1`: a Bloch state
`½(I + r⃗·σ)` is fixed by `E` *iff* its Bloch vector lies on the `x̂`-axis, `r_y = r_z = 0`.

`(⇐)` is `bitFlipChannel_isFixedPt_blochState` (holds for all `p`). `(⇒)`: if `E` fixes
`blochState r`, the Bloch action forces `blochState (r₀, (2p−1)r₁, (2p−1)r₂) = blochState r`, so by
uniqueness of the Bloch vector (`blochState_injective`) `(2p − 1) r₁ = r₁` and `(2p − 1) r₂ = r₂`,
i.e. `(2p − 2) r_j = 0`; with `p < 1` the factor `2p − 2 ≠ 0`, forcing `r₁ = r₂ = 0`.

Combined with `State.exists_blochState` (every qubit state is a Bloch state), this identifies the
full fixed-point set with the `x̂`-axis segment `{½(I + r_x X) : r_x ∈ [−1, 1]}` — the states
diagonal in the `X` eigenbasis, i.e. the mixtures of `|+⟩` and `|−⟩`. (At `p = 1` the channel is the
identity and every state is fixed, so the hypothesis `p < 1` is necessary.) -/
theorem bitFlipChannel_isFixedPt_blochState_iff (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp1' : p < 1)
    {r : Fin 3 → ℝ} (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    Function.IsFixedPt (bitFlipChannel p hp0 hp1) (blochState r h) ↔ r 1 = 0 ∧ r 2 = 0 := by
  constructor
  · intro hfix
    have hvec := blochState_injective
      ((bitFlipChannel_apply_blochState p hp0 hp1 r h).symm.trans hfix)
    have h1 := congrFun hvec 1
    have h2 := congrFun hvec 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at h1 h2
    have hne : (2 * p - 2 : ℝ) ≠ 0 := by intro hc; linarith
    exact ⟨(mul_eq_zero.mp (by linear_combination h1)).resolve_left hne,
      (mul_eq_zero.mp (by linear_combination h2)).resolve_left hne⟩
  · rintro ⟨hy, hz⟩
    exact bitFlipChannel_isFixedPt_blochState p hp0 hp1 h hy hz

/-- **The bit flip channel is *not* strictly contractive** (Nielsen & Chuang, Exercise 9.13,
part 2). Strict contraction (`StrictlyContractive`, Exercise 9.10) would give
`D(E(ρ), E(σ)) < D(ρ, σ)` for *every* pair of distinct states; but the two distinct pure states
`|±⟩ = blochState (±1, 0, 0)` lie on the `x̂`-axis, which `E` fixes, so
`D(E|+⟩, E|−⟩) = D(|+⟩, |−⟩)` — the distance is preserved, contradicting the strict decrease. The
`x̂`-axis is fixed for **every** `p` (`mₓ = p + (1−p) = 1`), so the bit flip channel is strictly
contractive for no value of `p`. -/
theorem not_strictlyContractive_bitFlipChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ¬ StrictlyContractive (bitFlipChannel p hp0 hp1) := by
  intro hSC
  have hb1 : (![1, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![1, 0, 0] : Fin 3 → ℝ) 1 ^ 2
      + (![1, 0, 0] : Fin 3 → ℝ) 2 ^ 2 ≤ 1 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have hb2 : (![-1, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![-1, 0, 0] : Fin 3 → ℝ) 1 ^ 2
      + (![-1, 0, 0] : Fin 3 → ℝ) 2 ^ 2 ≤ 1 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have hfρ : bitFlipChannel p hp0 hp1 (blochState ![1, 0, 0] hb1) = blochState ![1, 0, 0] hb1 :=
    bitFlipChannel_isFixedPt_blochState (r := ![1, 0, 0]) p hp0 hp1 hb1 (by simp)
      (by simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
  have hfσ : bitFlipChannel p hp0 hp1 (blochState ![-1, 0, 0] hb2) = blochState ![-1, 0, 0] hb2 :=
    bitFlipChannel_isFixedPt_blochState (r := ![-1, 0, 0]) p hp0 hp1 hb2 (by simp)
      (by simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
  have hne : blochState ![1, 0, 0] hb1 ≠ blochState ![-1, 0, 0] hb2 := by
    intro he
    have hveq := congrFun (blochState_injective he) 0
    norm_num at hveq
  have hlt := hSC _ _ hne
  rw [hfρ, hfσ] at hlt
  exact lt_irrefl _ hlt

end AxQM
