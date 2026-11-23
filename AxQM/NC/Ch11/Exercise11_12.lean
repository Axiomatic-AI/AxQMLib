/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyComparisonState
import AxQM.Postulates.API.BlochStateEntropy
import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Nielsen & Chuang, Exercise 11.12 — comparison of quantum and classical entropies

**Exercise 11.12 (Comparison of quantum and classical entropies).** For `ρ(p) = p |0⟩⟨0| +
(1 − p) |+⟩⟨+|` (with `|+⟩ = (|0⟩ + |1⟩)/√2`), evaluate `S(ρ)` and compare it to `H(p, 1 − p)`.

The state `ρ(p) = entropyComparisonState p` is a mixture of the two **pure** states `|0⟩⟨0|` and
`|+⟩⟨+|`; it is the single-qubit Bloch state with Bloch vector `r⃗ = (1 − p, 0, p)` (that is
`entropyComparisonState_eq_blochState`), whose norm is `‖r⃗‖ = √((1 − p)² + p²)`.

## Results (the item's formalisation)

* `vonNeumannEntropy_entropyComparisonState` — **evaluation.** `S(ρ) = H((1 ± ‖r⃗‖)/2)`, the binary
  Shannon entropy of the two eigenvalues `(1 ± √((1 − p)² + p²))/2` (via the reusable qubit engine
  `blochState_vonNeumannEntropy`). There is no closed form for these as rational multiples of `log`,
  so — exactly as in N&C — the value is this Shannon entropy of the explicit eigenvalue pair.
* `vonNeumannEntropy_entropyComparisonState_le` — **the comparison.** `S(ρ) ≤ H(p, 1 − p)`: the
  quantum entropy never exceeds the classical Shannon entropy of the mixing weights.
* `vonNeumannEntropy_entropyComparisonState_lt` — **the sharp comparison.** For `0 < p < 1`,
  `S(ρ) < H(p, 1 − p)` *strictly*: the classical bound is not saturated because the two mixed
  states `|0⟩` and `|+⟩` are **not orthogonal** (equality `S(ρ) = H(p, 1 − p)` holds only at the
  endpoints `p ∈ {0, 1}`, where `ρ` is pure). This is Exercise 11.12's punchline: mixing
  non-orthogonal states loses less "information" than the labels `H(p, 1 − p)` would suggest.

## Proof of the comparison

Writing `t = √((1 − p)² + p²) ∈ [1/√2, 1]`, the two sides are binary entropies:
`S(ρ) = binEntropy ((1 + t)/2)` and `H(p, 1 − p) = binEntropy p`
(`Real.entropy_fin_two_eq_binEntropy`). Since `binEntropy` is (strictly) decreasing on `[1/2, 1]`
(`Real.binEntropy_strictAntiOn`) and symmetric (`Real.binEntropy_one_sub`), and both `(1 + t)/2` and
`max p (1 − p)` lie in `[1/2, 1]`, the comparison reduces to `|2p − 1| ≤ t`, i.e.
`(2p − 1)² ≤ (1 − p)² + p²`, i.e. `0 ≤ 2p(1 − p)` — true on `[0, 1]`, strict on `(0, 1)`.

The state definition and its Bloch form are in
`AxQM/Postulates/API/EntropyComparisonState.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **N&C Exercise 11.12, evaluation of `S(ρ)`.** For `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|`,
`S(ρ) = H((1 + ‖r⃗‖)/2, (1 − ‖r⃗‖)/2)` with `‖r⃗‖ = √((1 − p)² + p²)`: `ρ` is the Bloch state with
Bloch vector `(1 − p, 0, p)` (`entropyComparisonState_eq_blochState`), whose entropy is the binary
Shannon entropy of the eigenvalues `(1 ± ‖r⃗‖)/2` (`blochState_vonNeumannEntropy`). -/
theorem vonNeumannEntropy_entropyComparisonState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (entropyComparisonState p hp0 hp1).vonNeumannEntropy
      = Real.entropy ![(1 + Real.sqrt ((1 - p) ^ 2 + p ^ 2)) / 2,
                       (1 - Real.sqrt ((1 - p) ^ 2 + p ^ 2)) / 2] := by
  have hSq : (![1 - p, 0, p] : Fin 3 → ℝ) 0 ^ 2 + (![1 - p, 0, p] : Fin 3 → ℝ) 1 ^ 2
      + (![1 - p, 0, p] : Fin 3 → ℝ) 2 ^ 2 = (1 - p) ^ 2 + p ^ 2 := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  rw [entropyComparisonState_eq_blochState,
    blochState_vonNeumannEntropy ![1 - p, 0, p] (comparison_blochVector_normSq_le_one p hp0 hp1)
      (by rw [hSq]; nlinarith [sq_nonneg (1 - 2 * p)]), hSq]

/-- **N&C Exercise 11.12, the comparison `S(ρ) ≤ H(p, 1 − p)`.** The von Neumann entropy of the
mixture `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|` never exceeds the classical Shannon entropy `H(p, 1 − p)`
of its mixing weights. Both sides are binary entropies — `S(ρ) = binEntropy ((1 + t)/2)` and
`H(p, 1 − p) = binEntropy p` with `t = √((1 − p)² + p²)` — and `binEntropy` is antitone on
`[1/2, 1]` (`Real.binEntropy_strictAntiOn`), so the claim follows from `|2p − 1| ≤ t`. -/
theorem vonNeumannEntropy_entropyComparisonState_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (entropyComparisonState p hp0 hp1).vonNeumannEntropy ≤ Real.entropy ![p, 1 - p] := by
  rw [vonNeumannEntropy_entropyComparisonState]
  refine Real.entropy_pair_le hp0 hp1
    (Real.sqrt_le_one.mpr (by nlinarith [mul_nonneg hp0 (by linarith : (0 : ℝ) ≤ 1 - p)])) ?_
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hp0 (by linarith : (0 : ℝ) ≤ 1 - p)])

/-- **N&C Exercise 11.12, the sharp comparison `S(ρ) < H(p, 1 − p)` for `0 < p < 1`.** Strictly
below the classical Shannon entropy: because `|0⟩` and `|+⟩` are non-orthogonal, mixing them loses
strictly less "information" than `H(p, 1 − p)`. The equality case `S(ρ) = H(p, 1 − p)` occurs only
at the endpoints `p ∈ {0, 1}` (where `ρ` is pure). Same route as the non-strict form, with the
strict `|2p − 1| < t` from `0 < 2p(1 − p)`. -/
theorem vonNeumannEntropy_entropyComparisonState_lt (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (entropyComparisonState p hp0.le hp1.le).vonNeumannEntropy < Real.entropy ![p, 1 - p] := by
  rw [vonNeumannEntropy_entropyComparisonState]
  refine Real.entropy_pair_lt hp0.le hp1.le
    (Real.sqrt_le_one.mpr (by nlinarith [mul_pos hp0 (by linarith : (0 : ℝ) < 1 - p)])) ?_
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _)
    (by nlinarith [mul_pos hp0 (by linarith : (0 : ℝ) < 1 - p)])

end AxQM
