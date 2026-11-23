/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.AmplitudeDampingChannel
import AxQM.Postulates.API.BlochHSOverlap
import AxQM.NC.Ch2.Exercise2_72
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 10.13 (Minimum fidelity of the amplitude-damping channel)

Min fidelity F(|psi>,E(|psi><psi|)) for amplitude damping channel parameter gamma is sqrt(1-gamma).

Here `E` is the single-qubit **amplitude-damping channel** of §8.3.5 (eq. 10.46),
`E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` with operation elements `E₀ = diag(1, √(1-γ))` and `E₁ = √γ |0⟩⟨1|`.
It is the grounded `State qubit → State qubit` map `AxQM.amplitudeDampingChannel`, built in
`AxQM/Postulates/API/AmplitudeDampingChannel.lean`.

## The computation

Unlike the depolarizing channel of Exercise 10.12 — which is isotropic, so the fidelity is a
*constant* across pure inputs — amplitude damping is **not** unital, and the fidelity genuinely
depends on the input state. Its Bloch action is the *affine* map
`r⃗ ↦ (√(1-γ) r₀, √(1-γ) r₁, (1-γ) r₂ + γ)` (`amplitudeDampingChannel_apply_blochState`), so the
minimum is a genuine attained minimum, not a symmetry-forced constant.

For a **pure** input `|ψ⟩ = blochState r⃗` (`‖r⃗‖ = 1`), the squared fidelity is the Hilbert–Schmidt
overlap of the two Bloch states (`State.fidelity_toState_sq_eq_hsOverlap`, `blochState_hsOverlap`),
`F(|ψ⟩, E(|ψ⟩⟨ψ|))² = ½(1 + r⃗ · s⃗)` with `s⃗` the affine transform of `r⃗`
(`amplitudeDampingChannel_fidelity_sq_pure`). Writing `z = r₂` and `‖r⃗‖ = 1` (so `r₀² + r₁² =
1 - z²`), this is `½(1 + √(1-γ)(1 - z²) + (1-γ)z² + γz)`, a function of the longitudinal component
`z ∈ [-1, 1]` alone.

The excess over the claimed minimum factors cleanly:
`F² − (1 − γ) = ½ (z + 1)(1 − √(1-γ))(1 + 2√(1-γ) − √(1-γ) z)`, a product of three nonnegative
factors on `z ∈ [-1, 1]` (`amplitudeDampingChannel_fidelity_ge`). Hence `F(|ψ⟩, E(|ψ⟩⟨ψ|)) ≥
√(1 − γ)` for **every** pure `|ψ⟩`, with equality exactly at `z = -1` — the excited state `|1⟩`
(Bloch point `(0, 0, -1)`, `qubitBasis_one_blochVector`), whose fidelity is `√(1 − γ)`
(`amplitudeDampingChannel_fidelity_excitedState`). The two facts assemble to
`amplitudeDampingChannel_isLeast_fidelity`: `√(1 − γ)` is the `IsLeast` of the set of per-state
fidelities.

Physically: amplitude damping decays the excited state `|1⟩` toward the ground state `|0⟩`, so `|1⟩`
is the *worst-case* input (its density operator is moved the most), while `|0⟩` — the fixed point —
has fidelity `1`. The minimum `√(1 − γ)` is attained at `|1⟩`.

## Design decisions

* **A genuine attained minimum, not a constant.** Because the channel is non-unital, the honest
  formal content of "the minimum fidelity is `√(1 − γ)`" is an `IsLeast`: membership witnessed by
  the excited state `|1⟩` (`amplitudeDampingChannel_fidelity_excitedState`) and a lower bound
  `F(|ψ⟩) ≥ √(1 − γ)` holding for every pure `|ψ⟩` (`amplitudeDampingChannel_fidelity_ge`). This is
  the substantive difference from Exercise 10.12, where `IsLeast` collapses to a single constant.
* **The lower bound by a nonnegative factorization.** `2(F² − (1 − γ)) =
  (z + 1)(1 − √(1-γ))(1 + 2√(1-γ) − √(1-γ)z)` with `z = r₂ ∈ [-1, 1]`; all three factors are `≥ 0`
  (`z + 1 ≥ 0`, `√(1-γ) ≤ 1`, and `1 + 2√(1-γ) − √(1-γ)z ≥ 1 + √(1-γ) ≥ 0` since `z ≤ 1`), so
  `F² ≥ 1 − γ`, and `F ≥ √(1 − γ)` by monotonicity of `√·`. The concavity argument N&C alludes to,
  made a single `nlinarith` product certificate.
* **Ingredients.** The proof rests on `State.fidelity_toState_sq_eq_hsOverlap` and
  `blochState_hsOverlap` (in `AxQM/Postulates/API/BlochHSOverlap.lean`) and on the channel with its
  affine Bloch action `amplitudeDampingChannel_apply_blochState` (in
  `AxQM/Postulates/API/AmplitudeDampingChannel.lean`).

N&C Exercise 10.13, p. 443.
-/

open Matrix

noncomputable section

namespace AxQM

/-- **The squared per-state fidelity of the amplitude-damping channel** (Nielsen & Chuang,
Exercise 10.13). For a pure state `|ψ⟩ = blochState r⃗` (any `r⃗` in the closed unit ball) and
`0 ≤ γ ≤ 1`,
`F(|ψ⟩, E(|ψ⟩⟨ψ|))² = ½(1 + √(1-γ)(r₀² + r₁²) + ((1-γ)r₂ + γ)r₂)`.

Proof: `State.fidelity_toState_sq_eq_hsOverlap` turns the squared fidelity into the Hilbert–Schmidt
overlap `F² = (blochState r⃗).hsOverlap (E (blochState r⃗))`; the channel's affine Bloch action
`amplitudeDampingChannel_apply_blochState` rewrites `E(blochState r⃗) =
blochState (√(1-γ)r₀, √(1-γ)r₁, (1-γ)r₂ + γ)`; and `blochState_hsOverlap` evaluates the overlap of
two Bloch states as `½(1 + r⃗ · s⃗)`. -/
theorem amplitudeDampingChannel_fidelity_sq_pure (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (ψ : PureState qubit) (r : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
    (hρ : ψ.toState = blochState r hr) :
    (ψ.toState.fidelity (amplitudeDampingChannel γ h0 h1 ψ.toState)) ^ 2
      = (1 + (Real.sqrt (1 - γ) * (r 0 ^ 2 + r 1 ^ 2) + ((1 - γ) * r 2 + γ) * r 2)) / 2 := by
  rw [State.fidelity_toState_sq_eq_hsOverlap, hρ, amplitudeDampingChannel_apply_blochState,
    blochState_hsOverlap]
  simp only [Concrete.ampDampBlochVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The lower bound: every pure input has fidelity at least `√(1 − γ)`** (Nielsen & Chuang,
Exercise 10.13). For every pure qubit state `|ψ⟩` and `0 ≤ γ ≤ 1`,
`√(1 − γ) ≤ F(|ψ⟩, E(|ψ⟩⟨ψ|))`.

Writing `|ψ⟩ = blochState r⃗` with `‖r⃗‖ = 1` (`State.exists_blochState`,
`blochState_isPure_iff_norm_one`) and `z = r₂ ∈ [-1, 1]`, the squared fidelity
(`amplitudeDampingChannel_fidelity_sq_pure`) exceeds `1 − γ` by
`½(z + 1)(1 − √(1-γ))(1 + 2√(1-γ) − √(1-γ)z) ≥ 0` (a product of three nonnegative factors, using
`√(1-γ)² = 1 - γ`); hence `F² ≥ 1 − γ` and `F ≥ √(1 − γ)` by monotonicity of `√·`. -/
theorem amplitudeDampingChannel_fidelity_ge (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (ψ : PureState qubit) :
    Real.sqrt (1 - γ) ≤ ψ.toState.fidelity (amplitudeDampingChannel γ h0 h1 ψ.toState) := by
  obtain ⟨r, hr, hρ⟩ := ψ.toState.exists_blochState
  have hnorm : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 :=
    (blochState_isPure_iff_norm_one r hr).mp (hρ ▸ ⟨ψ, rfl⟩)
  have hsq := amplitudeDampingChannel_fidelity_sq_pure γ h0 h1 ψ r hr hρ
  set s := Real.sqrt (1 - γ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - γ := Real.sq_sqrt (by linarith)
  have hs1 : s ≤ 1 := by nlinarith [hs2, hs0]
  have hz1 : r 2 ≤ 1 := by nlinarith [hnorm, sq_nonneg (r 0), sq_nonneg (r 1), sq_nonneg (r 2 - 1)]
  have hz2 : -1 ≤ r 2 := by nlinarith [hnorm, sq_nonneg (r 0), sq_nonneg (r 1), sq_nonneg (r 2 + 1)]
  have hbound : 1 - γ ≤ (ψ.toState.fidelity (amplitudeDampingChannel γ h0 h1 ψ.toState)) ^ 2 := by
    rw [hsq]
    have hsum : r 0 ^ 2 + r 1 ^ 2 = 1 - r 2 ^ 2 := by linarith
    rw [hsum]
    have hprod : 0 ≤ (r 2 + 1) * ((1 - s) * (1 + 2 * s - s * r 2)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith)
        (by nlinarith [mul_nonneg hs0 (show (0 : ℝ) ≤ 1 - r 2 by linarith)]))
    nlinarith [hprod, hs2]
  calc Real.sqrt (1 - γ)
      ≤ Real.sqrt ((ψ.toState.fidelity (amplitudeDampingChannel γ h0 h1 ψ.toState)) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = ψ.toState.fidelity (amplitudeDampingChannel γ h0 h1 ψ.toState) :=
        Real.sqrt_sq (State.fidelity_nonneg _ _)

/-- **The minimum is attained at the excited state `|1⟩`** (Nielsen & Chuang, Exercise 10.13). The
fidelity between `|1⟩` and `E(|1⟩⟨1|)` for the amplitude-damping channel is exactly `√(1 − γ)`.

The excited state `|1⟩ = qubitBasis 1` has Bloch point `(0, 0, -1)` (`qubitBasis_one_blochVector`),
so its squared fidelity (`amplitudeDampingChannel_fidelity_sq_pure` at `r⃗ = (0,0,-1)`) is
`½(1 + √(1-γ)·0 + ((1-γ)(-1) + γ)(-1)) = ½(1 + (1 - 2γ)) = 1 − γ`; being nonnegative, the fidelity
is `√(1 − γ)`. Physically, `|1⟩` is the worst-case input for amplitude damping — the state whose
density operator is displaced the most toward the fixed ground state `|0⟩`. -/
theorem amplitudeDampingChannel_fidelity_excitedState (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (qubitBasis 1).toState.fidelity (amplitudeDampingChannel γ h0 h1 (qubitBasis 1).toState)
      = Real.sqrt (1 - γ) := by
  have hsq := amplitudeDampingChannel_fidelity_sq_pure γ h0 h1 (qubitBasis 1) ![0, 0, -1]
    (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) qubitBasis_one_blochVector
  have hval : (qubitBasis 1).toState.fidelity
      (amplitudeDampingChannel γ h0 h1 (qubitBasis 1).toState) ^ 2 = 1 - γ := by
    rw [hsq]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    ring
  rw [← hval, Real.sqrt_sq (State.fidelity_nonneg _ _)]

/-- **Nielsen & Chuang, Exercise 10.13.** `√(1 − γ)` is the **minimum** fidelity of the
amplitude-damping channel over pure input states: it is the `IsLeast` of the set of per-state
fidelities `{F | ∃ ψ, F(|ψ⟩, E(|ψ⟩⟨ψ|)) = F}`.

Membership is witnessed by the excited state `|1⟩`, at which the fidelity equals `√(1 − γ)`
(`amplitudeDampingChannel_fidelity_excitedState`); the lower bound is the per-state estimate
`√(1 − γ) ≤ F(|ψ⟩, E(|ψ⟩⟨ψ|))` for every pure `|ψ⟩` (`amplitudeDampingChannel_fidelity_ge`).
Together they make N&C's claim precise: the least achievable fidelity is `√(1 − γ)`, and it is
genuinely attained (at `|1⟩`), the channel being non-unital rather than isotropic. -/
theorem amplitudeDampingChannel_isLeast_fidelity (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsLeast {F : ℝ | ∃ ψ : PureState qubit,
        ψ.toState.fidelity (amplitudeDampingChannel γ h0 h1 ψ.toState) = F}
      (Real.sqrt (1 - γ)) := by
  refine ⟨⟨qubitBasis 1, amplitudeDampingChannel_fidelity_excitedState γ h0 h1⟩, ?_⟩
  rintro F ⟨ψ, rfl⟩
  exact amplitudeDampingChannel_fidelity_ge γ h0 h1 ψ

end AxQM
