/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch8.Problem8_3
import AxQM.NC.Ch2.Exercise2_72
import AxQM.Postulates.API.BlochHSOverlap
import AxQM.Postulates.API.Qubit

/-!
# Nielsen & Chuang, Exercise 10.12 (Fidelity for the depolarizing channel; minimum fidelity)

Fidelity between |0> and E(|0><0|) for depolarizing channel is sqrt(1-2p/3); min fidelity argument.

Here `E` is the single-qubit **depolarizing channel** of §10.3.2 (eq. 10.42),
`E(ρ) = (1 − p)ρ + (p/3)(XρX + YρY + ZρZ)`: nothing happens with probability `1 − p`, and each of
`X, Y, Z` is applied with probability `p/3`.

## The computation

The channel is the qubit **Pauli channel** `∑ₖ pₖ σₖ ρ σₖ` (`AxQM.pauliChannel`, Problem
8.3) with the weight distribution `![1 − p, p/3, p/3, p/3]` over `I, X, Y, Z`; it is thereby a
genuine CPTP map (`pauliDepolarizingChannel_isChannel`). Its Bloch action is the **isotropic
shrink** `r⃗ ↦ (1 − 4p/3) r⃗` (`pauliDepolarizingChannel_apply_blochState`): the Pauli-transfer
coefficients are all `mₓ = m_y = m_z = (1−p) + p/3 − p/3 − p/3 = 1 − 4p/3`.

For a **pure** input `|ψ⟩ = blochState r⃗` (`‖r⃗‖ = 1`), the squared fidelity is the Hilbert–Schmidt
overlap of the two Bloch states (`State.fidelity_toState_sq_eq_hsOverlap`, `blochState_hsOverlap`):
`F(|ψ⟩, E(|ψ⟩⟨ψ|))² = ½(1 + r⃗·(1−4p/3)r⃗) = ½(1 + (1−4p/3)‖r⃗‖²) = ½(1 + (1−4p/3)) = 1 − 2p/3`,
**independent of `|ψ⟩`**. Hence `F(|ψ⟩, E(|ψ⟩⟨ψ|)) = √(1 − 2p/3)` for every pure state
(`pauliDepolarizingChannel_fidelity_pure`); the `|0⟩` case is the special instance
`pauliDepolarizingChannel_fidelity_ket0`.

Because the per-state fidelity is the *same constant* for all pure inputs, the minimum over pure
states is that constant: `√(1 − 2p/3)` is the least achievable fidelity
(`pauliDepolarizingChannel_isLeast_fidelity`, `IsLeast`). This is precisely the symmetry argument
N&C invokes ("use this to argue the minimum fidelity is `√(1 − 2p/3)`") — the depolarizing channel
is isotropic, so no input state does worse (or better) than `|0⟩`.

## Design decisions

* **The faithful Pauli parametrization.** `E` is defined with N&C's §10.3.2 form
  `(1−p)ρ + (p/3)(XρX+YρY+ZρZ)` via `pauliChannel ![1−p, p/3, p/3, p/3]`, which is valid for the
  full physical range `0 ≤ p ≤ 1`. On trace-one states this coincides with the maximally-mixing
  form `(1 − 4p/3)ρ + (2p/3)I`, i.e. `qubitDepolarizingChannel (4p/3)` (Exercise 9.12) — but only
  where the latter is defined (`4p/3 ≤ 1`, i.e. `p ≤ 3/4`); the Pauli form is used precisely so the
  statement is faithful for **all** `p ∈ [0,1]`, not a `p ≤ 3/4` weakening.
* **The minimum via constancy, not an infimum estimate.** The fidelity is genuinely constant across
  pure inputs (the isotropy of the depolarizing channel), so `IsLeast` is discharged by the single
  per-state value `pauliDepolarizingChannel_fidelity_pure` — membership at `|0⟩` and the lower
  bound (an equality) for every state. This is the honest formal content of N&C's symmetry argument.
* **Ingredients.** The overlap identities the proof rests on are
  `State.fidelity_toState_sq_eq_hsOverlap` and `blochState_hsOverlap` (in
  `AxQM/Postulates/API/BlochHSOverlap.lean`) and `Concrete.blochMatrix_mul_trace` (in
  `AxQM/Concrete/BlochMatrixMulTrace.lean`).

N&C Exercise 10.12, p. 441.
-/

open Matrix

noncomputable section

namespace AxQM

/-- The depolarizing weights `![1 − p, p/3, p/3, p/3]` over `I, X, Y, Z` are **nonnegative**, for
`0 ≤ p ≤ 1`: `1 − p ≥ 0` and `p/3 ≥ 0`. -/
theorem depolarizingProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i, 0 ≤ (![1 - p, p / 3, p / 3, p / 3] : Fin 4 → ℝ) i := by
  intro i
  fin_cases i <;> simp <;> linarith

/-- The depolarizing weights `![1 − p, p/3, p/3, p/3]` **sum to one**:
`(1 − p) + p/3 + p/3 + p/3 = 1`. -/
theorem depolarizingProb_sum (p : ℝ) :
    ∑ i, (![1 - p, p / 3, p / 3, p / 3] : Fin 4 → ℝ) i = 1 := by
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  ring

/-- **The single-qubit depolarizing channel** `E(ρ) = (1 − p)ρ + (p/3)(XρX + YρY + ZρZ)` (Nielsen &
Chuang §10.3.2, eq. 10.42), for depolarizing probability `0 ≤ p ≤ 1`. Realised as the qubit Pauli
channel (`AxQM.pauliChannel`, Problem 8.3) with the weight distribution
`![1 − p, p/3, p/3, p/3]` over the Paulis `I, X, Y, Z`: identity with probability `1 − p`, and each
of `X, Y, Z` with probability `p/3`. (Distinct from the maximally-mixing form
`qubitDepolarizingChannel` of Exercise 9.12, with which it agrees on states only when `p ≤ 3/4`.) -/
def pauliDepolarizingChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit → State qubit :=
  (pauliChannel ![1 - p, p / 3, p / 3, p / 3] (depolarizingProb_nonneg hp0 hp1)
    (depolarizingProb_sum p)).apply

/-- **The depolarizing channel is a genuine CPTP quantum channel** (`IsChannel`), being a
random-unitary Pauli channel (`pauliChannel_isChannel`). -/
theorem pauliDepolarizingChannel_isChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsChannel (pauliDepolarizingChannel p hp0 hp1) :=
  pauliChannel_isChannel _ _ _

/-- **The Pauli-transfer vector of the depolarizing channel is the isotropic shrink**
`r⃗ ↦ (1 − 4p/3) r⃗`. Each transfer coefficient `mⱼ = ∑ₖ ±pₖ` of the weights
`![1 − p, p/3, p/3, p/3]` equals `(1 − p) + p/3 − p/3 − p/3 = 1 − 4p/3`, since the three
off-identity weights are all `p/3`; so the diagonal contraction is the same `1 − 4p/3` on every
axis. -/
theorem pauliTwirlVec_pauliDepolarizing (p : ℝ) (r : Fin 3 → ℝ) :
    Concrete.pauliTwirlVec ![1 - p, p / 3, p / 3, p / 3] r
      = ![(1 - 4 * p / 3) * r 0, (1 - 4 * p / 3) * r 1, (1 - 4 * p / 3) * r 2] := by
  funext i
  fin_cases i <;>
    simp only [Concrete.pauliTwirlVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] <;> ring_nf

/-- **The shrunk Bloch vector `(1 − 4p/3) r⃗` stays in the closed unit ball**, for `0 ≤ p ≤ 1`:
`‖(1 − 4p/3) r⃗‖² = (1 − 4p/3)² ‖r⃗‖² ≤ (1 − 4p/3)² ≤ 1`, using `|1 − 4p/3| ≤ 1` (which holds since
`0 ≤ p ≤ 3/2`). Stated on the explicit shrunk components `(1 − 4p/3) rⱼ`. -/
private theorem sq_sum_depolShrink_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {r : Fin 3 → ℝ}
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    (![(1 - 4 * p / 3) * r 0, (1 - 4 * p / 3) * r 1, (1 - 4 * p / 3) * r 2] : Fin 3 → ℝ) 0 ^ 2
        + (![(1 - 4 * p / 3) * r 0, (1 - 4 * p / 3) * r 1, (1 - 4 * p / 3) * r 2] : Fin 3 → ℝ) 1 ^ 2
        + (![(1 - 4 * p / 3) * r 0, (1 - 4 * p / 3) * r 1, (1 - 4 * p / 3) * r 2] : Fin 3 → ℝ) 2 ^ 2
      ≤ 1 := by
  have hc : (1 - 4 * p / 3) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hp0 (show (0 : ℝ) ≤ 3 - 2 * p by linarith)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  nlinarith [h, hc, sq_nonneg (1 - 4 * p / 3)]

/-- **The Bloch action of the depolarizing channel is the isotropic shrink**
`blochState r⃗ ↦ blochState ((1 − 4p/3) r⃗)`: the channel scales every Bloch vector by the single
factor `1 − 4p/3`. Immediate from the Pauli channel's Bloch action
(`pauliChannel_apply_blochState`) and the transfer coefficients
`pauliTwirlVec_pauliDepolarizing`. -/
theorem pauliDepolarizingChannel_apply_blochState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    pauliDepolarizingChannel p hp0 hp1 (blochState r h)
      = blochState ![(1 - 4 * p / 3) * r 0, (1 - 4 * p / 3) * r 1, (1 - 4 * p / 3) * r 2]
          (sq_sum_depolShrink_le hp0 hp1 h) := by
  rw [pauliDepolarizingChannel, pauliChannel_apply_blochState]
  exact blochState_congr (pauliTwirlVec_pauliDepolarizing p r)

/-- **The per-state fidelity of the depolarizing channel is the constant `√(1 − 2p/3)`** (Nielsen &
Chuang, Exercise 10.12, general case). For *every* pure qubit state `|ψ⟩`,
`F(|ψ⟩, E(|ψ⟩⟨ψ|)) = √(1 − 2p/3)`.

Writing `|ψ⟩ = blochState r⃗` with `‖r⃗‖ = 1` (`State.exists_blochState`,
`blochState_isPure_iff_norm_one`), the squared fidelity is the Hilbert–Schmidt overlap
`F² = ½(1 + r⃗·(1−4p/3)r⃗) = ½(1 + (1−4p/3)) = 1 − 2p/3` (`State.fidelity_toState_sq_eq_hsOverlap`,
`pauliDepolarizingChannel_apply_blochState`, `blochState_hsOverlap`), independent of `r⃗`. Since the
fidelity is nonnegative, `F = √(1 − 2p/3)`. -/
theorem pauliDepolarizingChannel_fidelity_pure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ψ : PureState qubit) :
    ψ.toState.fidelity (pauliDepolarizingChannel p hp0 hp1 ψ.toState)
      = Real.sqrt (1 - 2 * p / 3) := by
  obtain ⟨r, hr, hρ⟩ := ψ.toState.exists_blochState
  have hnorm : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 :=
    (blochState_isPure_iff_norm_one r hr).mp (hρ ▸ ⟨ψ, rfl⟩)
  have hsq : (ψ.toState.fidelity (pauliDepolarizingChannel p hp0 hp1 ψ.toState)) ^ 2
      = 1 - 2 * p / 3 := by
    rw [State.fidelity_toState_sq_eq_hsOverlap, hρ, pauliDepolarizingChannel_apply_blochState,
      blochState_hsOverlap]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    linear_combination ((1 - 4 * p / 3) / 2) * hnorm
  rw [← hsq, Real.sqrt_sq (State.fidelity_nonneg _ _)]

/-- **Nielsen & Chuang, Exercise 10.12 (the `|0⟩` case).** The fidelity between `|0⟩` and
`E(|0⟩⟨0|)` for the depolarizing channel is `√(1 − 2p/3)`. The stated special case of
`pauliDepolarizingChannel_fidelity_pure` at the computational basis state `|0⟩ = qubitBasis 0`. -/
theorem pauliDepolarizingChannel_fidelity_ket0 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qubitBasis 0).toState.fidelity (pauliDepolarizingChannel p hp0 hp1 (qubitBasis 0).toState)
      = Real.sqrt (1 - 2 * p / 3) :=
  pauliDepolarizingChannel_fidelity_pure p hp0 hp1 (qubitBasis 0)

/-- **Nielsen & Chuang, Exercise 10.12 (the minimum fidelity).** `√(1 − 2p/3)` is the *minimum*
fidelity of the depolarizing channel over pure input states: it is `IsLeast` of the set of
per-state fidelities `{F | ∃ ψ, F(|ψ⟩, E(|ψ⟩⟨ψ|)) = F}`.

This is N&C's symmetry argument made precise: the fidelity is the *same constant* `√(1 − 2p/3)` for
every pure input (`pauliDepolarizingChannel_fidelity_pure`, the isotropy of the depolarizing
channel), so `√(1 − 2p/3)` both belongs to the set (witnessed by `|0⟩`) and lower-bounds it (as an
equality for every state). -/
theorem pauliDepolarizingChannel_isLeast_fidelity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsLeast {F : ℝ | ∃ ψ : PureState qubit,
        ψ.toState.fidelity (pauliDepolarizingChannel p hp0 hp1 ψ.toState) = F}
      (Real.sqrt (1 - 2 * p / 3)) := by
  refine ⟨⟨qubitBasis 0, pauliDepolarizingChannel_fidelity_pure p hp0 hp1 (qubitBasis 0)⟩, ?_⟩
  rintro F ⟨ψ, rfl⟩
  exact (pauliDepolarizingChannel_fidelity_pure p hp0 hp1 ψ).ge

end AxQM
