/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GeneralizedDepolarizingChannel
import AxQM.Core.StrictContraction
import AxQM.NC.Ch9.Exercise9_6

/-!
# Nielsen & Chuang, Exercise 9.12 (The depolarizing channel is strictly contractive)

For depolarizing channel, find D(E(rho),E(sigma)) via Bloch and prove strict contractivity.

## The computation

Every qubit state has a Bloch representation `ρ = ½(I + r⃗·σ)` (`State.exists_blochState`, N&C Ex
2.72(1)). The depolarizing channel `E(ρ) = p(I/2) + (1−p)ρ` acts on the Bloch vector by a *uniform
shrink*:
`E(½(I + r⃗·σ)) = p(I/2) + (1−p)½(I + r⃗·σ) = ½(I + (1−p) r⃗·σ)`,
i.e. `r⃗ ↦ (1−p) r⃗` (`qubitDepolarizingChannel_blochState`). Since the qubit trace distance is
half the Euclidean Bloch distance, `D(ρ, σ) = ‖r⃗ − s⃗‖/2` (`blochState_traceDistance`, N&C
`(9.20)`, Ex 9.6), the channel scales *every* trace distance by exactly `1 − p`:
`D(E(ρ), E(σ)) = ‖(1−p) r⃗ − (1−p) s⃗‖/2 = (1−p) ‖r⃗ − s⃗‖/2 = (1−p) D(ρ, σ)`
(`qubitDepolarizingChannel_traceDistance`). This is the answer N&C asks us to *find* using the Bloch
representation.

Strict contraction is then immediate for `0 < p ≤ 1`: for distinct `ρ ≠ σ` the trace distance is
positive (`D(ρ, σ) = 0 ↔ ρ = σ`, `State.traceDistance_eq_zero_iff`), and multiplying a positive
number by `1 − p < 1` strictly decreases it: `D(E(ρ), E(σ)) = (1−p) D(ρ, σ) < D(ρ, σ)`
(`qubitDepolarizingChannel_strictlyContractive`, the `StrictlyContractive` predicate of Ex 9.10).

## Design decisions

* **Reuse of the one depolarizing-channel object.** `E` is taken to be the generalized depolarizing
  channel `genDepolarizingChannel` (N&C §8.3.4 eq. 8.106, Exercise 8.19) specialized to `d = 2`; at
  `d = 2` its defining operator `(1−p) ρ + p (I/2)` is *exactly* N&C's eq. 8.100 `E(ρ) = pI/2 +
  (1−p)ρ` (`qubit` and `qudit 2` are the same system `EuclideanSpace ℂ (Fin 2)`). No second channel
  object is introduced — `qubitDepolarizingChannel` is a thin `State qubit → State qubit`
  specialization so the Bloch machinery (all native to `qubit`) applies directly.
* **Faithful generality.** The trace-distance identity holds for *arbitrary* qubit states `ρ, σ`
  (not just a chosen pair), matching "for arbitrary `ρ` and `σ`". Strict contraction uses only the
  physical range `0 < p ≤ 1` (`p > 0` is exactly what makes `1 − p < 1`; `p = 0` is the identity,
  which is contractive but not strictly so).
* N&C Exercise 9.12, p. 409.
-/

open Matrix

noncomputable section

namespace AxQM

/-- **The qubit depolarizing channel** `E(ρ) = p (I/2) + (1 − p) ρ` (Nielsen & Chuang eq. 8.100, the
depolarizing channel of §8.3.4). It is the generalized depolarizing channel `genDepolarizingChannel`
specialized to the qubit `d = 2`: with probability `p` the state is replaced by the maximally mixed
state `I/2`, and left untouched otherwise. For `0 ≤ p ≤ 1` this is a genuine `State qubit → State
qubit` map. -/
def qubitDepolarizingChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit → State qubit :=
  genDepolarizingChannel 2 p hp0 hp1

/-- **The depolarizing channel shrinks the Bloch vector by `1 − p`.** Applied to the Bloch state
`ρ = ½(I + r⃗·σ)`, the channel returns `½(I + (1−p) r⃗·σ) = blochState ((1−p) r⃗)`:
`p(I/2) + (1−p)½(I + r⃗·σ) = ½(I + (1−p) r⃗·σ)`.

Proved at the operator level: the channel's operator is `(1−p) blochMatrix r + p (I/2)`, and since
`I/2 = blochMatrix 0`, the two-point convexity identity `blochMatrix_convex` (with `(1−p) + p = 1`)
collapses it to `blochMatrix ((1−p) r⃗ + p·0) = blochMatrix ((1−p) r⃗)`. -/
theorem qubitDepolarizingChannel_blochState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : Fin 3 → ℝ)
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    qubitDepolarizingChannel p hp0 hp1 (blochState r h)
      = blochState ((1 - p) • r) (Concrete.sq_sum_smul_le_one h (by linarith) (by linarith)) := by
  have hmix : (maximallyMixedState qubit).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix 0) := by
    change (maximallyMixedState (qudit 2)).op = _
    rw [maximallyMixedState_op, finrank_qudit, Concrete.blochMatrix_zero, map_smul, map_one]
    congr 1
  have hconv : Concrete.blochMatrix ((1 - p) • r)
      = ((1 - p : ℝ) : ℂ) • Concrete.blochMatrix r + ((p : ℝ) : ℂ) • Concrete.blochMatrix 0 := by
    rw [Concrete.blochMatrix_convex r 0 (by ring : (1 - p) + p = 1), smul_zero, add_zero]
  apply State.ext
  have hLHS : (qubitDepolarizingChannel p hp0 hp1 (blochState r h)).op
      = ((1 - p : ℝ) : ℂ) • (blochState r h).op
        + ((p : ℝ) : ℂ) • (maximallyMixedState qubit).op :=
    rfl
  rw [hLHS, blochState_op, hmix, blochState_op, hconv, map_add, map_smul, map_smul]
  rfl

/-- **The Bloch-explicit trace distance under the depolarizing channel** (Nielsen & Chuang Ex 9.12,
"find `D(E(ρ), E(σ))` using the Bloch representation"). For Bloch states with vectors `r⃗, s⃗`,
`D(E(ρ), E(σ)) = (1 − p) · ‖r⃗ − s⃗‖/2`: the channel shrinks both Bloch vectors by `1 − p`, so the
Euclidean Bloch distance — hence the trace distance — scales by `|1 − p| = 1 − p`. -/
theorem qubitDepolarizingChannel_blochState_traceDistance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r s : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
    (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 ≤ 1) :
    (qubitDepolarizingChannel p hp0 hp1 (blochState r hr)).traceDistance
        (qubitDepolarizingChannel p hp0 hp1 (blochState s hs))
      = (1 - p) * (Real.sqrt ((r 0 - s 0) ^ 2 + (r 1 - s 1) ^ 2 + (r 2 - s 2) ^ 2) / 2) := by
  rw [qubitDepolarizingChannel_blochState, qubitDepolarizingChannel_blochState,
    blochState_traceDistance]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show ((1 - p) * r 0 - (1 - p) * s 0) ^ 2 + ((1 - p) * r 1 - (1 - p) * s 1) ^ 2
        + ((1 - p) * r 2 - (1 - p) * s 2) ^ 2
        = (1 - p) ^ 2 * ((r 0 - s 0) ^ 2 + (r 1 - s 1) ^ 2 + (r 2 - s 2) ^ 2) from by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
  ring

/-- **Nielsen & Chuang, Exercise 9.12 (the trace distance under the depolarizing channel).** For
*arbitrary* qubit states `ρ` and `σ`, the depolarizing channel scales the trace distance by exactly
`1 − p`:
`D(E(ρ), E(σ)) = (1 − p) D(ρ, σ)`.
Obtained by writing `ρ, σ` in Bloch form (`State.exists_blochState`) and applying the Bloch-explicit
computation together with `D(ρ, σ) = ‖r⃗ − s⃗‖/2`. This is the closed form N&C asks us to *find*. -/
theorem qubitDepolarizingChannel_traceDistance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ σ : State qubit) :
    (qubitDepolarizingChannel p hp0 hp1 ρ).traceDistance (qubitDepolarizingChannel p hp0 hp1 σ)
      = (1 - p) * ρ.traceDistance σ := by
  obtain ⟨r, hr, rfl⟩ := ρ.exists_blochState
  obtain ⟨s, hs, rfl⟩ := σ.exists_blochState
  rw [qubitDepolarizingChannel_blochState_traceDistance, blochState_traceDistance]

/-- **Nielsen & Chuang, Exercise 9.12 (strict contractivity).** For `0 < p ≤ 1` the depolarizing
channel `E(ρ) = p(I/2) + (1 − p)ρ` is *strictly contractive*: `D(E(ρ), E(σ)) < D(ρ, σ)` for every
pair of distinct states `ρ ≠ σ`.

Proof: `D(E(ρ), E(σ)) = (1 − p) D(ρ, σ)` (`qubitDepolarizingChannel_traceDistance`), and for `ρ ≠ σ`
the trace distance is positive — `D(ρ, σ) = 0 ↔ ρ = σ` (`State.traceDistance_eq_zero_iff`) together
with `0 ≤ D(ρ, σ)` (`State.traceDistance_nonneg`) — so multiplying it by `1 − p < 1` (using `0 < p`)
strictly decreases it. Combined with Exercise 9.10 (a strictly contractive map has a unique fixed
point) and Exercise 9.9 (existence), `E` therefore has a unique fixed point — the maximally mixed
state `I/2`. -/
theorem qubitDepolarizingChannel_strictlyContractive (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 0 < p) : StrictlyContractive (qubitDepolarizingChannel p hp0 hp1) := by
  intro ρ σ hne
  have hd : 0 < ρ.traceDistance σ :=
    lt_of_le_of_ne (State.traceDistance_nonneg ρ σ)
      (fun h => hne ((State.traceDistance_eq_zero_iff ρ σ).mp h.symm))
  rw [qubitDepolarizingChannel_traceDistance]
  nlinarith [mul_pos hp hd, hd]

end AxQM
