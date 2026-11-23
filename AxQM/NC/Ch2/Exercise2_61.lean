/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliMeasurement

/-!
# Nielsen & Chuang, Exercise 2.61 (measurement of `v · σ` on `|0⟩`)

Probability of +1 for measurement of v.sigma given state |0>; post-measurement state.

Here `v` is a real three-dimensional **unit** vector and `v · σ = v₁X + v₂Y + v₃Z` is the spin
observable of §2.2.5 (eq. 2.116). Measuring it is the projective measurement whose operators are the
eigenprojectors `P± = (I ± v·σ)/2` of Exercise 2.60. By the Born rule and Postulate 4:

* **Probability of `+1`:** `p(+1) = ⟨0| P₊ |0⟩ = (1 + ⟨0|v·σ|0⟩)/2 = (1 + v₃)/2`, since only the `Z`
  component of `v·σ` survives on `|0⟩` (`⟨0|X|0⟩ = ⟨0|Y|0⟩ = 0`, `⟨0|Z|0⟩ = 1`).
* **Post-measurement state:** when `+1` is obtained, the state collapses to the normalized
  `P₊|0⟩ / ‖P₊|0⟩‖`, which is the `+1` eigenstate of `v·σ`.

The item is stated with `Measurement.bornProb` (Postulate 3, the Born rule) and
`Measurement.postMeasurement` (Postulate 4, collapse).

* `pauliVecMeasurement` — the projective measurement of `v·σ` (Exercise 2.60's
  eigenprojectors `P±` as measurement operators), a two-outcome `Measurement (Fin 2) qubit`.
* `pauliVecMeasurement_bornProb_qubitKet0_zero` — the probability of `+1` on `|0⟩` is `(1 + v₃)/2`.
* `pauliVecMeasurement_postMeasurement_qubitKet0_zero` — the post-measurement state after `+1` is
  the normalized `P₊|0⟩` (Exercise 2.61's collapsed state).

The `|0⟩` state `qubitKet0`, the `±1`-observable eigenprojectors
`Observable.projPlus`/`projMinus`, the involution measurement `Observable.signMeasurement` with the
general Born-rule and collapse identities, and the expectation `⟨0|v·σ|0⟩ = v₃`
(`pauliObservable_expectation_qubitKet0`) are in `AxQM/Postulates/API/PauliMeasurement.lean`.
-/

namespace AxQM

/-- The **projective measurement of the spin observable `v · σ`** on the qubit, for a real unit
vector `v` (Nielsen & Chuang §2.2.5, Exercises 2.60–2.61): the two-outcome measurement whose
operators are the eigenprojectors `P± = (I ± v·σ)/2` (outcome `0 ↔ +1`, `1 ↔ −1`). The unit-vector
hypothesis makes `(v·σ)² = I`, so the `P±` are genuine orthogonal projectors. -/
noncomputable def pauliVecMeasurement (n : Fin 3 → ℝ) (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    Measurement (Fin 2) qubit :=
  (pauliObservable n).signMeasurement (pauliObservable_op_mul_self h)

/-- **Nielsen & Chuang, Exercise 2.61 (probability of `+1`).** For a real unit vector `v`, the
probability of obtaining `+1` when measuring `v · σ` on the state `|0⟩` is `(1 + v₃)/2`
(here `v₃ = n 2`). The `Z`-component alone contributes because `⟨0|X|0⟩ = ⟨0|Y|0⟩ = 0` and
`⟨0|Z|0⟩ = 1`. The probability is `Measurement.bornProb` (Postulate 3, the Born rule). -/
theorem pauliVecMeasurement_bornProb_qubitKet0_zero (n : Fin 3 → ℝ)
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    (pauliVecMeasurement n h).bornProb qubitKet0.toState 0 = (1 + n 2) / 2 := by
  rw [pauliVecMeasurement, Observable.bornProb_signMeasurement_plus,
    pauliObservable_expectation_qubitKet0]

/-- **Nielsen & Chuang, Exercise 2.61 (post-measurement state).** If the `+1` outcome is obtained —
a possible outcome, `hp : p(+1) ≠ 0`, i.e. `v₃ ≠ −1` — the qubit collapses to the normalized state
`P₊|0⟩ / ‖P₊|0⟩‖`, the `+1` eigenstate of `v · σ`. Stated over the `Measurement.postMeasurement`
generator (Postulate 4, state update / collapse). -/
theorem pauliVecMeasurement_postMeasurement_qubitKet0_zero (n : Fin 3 → ℝ)
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hp : (pauliVecMeasurement n h).bornProb qubitKet0.toState 0 ≠ 0) :
    (pauliVecMeasurement n h).postMeasurement qubitKet0.toState 0 hp
      = ((pauliObservable n).postMeasPlus qubitKet0
          ((pauliObservable n).projPlus_apply_ne_zero_of_bornProb
            (pauliObservable_op_mul_self h) qubitKet0 hp)).toState :=
  (pauliObservable n).postMeasurement_signMeasurement_plus (pauliObservable_op_mul_self h)
    qubitKet0 _ hp

end AxQM
