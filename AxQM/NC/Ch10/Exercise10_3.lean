/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BitFlipSyndromeMeasurement

/-!
# Nielsen & Chuang, Exercise 10.3 — the bit-flip syndrome measured two ways

Measuring Z1Z2 then Z2Z3 equals measuring the four bit-flip projectors, same statistics and
post-states.

The three-qubit bit-flip code uses two equivalent descriptions of its syndrome measurement:

* **Two `±1` observable measurements**: measure `Z₁Z₂ = Z ⊗ Z ⊗ I`, then `Z₂Z₃ = I ⊗ Z ⊗ Z`
  (N&C eq. 10.12) — a *cascade* of two two-outcome projective measurements, with a joint outcome
  `(s₁, s₂) : Fin 2 × Fin 2`.
* **One four-outcome measurement**: measure the four bit-flip syndrome projectors
  `P₀ = |000⟩⟨000|+|111⟩⟨111|`, …, `P₃ = |001⟩⟨001|+|110⟩⟨110|` of N&C eqns (10.5)–(10.8).

"Up to labeling" is N&C's outcome dictionary `bitFlipRelabel`: `(+,+) ↦ 0` (no error),
`(−,+) ↦ 1` (qubit 1 flipped), `(−,−) ↦ 2` (qubit 2), `(+,−) ↦ 3` (qubit 3).

## This file

The two theorems below make "same statistics and post-measurement states" precise, in terms of
`Measurement.bornProb` (Born rule, Postulate 3) and `Measurement.postMeasurement` (collapse,
Postulate 4):

* `bitFlipSyndrome_bornProb_eq` — **same statistics**: for every state `ρ` and joint outcome `s`,
  the cascade's Born probability for `s` equals the four-projector measurement's Born probability
  for the relabeled outcome `bitFlipRelabel s`.
* `bitFlipSyndrome_postMeasurement_eq` — **same post-measurement states**: whenever the joint
  outcome `s` is possible, the two procedures collapse `ρ` to the *same* state.

Both are immediate from the operator identity `cascade_op_eq_syndromeProj` (the cascade's
measurement operator for outcome `s` **is** the syndrome projector `P_{bitFlipRelabel s}`, N&C's
"explicit calculation") via the general bridges `Measurement.bornProb_congr` /
`Measurement.postMeasurement_congr` (equal outcome operators ⇒ equal Born probabilities and
collapses). This is the exact content of the exercise: the two procedures are statistically and
dynamically indistinguishable, differing only in how outcomes are labeled.

### Where the constructions are

The constructions (`bitFlipReg`, the observables `Z₁Z₂`/`Z₂Z₃`, the sign-measurements
`bitFlipZ12Measurement`/`bitFlipZ23Measurement`, the syndrome projectors and their measurement
`bitFlipSyndromeMeasurement`, and the operator identity `cascade_op_eq_syndromeProj`) are in
`AxQM/Postulates/API/BitFlipSyndromeMeasurement.lean`. Compare the cascade construction of N&C
Exercise 2.57.

N&C Exercise 10.3, p. 430.
-/

noncomputable section

namespace AxQM

/-- **Exercise 10.3 — same measurement statistics.** Measuring `Z₁Z₂` then `Z₂Z₃` (the cascade
`bitFlipZ12Measurement.cascade bitFlipZ23Measurement`) assigns to the joint outcome `s : Fin 2 ×
Fin 2` exactly the Born probability that measuring the four syndrome projectors
(`bitFlipSyndromeMeasurement`) assigns to the relabeled outcome `bitFlipRelabel s`, for every state
`ρ`. Immediate from the operator identity `cascade_op_eq_syndromeProj` via
`Measurement.bornProb_congr`. -/
theorem bitFlipSyndrome_bornProb_eq (ρ : State bitFlipReg) (s : Fin 2 × Fin 2) :
    (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).bornProb ρ s
      = bitFlipSyndromeMeasurement.bornProb ρ (bitFlipRelabel s) :=
  Measurement.bornProb_congr (cascade_op_eq_syndromeProj s) ρ

/-- **Exercise 10.3 — same post-measurement states.** Whenever the joint outcome `s` of measuring
`Z₁Z₂` then `Z₂Z₃` is possible, the collapsed state (Postulate 4) equals the collapsed state of
measuring the four syndrome projectors for the relabeled outcome `bitFlipRelabel s`: the two
procedures update `ρ` identically. Immediate from `cascade_op_eq_syndromeProj` via
`Measurement.postMeasurement_congr`; the relabeled outcome is possible because it has the same Born
probability (`bitFlipSyndrome_bornProb_eq`). -/
theorem bitFlipSyndrome_postMeasurement_eq (ρ : State bitFlipReg) (s : Fin 2 × Fin 2)
    (hs : (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).bornProb ρ s ≠ 0) :
    (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).postMeasurement ρ s hs
      = bitFlipSyndromeMeasurement.postMeasurement ρ (bitFlipRelabel s)
          (by rw [← bitFlipSyndrome_bornProb_eq]; exact hs) :=
  Measurement.postMeasurement_congr (cascade_op_eq_syndromeProj s) ρ hs _

end AxQM
