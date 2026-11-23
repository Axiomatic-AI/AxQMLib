/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementOperation

/-!
# Nielsen & Chuang, Exercise 8.2 (Measurement as a quantum operation)

*(N&C p. 357.)*

Show measurement outcome state is E_m(ρ)/tr(E_m(ρ)) with p(m)=tr(E_m(ρ)) for E_m(ρ)=M_mρM_m†.

The exercise identifies the two outputs of the measurement postulate (Postulate 3,
`Measurement.bornProb`; Postulate 4, `Measurement.postMeasurement`) with the operator-sum
quantities built from `Eₘ(ρ) = Mₘ ρ Mₘ†`. That construction uses the measurement operators `Mₘ`
(`Measurement.op`), operator conjugation, and the operator trace.

## The formalisation

The formalisation lives in `AxQM/Postulates/API/MeasurementOperation.lean`:

* `AxQM.Measurement.opElement` — the **quantum operation element** `Eₘ(ρ) = Mₘ ρ Mₘ†` of
  outcome `i`, with `opElement_isPositive` (it is a positive, subnormalized density operator).
* `AxQM.Measurement.bornProb_eq_trace_opElement` — **the probability claim:**
  `p(m) = tr(Eₘ(ρ))`, as the complex equality `(p(m) : ℂ) = tr(Eₘ(ρ))` (so the trace is real and
  equals the Born probability).
* `AxQM.Measurement.postMeasurement_op_eq_opElement_div` — **the state-update claim, N&C
  Eq. (8.5):** the post-measurement state is `Eₘ(ρ)/tr(Eₘ(ρ))`, with
  `postMeasurement_op_eq_bornProb_smul_opElement` giving the physical `Eₘ(ρ)/p(m)` reading.

The probability claim is stated in the stronger complex form `(p(m) : ℂ) = tr(Eₘ(ρ))` rather than
`p(m) = re tr(Eₘ(ρ))`, and the state-update claim in N&C's literal `Eₘ(ρ)/tr(Eₘ(ρ))` form, over an
arbitrary measurement, state, and outcome — a faithful, unweakened rendering of the exercise. See
the module docstring there for the full argument.
-/
