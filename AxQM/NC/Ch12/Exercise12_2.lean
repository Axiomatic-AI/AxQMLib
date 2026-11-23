/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HolevoMeasurementChannel

/-!
# Nielsen & Chuang, Exercise 12.2 (the Holevo measurement operation `𝓔`)

*(N&C p. 533.)*

Show {sqrt(E_y) tensor U_y} defines a trace-preserving quantum operation matching (12.8).

This is the construction used in the proof of the Holevo bound (Theorem 12.1). The system `Q` is the
quantum system Alice gives Bob; `M` is Bob's measuring apparatus, with an orthonormal basis `|y⟩`
labelled by the measurement outcomes and initialised in the standard state `|0⟩`. The operation `𝓔`
performs a measurement with POVM elements `{E_y}` on `Q` and stores the outcome in `M`:

  `𝓔(σ ⊗ |0⟩⟨0|) = ∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`   (Nielsen & Chuang, Eq. (12.8)).

The operation elements `√E_y ⊗ U_y` are built from the measurement operators `M_y`
(`Measurement.op`), the tensor of operators (`TensorProduct.mapL`), the operator square root, and
the operator-sum map `krausSumₗ`; (12.8) is an operator identity `∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`.

## The formalisation

The formalisation is in `AxQM/Postulates/API/HolevoMeasurementChannel.lean`. The
measurement is `Measurement (Fin r) Q` (Postulate 3; `r = n + 1` outcomes),
whose induced POVM has effects `E_y = M_y† M_y`, so the positive square root `√E_y = |M_y|` is the
absolute value of `M_y`. The apparatus `M` is `qudit r` with cyclic shift `U_y = periodShift r y`
(`U_y|0⟩ = |y⟩`).

* `AxQM.holevoMeasurementKraus` — the **operation element** `√E_y ⊗ U_y` of outcome `y` on
  `Q ⊗ M`.
* `AxQM.holevoMeasurementKraus_completeness` — **the trace-preservation / completeness
  relation** `∑_y (√E_y ⊗ U_y)† (√E_y ⊗ U_y) = 1`: the elements define a trace-preserving operation.
* `AxQM.holevoMeasurementChannel` — the operation `𝓔` as a state-map, with
  `AxQM.holevoMeasurementChannel_isChannel` proving it is a genuine CPTP quantum channel
  (`IsChannel`).
* `AxQM.holevoMeasurementChannel_apply_tmul` — **agreement with Eq. (12.8):**
  `𝓔(σ ⊗ |0⟩⟨0|) = ∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`.

The statement is over an arbitrary system `Q`, an arbitrary measurement on it (arbitrary outcome
count `r = n + 1`), and an arbitrary state `σ`, with the right-hand side in N&C's literal Eq. (12.8)
shape — a faithful, unweakened rendering of the exercise.
-/
