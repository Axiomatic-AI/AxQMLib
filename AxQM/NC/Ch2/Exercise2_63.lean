/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementPolar

/-!
# Nielsen & Chuang, Exercise 2.63

Show measurement operators M_m = U_m sqrt(E_m) for some unitaries U_m.

Here `Eₘ ≡ Mₘ† Mₘ` (Nielsen–Chuang eq. (2.117)) and `√Eₘ` is the positive operator square root of
the positive operator `Eₘ`. The claim is exactly the **left polar decomposition**
`Mₘ = Uₘ |Mₘ|` applied to each measurement operator, together with `|Mₘ| = √(Mₘ† Mₘ) = √Eₘ`.

A measurement (Postulate 3 / §2.2.3) is a `Measurement`, and `Eₘ = Mₘ† Mₘ` is its induced POVM
(`Measurement.toPOVM`). The exercise's assertion is an *operator equation* relating the measurement
operator `Mₘ`, its POVM element `Eₘ`, and a unitary `Uₘ`; weakening it to "the same statistics as
the canonical `{√Eₘ}` measurement" would be a strictly weaker claim. So the formalisation uses the
measurement operator `Measurement.op` and names `unitary (S →L[ℂ] S)`, `POVM.elements` and `cfc`.

The formalisation is in `AxQM/Postulates/API/MeasurementPolar.lean`:

* `AxQM.Measurement.exists_unitary_op_eq_comp_sqrt_toPOVM_elements` — for a measurement
  `m : Measurement ι S` and outcome `i`, there is a unitary `U` with
  `m.op i = U ∘L √(m.toPOVM.elements i)`, i.e. `Mᵢ = Uᵢ √Eᵢ`.

**Fidelity note.** The statement is proved at full generality: any measurement `m` on any system
`S`, and every outcome `i` (no invertibility or nondegeneracy hypothesis on `Mᵢ`). The unitary is
supplied by the existence-of-polar-unitary theorem
`ContinuousLinearMap.exists_mem_unitary_eq_comp_absoluteValue`, whose construction extends the
partial isometry `polarPart` (defined on `range |Mᵢ|`) to a genuine unitary of the whole space —
exactly the freedom N&C's `Uₘ` enjoys where `√Eₘ` has a nontrivial kernel.
-/
