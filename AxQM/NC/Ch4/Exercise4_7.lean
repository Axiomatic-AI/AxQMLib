/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationConjugation

/-!
# Nielsen & Chuang, Exercise 4.7 — `XYX = -Y` and `X R_y(θ) X = R_y(-θ)`

*(N&C p. 175.)*

Show XYX=-Y and use it to prove X R_y(theta) X = R_y(-theta).

The formalisation is in `AxQM/Concrete/RotationConjugation.lean`:

* `AxQM.Concrete.pauliX_mul_pauliY_mul_pauliX` — `X Y X = -Y` (the first part).
* `AxQM.Concrete.pauliX_mul_rotY_mul_pauliX` — `X R_y(θ) X = R_y(-θ)` (the second part).

The reason both hold: conjugation by `X` fixes `X` but negates every Pauli matrix that
anticommutes with it, so it flips the sign of the `Y` component of `R_y(θ) = cos(θ/2) I −
i sin(θ/2) Y`, i.e. sends `θ ↦ −θ`.

That file additionally proves the `Z`-analogues `pauliX_mul_pauliZ_mul_pauliX` (`X Z X = -Z`) and
`pauliX_mul_rotZ_mul_pauliX` (`X R_z(θ) X = R_z(-θ)`), which are not part of this exercise but are
the shared prerequisite for the ABC decomposition (N&C Corollary 4.2), where the two `X` gates are
moved through the middle rotation using exactly these conjugation identities.
-/
