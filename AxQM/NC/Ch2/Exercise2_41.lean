/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli

/-!
# Nielsen & Chuang, Exercise 2.41 (Anti-commutation relations for the Pauli matrices)

Verify anti-commutation relations {sigma_i,sigma_j}=0 and sigma_i^2=I.

Both relations are pure `2 × 2` complex-matrix arithmetic on the Pauli matrices `X`, `Y`, `Z`
(with `σ₀ = I`); the anticommutator is `{A, B} = A B + B A`.

## The formalisation

All in `AxQM/Concrete/Pauli.lean`.

The **anticommutation relations** `{σᵢ, σⱼ} = 0` (eq. 2.75), for the three distinct pairs drawn
from `{1, 2, 3} = {X, Y, Z}`:

* `AxQM.Concrete.pauliX_anticomm_pauliY` — `X Y + Y X = 0`.
* `AxQM.Concrete.pauliY_anticomm_pauliZ` — `Y Z + Z Y = 0`.
* `AxQM.Concrete.pauliX_anticomm_pauliZ` — `X Z + Z X = 0`.

Each is a direct entrywise computation (`X Y = diag(i, -i)`, `Y X = diag(-i, i)`, and likewise
for the other pairs), so the two orders cancel. Since the anticommutator is symmetric in its
arguments, these three unordered pairs are exactly the content of eq. 2.75.

The **involution property** `σᵢ² = I` (eq. 2.76) for all four indices `i = 0, 1, 2, 3`, stated
uniformly over the indexed family `AxQM.Concrete.pauli : Fin 4 → M₂(ℂ)` (N&C's
`σ₀ = I`, `σ₁ = X`, `σ₂ = Y`, `σ₃ = Z`):

* `AxQM.Concrete.pauli_mul_self` — `σᵢ² = I` for every `i : Fin 4`; the `i = 1, 2, 3`
  cases reduce to the per-matrix involutions `pauliX_mul_self`, `pauliY_mul_self`,
  `pauliZ_mul_self`, and `i = 0` to `I² = I`.

Both relations are also packaged in indexed form to mirror N&C's own quantified statements:

* `AxQM.Concrete.pauli_anticomm` — `σᵢ σⱼ + σⱼ σᵢ = 0` for distinct `i, j ≠ 0` (the
  non-zero indices of `Fin 4` being exactly N&C's `{1, 2, 3}`). The identity `σ₀ = I` is excluded
  because `{I, σ} = 2σ ≠ 0`, matching the exercise's restriction to `i, j ∈ {1, 2, 3}`.
-/
