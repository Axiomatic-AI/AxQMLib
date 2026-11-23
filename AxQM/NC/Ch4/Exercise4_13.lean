/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HadamardPauliConjugation

/-!
# Nielsen & Chuang, Exercise 4.13 (Circuit identities)

Prove the circuit identities HXH=Z, HYH=-Y, HZH=X.

Each identity is a fact of `2 × 2` complex linear algebra: an equality of concrete matrices — the
Hadamard matrix `hadamardC` conjugating a Pauli matrix `pauliX`/`pauliY`/`pauliZ`.

## The formalisation

The three identities are in `AxQM/Concrete/HadamardPauliConjugation.lean`, built on the
Hadamard matrix (`AxQM/Concrete/Hadamard.lean`) and the Pauli matrices
(`AxQM/Concrete/Pauli.lean`):

* `AxQM.Concrete.hadamardC_mul_pauliX_mul_hadamardC` — `H X H = Z`.
* `AxQM.Concrete.hadamardC_mul_pauliY_mul_hadamardC` — `H Y H = -Y`.
* `AxQM.Concrete.hadamardC_mul_pauliZ_mul_hadamardC` — `H Z H = X`.

Geometrically the Hadamard gate is the Bloch-sphere reflection that exchanges the `x̂` and `ẑ` axes
and flips `ŷ`; the three identities record its action on the Pauli operators. Each is proved by
collapsing the two Hadamard normalisation factors `(√2)⁻¹` to `2⁻¹` (`inv_sqrt_two_mul_self`) and
then checking the resulting `2 × 2` matrix equality entry by entry. `H Z H = X` is the Pauli-level
form of the rotation identity `hadamardC_mul_rotZ_mul_hadamardC` (`H R_z(θ) H = R_x(θ)`) used by
Exercise 4.10.
-/
