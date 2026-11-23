/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliOuterProduct

/-!
# Nielsen & Chuang, Exercise 2.9 (Pauli operators and the outer product)

Express each Pauli matrix in the outer product notation.

The outer product `|i⟩⟨j|` is the operator `|v'⟩ ↦ ⟨j|v'⟩ |i⟩` (N&C eq. (2.20));
the coefficient of `|a⟩⟨b|` in an operator's outer-product expansion is its
`(a, b)` matrix element (eq. (2.25)). With the computational basis, reading the
Pauli matrices of Figure 2.2 entrywise gives
`I = |0⟩⟨0| + |1⟩⟨1|`, `X = |0⟩⟨1| + |1⟩⟨0|`,
`Y = -i|0⟩⟨1| + i|1⟩⟨0|`, and `Z = |0⟩⟨0| - |1⟩⟨1|`.

The formalisation is in `AxQM/Concrete/PauliOuterProduct.lean`
(the Pauli matrices `pauliX/pauliY/pauliZ` are reused from
`AxQM/Concrete/Pauli.lean`):

* `AxQM.Concrete.pauliI` — the fourth Pauli operator `σ₀ = I` (the `2 × 2`
  identity), completing the `{I, X, Y, Z}` of Figure 2.2.
* `AxQM.Concrete.ket` — the computational-basis kets `|0⟩, |1⟩`.
* `AxQM.Concrete.ketBra` — the outer product `|i⟩⟨j|` as a matrix
  (`vecMulVec |i⟩ (star |j⟩)`), with `ketBra_apply` (its entries) and
  `ketBra_eq_single` (it is the matrix unit `single i j 1`).
* `AxQM.Concrete.pauliI_eq_ketBra`, `AxQM.Concrete.pauliX_eq_ketBra`,
  `AxQM.Concrete.pauliY_eq_ketBra`, `AxQM.Concrete.pauliZ_eq_ketBra` —
  the four outer-product expansions the exercise asks for.
-/
