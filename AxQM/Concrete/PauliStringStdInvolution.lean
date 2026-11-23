/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCommutation

/-!
# Concrete: a standard-register Pauli string is an involution (`P_g² = I`)

The Pauli string `pauliStringStd g` on the flat computational-basis register `Fin (2ⁿ)` squares to
the identity. This is the standard-indexed analogue of `pauliString_mul_self` (`P_g · P_g = I` on
the bit-string indexing `Fin n → Fin 2`), transported along the reindexing equivalence
`finFunctionFinEquiv`.

It is the matrix half of the observation that **every honest (phase `+1`) `n`-qubit Pauli operator
is a self-adjoint involution** — Hermitian (`pauliStringStd_isHermitian`) and squaring to `I` —
hence a unitary with eigenvalues `±1`. Nielsen & Chuang use exactly this to feed a product of Pauli
operators to the operator-measurement circuit of Figure 10.13 ("`M` is an arbitrary Hermitian
operator with eigenvalues `±1`"); on the physics side it lets a Pauli-string observable be promoted
to an `Evolution` (a controllable unitary), which the stabilizer syndrome circuits of §10.5.8 need.

Everything is stated for raw matrix / index data (`Matrix`, `Concrete.pauliStringStd`,
`Fin n → Fin 4`).
-/

open scoped Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **A standard-register Pauli string is an involution**: `pauliStringStd g · pauliStringStd g =
I`. Since `pauliStringStd g = (pauliString g).submatrix e⁻¹ e⁻¹` for the reindexing equivalence
`e = finFunctionFinEquiv`, and reindexing by an equivalence is multiplicative
(`Matrix.submatrix_mul_equiv`) and sends `I` to `I` (`Matrix.submatrix_one_equiv`), this follows
from the bit-string form `pauliString_mul_self` (`P_g · P_g = I`). Each single-qubit Pauli squares
to `I` with trivial phase, so their tensor product does too. -/
theorem pauliStringStd_mul_self (g : Fin n → Fin 4) :
    pauliStringStd g * pauliStringStd g = 1 := by
  unfold pauliStringStd
  rw [Matrix.submatrix_mul_equiv, pauliString_mul_self, Matrix.submatrix_one_equiv]

end AxQM.Concrete
