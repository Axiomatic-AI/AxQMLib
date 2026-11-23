/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli

/-!
# Nielsen & Chuang, Exercise 2.19

Show the Pauli matrices are Hermitian and unitary.

The formalisation is in `AxQM/Concrete/Pauli.lean`:

* `AxQM.Concrete.pauliX_isHermitian`, `pauliY_isHermitian`, `pauliZ_isHermitian`
  — each Pauli matrix satisfies `σᴴ = σ` (`Matrix.IsHermitian`), N&C's Hermiticity `A† = A`.
* `AxQM.Concrete.pauliX_mem_unitaryGroup`, `pauliY_mem_unitaryGroup`,
  `pauliZ_mem_unitaryGroup` — each Pauli matrix is unitary, stated as membership in
  `Matrix.unitaryGroup (Fin 2) ℂ`, which unfolds (via `Matrix.mem_unitaryGroup_iff'`) to
  exactly N&C's `σᴴ σ = I`.
* `AxQM.Concrete.pauliX_mul_self`, `pauliY_mul_self`, `pauliZ_mul_self` — the
  supporting involution facts `σ² = I` from which unitarity follows once `σᴴ = σ`.

The fourth Pauli matrix `σ₀ = I` (`AxQM.Concrete.pauliI = 1`) is trivially both
Hermitian and unitary via Mathlib's `Matrix.isHermitian_one` and the `unitary` structure on
`1`, so it needs no dedicated theorem here.
-/
