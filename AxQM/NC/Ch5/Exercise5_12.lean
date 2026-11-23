/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ModularMultiplication

/-!
# Nielsen & Chuang, Exercise 5.12

Show that U|y>=|xy mod N> is unitary (x coprime to N has inverse mod N).

Here `U` is the order-finding operator `U|y⟩ = |xy (mod N)⟩` (Eq. 5.36, §5.3.1, p. 227), acting on
the `L`-qubit register `y ∈ {0,1}^L = {0, …, 2ᴸ - 1}`, with N&C's convention that `U` fixes `y` when
`N ≤ y ≤ 2ᴸ - 1`.

The unitarity of `U` is a purely mathematical fact: because `x` is co-prime to `N` it is a unit in
`ZMod N`, so `y ↦ xy (mod N)` is a bijection of the residues `{0, …, N - 1}`; extended by the
identity on `{N, …, 2ᴸ - 1}` it is a permutation of the register, and `U` is its permutation
matrix — which is always unitary.

The formalisation is in `AxQM/Concrete/ModularMultiplication.lean`:

* `AxQM.Concrete.modMulPerm` — the operator `U` as a permutation of the register `Fin d`
  (any `d ≥ N`; N&C's case is `d = 2ᴸ`), with `modMulPerm_apply_of_lt` / `modMulPerm_apply_of_le`
  fixing its action `y ↦ xy (mod N)` on residues and the identity on `y ≥ N`.
* `AxQM.Concrete.modMulMatrix` — `U` as the permutation matrix of `modMulPerm` over `ℂ`.
* `AxQM.Concrete.modMulMatrix_mem_unitaryGroup` — **Exercise 5.12**: `U` is unitary
  (`U ∈ Matrix.unitaryGroup (Fin d) ℂ`); `modMulMatrix_two_pow_mem_unitaryGroup` specialises it to
  N&C's `d = 2ᴸ` register.
-/
