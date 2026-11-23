/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Hadamard

/-!
# Nielsen & Chuang, Exercise 2.33

Show H^{tensor n} = (1/sqrt(2^n)) sum (-1)^{x.y} |x><y|; write out H^{tensor2}.

This is a pure statement about the real matrix `H` and its tensor powers — the closed form of
the entries of `H^{⊗n}`.

The formalisation is in `AxQM/Concrete/Hadamard.lean`:

* `AxQM.Concrete.hadamard` — the `2 × 2` Hadamard matrix `(√2)⁻¹ • !![1,1; 1,-1]`
  of eq. (2.54), with `AxQM.Concrete.hadamard_apply` giving its closed entry form
  `H a b = (√2)⁻¹ (-1)^{a b}` (so `H(0,0)=H(0,1)=H(1,0)=1/√2`, `H(1,1)=-1/√2`).
* `AxQM.Concrete.hadamardPow` — the `n`-fold tensor power `H^{⊗n}`, indexed by the
  `n`-bit strings `Fin n → Fin 2` and defined by the honest Kronecker block recursion; its
  identity as *the* tensor power is certified by `AxQM.Concrete.hadamardPow_apply`,
  the Kronecker-entry formula `H^{⊗n} x y = ∏ᵢ H (xᵢ) (yᵢ)`.
* `AxQM.Concrete.hadamardPow_apply_eq` — **eq. (2.55)**:
  `H^{⊗n} x y = (√(2ⁿ))⁻¹ (-1)^{∑ᵢ xᵢ yᵢ}`, where `∑ᵢ xᵢ yᵢ` is the bitwise dot product
  `x·y`. Proved, not assumed: the entry is the product `∏ᵢ H(xᵢ,yᵢ)` and the closed form
  follows by distributing the single-qubit formula over that product.
* `AxQM.Concrete.hadamardPow_two_submatrix` — the explicit `4 × 4` matrix for
  `H^{⊗2}` in N&C's big-endian basis order `00, 01, 10, 11`:
  `(1/2) !![1,1,1,1; 1,-1,1,-1; 1,1,-1,-1; 1,-1,-1,1]`.
-/
