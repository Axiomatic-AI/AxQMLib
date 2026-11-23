/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Fourier.ZModUnitary

/-!
# Nielsen & Chuang, Exercise 5.1 (Unitarity of the quantum Fourier transform)

Give a direct proof that the linear transformation defined by the QFT (5.2) is unitary.

The statement is pure linear algebra: the `N × N` discrete Fourier transform matrix is unitary.

N&C's QFT (5.2) is exactly the symmetrically normalized discrete Fourier transform: on the
computational basis `|0⟩, …, |N-1⟩` it acts by `|j⟩ ↦ N⁻¹ᐟ² ∑ₖ exp(2πijk/N) |k⟩`. Its matrix has
`(j,k)` entry `N⁻¹ᐟ² exp(2πijk/N)`. Indexing the basis by `ZMod N` makes the exponent `j·k`
well-defined modulo `N` and identifies `exp(2πi(j·k)/N)` with Mathlib's standard additive character
`ZMod.stdAddChar (j·k)`, so the "direct proof" reduces to the orthogonality of that character (the
geometric sum of `N`-th roots of unity), exactly the computation N&C has in mind.

The formalisation is in `ToMathlib/Analysis/Fourier/ZModUnitary.lean`:

* `ZMod.dftMatrix` — the QFT / normalized DFT matrix `Matrix (ZMod N) (ZMod N) ℂ`, with entry
  `(j,k) ↦ N⁻¹ᐟ² · ZMod.stdAddChar (j·k)`.
* `ZMod.sum_stdAddChar_mul` — the orthogonality relation `∑ₖ stdAddChar (m·k) = if m = 0 then N
  else 0`, the sum-of-roots-of-unity fact underlying the direct proof.
* `ZMod.dftMatrix_mem_unitaryGroup` — Exercise 5.1 itself: `ZMod.dftMatrix N` lies in
  `Matrix.unitaryGroup (ZMod N) ℂ`, i.e. it is unitary. The proof computes the `(j₁, j₂)` entry of
  `(dftMatrix N)ᴴ * dftMatrix N` as `N⁻¹ ∑ₖ exp(2πi k (j₂ - j₁)/N)`, which is `1` on the diagonal
  and `0` off it by `sum_stdAddChar_mul`.
-/
