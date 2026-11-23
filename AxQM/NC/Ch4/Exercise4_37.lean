/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QFTTwoLevel

/-!
# Nielsen & Chuang, Exercise 4.37

Decompose the 4x4 QFT-like matrix into a product of two-level unitaries.

The statement is a fact about the concrete 4×4 complex matrix `F` (`Fⱼₖ = ½ iʲᵏ`, the `N = 4`
discrete Fourier transform) and a family of concrete 2×2-block matrices in `Matrix.unitaryGroup`.

## The formalisation

The formalisation is in `AxQM/Concrete/QFTTwoLevel.lean`:

* `AxQM.Concrete.IsTwoLevelUnitary` — the predicate "`U` is a two-level unitary": unitary
  and agreeing with the identity outside a single `{p,q} × {p,q}` principal submatrix (so it acts
  non-trivially on at most two computational basis vectors). Stated for general dimension `d`.
* `AxQM.Concrete.qftFour` — the transform `F` of eq. (4.52),
  `½ • !![1,1,1,1; 1,i,-1,-i; 1,-1,1,-1; 1,-i,-1,i]`.
* `AxQM.Concrete.qftFactorH02`, `qftFactorG13`, `qftFactorH01`, `qftFactorH23`,
  `qftFactorSwap` — the five two-level factors: the Hadamard block `(√2)⁻¹ !![1,1; 1,-1]` on the
  coordinate pairs `{0,2}`, `{0,1}`, `{2,3}`, the twiddled block `(√2)⁻¹ !![1,i; 1,-i]` on `{1,3}`,
  and the transposition of `{1,2}`. Each is certified a two-level unitary by
  `qftFactorH02_isTwoLevelUnitary`, `qftFactorG13_isTwoLevelUnitary`,
  `qftFactorH01_isTwoLevelUnitary`, `qftFactorH23_isTwoLevelUnitary`,
  `qftFactorSwap_isTwoLevelUnitary`.
* `AxQM.Concrete.qftFour_eq_prod` — **the exercise**: `F = qftFactorH02 · qftFactorG13 ·
  qftFactorH01 · qftFactorH23 · qftFactorSwap`, obtained from the radix-2 (Cooley–Tukey)
  factorisation of the DFT, whose sparse layers each split into two disjoint two-level blocks.
* `AxQM.Concrete.qftFour_mem_unitaryGroup` — a corollary: `F` is unitary, being a product
  of the five two-level unitaries.

The five-factor construction is an explicit *existence* proof, independent of the general §4.5.1
two-level decomposition algorithm; it exploits the special structure of the QFT.
-/
