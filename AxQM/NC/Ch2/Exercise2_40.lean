/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliCommutator

/-!
# Nielsen & Chuang, Exercise 2.40 (Commutation relations for the Pauli matrices)

Verify commutation relations [X,Y]=2iZ etc for the Pauli matrices.

The statement is pure `2 × 2` complex-matrix arithmetic: the
commutators `AB − BA` of the concrete Pauli matrices `X`, `Y`, `Z`, using the matrices (`pauliX`,
`pauliY`, `pauliZ`) and Mathlib's ring/Lie structure on `Matrix (Fin 2) (Fin 2) ℂ`.

The formalisation is in `AxQM/Concrete/PauliCommutator.lean`, built on the Pauli-matrix definitions
of `AxQM/Concrete/Pauli.lean`:

* `AxQM.Concrete.pauliSigma_lie` — the elegant tensor form (eq. 2.74):
  `⁅σⱼ, σₖ⁆ = 2i Σₗ ε_{jkl} σₗ`, where `⁅·,·⁆` is the matrix commutator `AB − BA`
  (`Ring.lie_def`) — exactly N&C's `[·,·]`.
* `AxQM.Concrete.pauliX_lie_pauliY` — `[X, Y] = 2iZ` (eq. 2.73).
* `AxQM.Concrete.pauliY_lie_pauliZ` — `[Y, Z] = 2iX` (eq. 2.73).
* `AxQM.Concrete.pauliZ_lie_pauliX` — `[Z, X] = 2iY` (eq. 2.73).

The three explicit relations are the cyclic instances of the general tensor form. The Levi-Civita
symbol `ε` is formalised as `AxQM.Concrete.leviCivita3` and the uniform index family
`σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ` as `AxQM.Concrete.pauliSigma`; both are `0`-based,
so `pauliSigma i` is N&C's `σ_{i+1}` and `leviCivita3 j k l` is N&C's `ε_{(j+1)(k+1)(l+1)}` — a
faithful reindexing that preserves the full antisymmetric structure.
-/
