/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliCommutator

/-!
# Nielsen & Chuang, Exercise 2.43 (Full multiplication relation for the Pauli matrices)

Show sigma_j sigma_k = delta_jk I + i sum eps_jkl sigma_l.

The statement is `2 × 2` complex-matrix arithmetic: the products `σⱼ σₖ` of the Pauli matrices
`X`, `Y`, `Z` (`pauliSigma`), expressed via the Kronecker delta `δ_{jk}` and the antisymmetric
tensor `ε_{jkl}` (`leviCivita3`).

## The declaration

The formalisation is in `AxQM/Concrete/PauliCommutator.lean`, alongside the commutation relation
`pauliSigma_lie` of Exercise 2.40 (both are built on the Pauli-matrix definitions of
`AxQM/Concrete/Pauli.lean`):

* `AxQM.Concrete.pauliSigma_mul` — the full multiplication relation (eq. 2.78):
  `σⱼ σₖ = δ_{jk} I + i Σₗ ε_{jkl} σₗ`, with `δ_{jk}` the Kronecker delta
  (`if j = k then 1 else 0`) and `I` the `2 × 2` identity matrix.

## Notes

This is the most fundamental of Chapter 2's Pauli-algebra relations: its symmetric part is the
anticommutator content `{σⱼ, σₖ} = 2 δ_{jk} I` (Exercise 2.41, eqs. 2.75–2.76) and its
antisymmetric part is the commutator content `[σⱼ, σₖ] = 2i Σₗ ε_{jkl} σₗ` (Exercise 2.40,
eq. 2.74) — the decomposition `AB = ([A, B] + {A, B}) / 2` of Exercise 2.42. Both `pauliSigma_lie`
and the anticommutation relations are therefore corollaries of `pauliSigma_mul`. They are proved
independently in the library (`pauliSigma_lie`, `pauli_anticomm`), so `pauliSigma_mul` is stated as
its own claim here rather than re-derived from them.

The index convention matches `pauliSigma`/`leviCivita3`: `Fin 3` is `0`-based, so `pauliSigma i` is
N&C's `σ_{i+1}` and `leviCivita3 j k l` is N&C's `ε_{(j+1)(k+1)(l+1)}` — a faithful reindexing that
preserves the full antisymmetric structure, universally quantified over all `j, k : Fin 3` (i.e.
N&C's `j, k ∈ {1, 2, 3}`), with no added hypotheses.
-/
