/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TotalAngularMomentumTwoQubit

/-!
# Nielsen & Chuang, Exercise 7.25 (Total angular momenta obey the SU(2) relations)

Show total angular momenta operators obey SU(2) relations [j_i,j_k]=iε_{ikl}j_l.

Here (N&C p. 314) the total operators are `jₓ = (X₁ + X₂)/2`, `j_y = (Y₁ + Y₂)/2`,
`j_z = (Z₁ + Z₂)/2`, built from the Pauli operators on the two qubits of a two-spin register.

The statement is a commutator identity between concrete `4 × 4` complex matrices (Kronecker
products of the Pauli matrices). Compare its single-qubit ancestor, the Pauli commutation relations
`pauliSigma_lie` of Ex. 2.40.

The formalisation is in `AxQM/Concrete/TotalAngularMomentumTwoQubit.lean`:

* `AxQM.Concrete.totalSpin` — the two-qubit total angular momentum operators
  `jᵢ = (σᵢ ⊗ I + I ⊗ σᵢ)/2` (`totalSpin 0/1/2 = jₓ/j_y/j_z`).
* `AxQM.Concrete.totalSpin_lie` — the exercise's claim, the SU(2) relation
  `⁅jⱼ, jₖ⁆ = i Σₗ ε_{jkl} jₗ`, for all `j, k : Fin 3`.
* `AxQM.Concrete.totalSpin_lie_xy` / `_yz` / `_zx` — the three explicit cyclic instances
  `⁅jₓ, j_y⁆ = i j_z`, `⁅j_y, j_z⁆ = i jₓ`, `⁅j_z, jₓ⁆ = i j_y`.

The general supporting lemmas (Kronecker distribution over subtraction/sums and the
commutator-lift lemmas `Matrix.lie_kronecker_one`, …) are in
`ToMathlib/LinearAlgebra/Matrix/KroneckerCommutator.lean`; the Pauli-specific `sigmaKronSum_lie`,
`totalSpin`, and the SU(2) theorems are in the file above.
-/
