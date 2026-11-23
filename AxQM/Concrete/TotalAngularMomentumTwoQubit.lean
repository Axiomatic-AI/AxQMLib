/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliCommutator
import ToMathlib.LinearAlgebra.Matrix.KroneckerCommutator

/-!
# Concrete: two-qubit total angular momentum obeys the SU(2) relations (N&C Ex. 7.25)

This file verifies Nielsen & Chuang,
Exercise 7.25 (p. 314), over the concrete `4 × 4` complex matrices built as Kronecker products
of the Pauli matrices `pauliSigma` from `AxQM.Concrete.PauliCommutator`, as its single-qubit
ancestor `pauliSigma_lie` (Ex. 2.40) does.

## The exercise

N&C (p. 314) forms, from two spin-1/2 spins, the **total angular momentum operators**

`jₓ = (X₁ + X₂)/2,   j_y = (Y₁ + Y₂)/2,   j_z = (Z₁ + Z₂)/2`,

where `Xₐ, Yₐ, Zₐ` are the Pauli operators acting on qubit `a ∈ {1, 2}` of the two-qubit register,
i.e. `X₁ = X ⊗ I`, `X₂ = I ⊗ X`, and similarly for `Y, Z`. Exercise 7.25 asks to show that these
obey the commutation relations for `SU(2)`, `[jᵢ, jₖ] = i ε_{ikl} jₗ` (Einstein summation over `l`).

## The formalisation

* `totalSpin i = (σᵢ ⊗ I + I ⊗ σᵢ)/2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` — the operator
  `jᵢ` (`totalSpin 0 = jₓ`, `totalSpin 1 = j_y`, `totalSpin 2 = j_z`), where the two-qubit space is
  `Fin 2 × Fin 2` and `⊗ₖ` (`Matrix.kroneckerMap (· * ·)`) is the tensor product.
* `totalSpin_lie` — the SU(2) relation `⁅jⱼ, jₖ⁆ = i Σₗ ε_{jkl} jₗ`, the faithful statement of the
  exercise for all `j, k : Fin 3` (the diagonal `j = k` and the anticyclic instances are included,
  since `ε` vanishes / changes sign accordingly).
* `totalSpin_lie_xy`, `totalSpin_lie_yz`, `totalSpin_lie_zx` — the three explicit cyclic instances
  `⁅jₓ, j_y⁆ = i j_z`, `⁅j_y, j_z⁆ = i jₓ`, `⁅j_z, jₓ⁆ = i j_y`.

## Proof strategy

The commutator is bilinear and the Pauli relations are already available in the elegant tensor form
`pauliSigma_lie` (`⁅σⱼ, σₖ⁆ = 2i Σₗ ε_{jkl} σₗ`). Writing `Aᵢ = σᵢ ⊗ I` and `Bᵢ = I ⊗ σᵢ`, the two
copies each reproduce the Pauli algebra and commute with one another — the general, Pauli-free facts
`Matrix.lie_kronecker_one`, `Matrix.one_kronecker_lie` (each embedding carries the commutator) and
`Matrix.lie_kronecker_one_one_kronecker`, `Matrix.one_kronecker_lie_kronecker_one` (cross
commutators vanish), together with the Kronecker distribution laws, all in
`ToMathlib/LinearAlgebra/Matrix/KroneckerCommutator.lean`.

Expanding `⁅A_j + B_j, A_k + B_k⁆` bilinearly (`add_lie`/`lie_add`), the cross terms drop, the
diagonal terms give `(2i Σₗ ε σₗ) ⊗ I + I ⊗ (2i Σₗ ε σₗ)`, and pushing `⊗` through the scalar and
the finite sum recovers `2i Σₗ ε (σₗ ⊗ I + I ⊗ σₗ)` (`sigmaKronSum_lie`). The overall `1/2` in
each `jᵢ` turns the `2i` into the `i` of the SU(2) relation.

## Index convention

As in `pauliSigma_lie`, `Fin 3` is `0`-based: `pauliSigma i` is N&C's `σ_{i+1}` and
`leviCivita3 j k l` is N&C's `ε_{(j+1)(k+1)(l+1)}`. This is a faithful reindexing of the fully
antisymmetric structure, not a weakening.
-/

namespace AxQM.Concrete

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix Complex
open scoped Kronecker

/-- The **unnormalized** total operators `σᵢ ⊗ I + I ⊗ σᵢ` (i.e. `2 jᵢ`) obey the raised commutation
relation `⁅Sⱼ, Sₖ⁆ = 2i Σₗ ε_{jkl} Sₗ`, the direct sum of the two commuting Pauli algebras. This is
the workhorse behind `totalSpin_lie`; the `1/2` normalization is applied afterwards. -/
theorem sigmaKronSum_lie (j k : Fin 3) :
    ⁅pauliSigma j ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliSigma j,
      pauliSigma k ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliSigma k⁆
      = (2 * I) • ∑ l, (leviCivita3 j k l : ℂ) •
          (pauliSigma l ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
            + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliSigma l) := by
  rw [add_lie, lie_add, lie_add, Matrix.lie_kronecker_one, Matrix.one_kronecker_lie,
    Matrix.lie_kronecker_one_one_kronecker, Matrix.one_kronecker_lie_kronecker_one,
    add_zero, zero_add, pauliSigma_lie]
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.sum_kronecker,
    Matrix.kronecker_sum, smul_add, Finset.smul_sum, Finset.sum_add_distrib]

/-- The **two-qubit total angular momentum operators** `jᵢ = (σᵢ ⊗ I + I ⊗ σᵢ)/2` (Nielsen & Chuang,
p. 314): `totalSpin 0 = jₓ = (X₁ + X₂)/2`, `totalSpin 1 = j_y = (Y₁ + Y₂)/2`,
`totalSpin 2 = j_z = (Z₁ + Z₂)/2`, on the two-qubit space `Fin 2 × Fin 2`. -/
noncomputable def totalSpin (i : Fin 3) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauliSigma i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliSigma i)

/-- **Exercise 7.25**: the two-qubit total angular momentum operators obey the commutation relations
for `SU(2)`, `⁅jⱼ, jₖ⁆ = i Σₗ ε_{jkl} jₗ` — Nielsen & Chuang's `[jᵢ, jₖ] = i ε_{ikl} jₗ`. Holds for
all `j, k : Fin 3`: the diagonal case is `0 = 0` and the anticyclic cases carry the sign of `ε`. -/
theorem totalSpin_lie (j k : Fin 3) :
    ⁅totalSpin j, totalSpin k⁆ = I • ∑ l, (leviCivita3 j k l : ℂ) • totalSpin l := by
  simp only [totalSpin, smul_lie, lie_smul, sigmaKronSum_lie, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

/-- The cyclic SU(2) relation `⁅jₓ, j_y⁆ = i j_z` (Nielsen & Chuang, p. 314). -/
theorem totalSpin_lie_xy : ⁅totalSpin 0, totalSpin 1⁆ = I • totalSpin 2 := by
  simpa [leviCivita3, Fin.sum_univ_three] using totalSpin_lie 0 1

/-- The cyclic SU(2) relation `⁅j_y, j_z⁆ = i jₓ` (Nielsen & Chuang, p. 314). -/
theorem totalSpin_lie_yz : ⁅totalSpin 1, totalSpin 2⁆ = I • totalSpin 0 := by
  simpa [leviCivita3, Fin.sum_univ_three] using totalSpin_lie 1 2

/-- The cyclic SU(2) relation `⁅j_z, jₓ⁆ = i j_y` (Nielsen & Chuang, p. 314). -/
theorem totalSpin_lie_zx : ⁅totalSpin 2, totalSpin 0⁆ = I • totalSpin 1 := by
  simpa [leviCivita3, Fin.sum_univ_three] using totalSpin_lie 2 0

end AxQM.Concrete
