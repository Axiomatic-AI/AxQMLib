/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSCode

/-!
# Commutativity of Pauli phase-flip strings

A small lemma about the CSS Pauli generators of
`AxQM.Postulates.API.CSSCode`: any two **phase-flip strings** `Z^u`, `Z^v`
(`AxQM.phaseString`) **commute**, as unitary `Evolution`s of the bit-vector register
`bitReg ι`.

Both `phaseString u` and `phaseString v` are diagonal operators in the computational orthonormal
basis `regBasis ι` (`|w⟩ ↦ (-1)^{u·w}|w⟩`), and diagonal operators commute because their diagonals
multiply pointwise and pointwise multiplication of scalars is commutative
(`OrthonormalBasis.diagonalOperator_comp`). The statement `Commute (phaseString u) (phaseString v)`
is about `phaseString`; the proof passes through the operator `.op` to its realization as a
diagonal operator.

This is the "encoded `Z` operators commute with `Z`-type stabilizer generators" fact behind
Nielsen & Chuang Exercise 10.56 (and the pure-`Z` half of the encoded-operator commutation relations
of §10.5.7): every product of `Z`'s commutes with every other, whatever their supports.
-/

open scoped Matrix

namespace AxQM

/-- **Two Pauli phase-flip strings commute.** For any bit vectors `u v : ι → ZMod 2`, the
phase-flip strings `Z^u = phaseString u` and `Z^v = phaseString v` commute as unitary `Evolution`s
of `bitReg ι`. Both are diagonal in the computational basis `regBasis ι`, so their composite is the
diagonal operator with pointwise-multiplied diagonal (`OrthonormalBasis.diagonalOperator_comp`),
and pointwise multiplication of the sign entries is commutative. -/
theorem phaseString_commute {ι : Type*} [Fintype ι] [DecidableEq ι] (u v : ι → ZMod 2) :
    Commute (phaseString u) (phaseString v) := by
  refine Evolution.ext ?_
  rw [Evolution.mul_def, Evolution.mul_def, Evolution.comp_op, Evolution.comp_op,
      phaseString_op, phaseString_op, OrthonormalBasis.diagonalOperator_comp,
      OrthonormalBasis.diagonalOperator_comp, mul_comm]

end AxQM
