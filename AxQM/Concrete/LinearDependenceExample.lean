/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# A linearly dependent triple of vectors in `ℂ²` (Nielsen & Chuang, Exercise 2.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.1
(p. 63) asks to show that the three vectors `(1, -1)`, `(1, 2)` and `(2, 1)` of
`ℂ²` are *linearly dependent*. In the book's sense (N&C (2.9)) this means some
complex linear combination of them, with at least one nonzero coefficient, is
the zero vector.

`ℂ²` is modelled by `EuclideanSpace ℂ (Fin 2)`, the library's model of a
two-dimensional complex Hilbert space; the inner-product structure plays no
role here, since linear dependence is a purely module-theoretic notion.

* `dependentTripleC2` — the three vectors as a family
  `Fin 3 → EuclideanSpace ℂ (Fin 2)`.
* `dependentTripleC2_combination_eq_zero` — the explicit witnessing relation
  `(-1)·(1, -1) + (-1)·(1, 2) + 1·(2, 1) = 0`, a zero linear combination with
  not-all-zero coefficients (exactly N&C (2.9)).
* `not_linearIndependent_dependentTripleC2` — the family is not linearly
  independent. Through `Fintype.not_linearIndependent_iff` this negation
  unfolds to precisely N&C's definition (2.9) of linear dependence.
-/

namespace AxQM.Concrete

/-- The three vectors `(1, -1)`, `(1, 2)` and `(2, 1)` of `ℂ²` from
Nielsen & Chuang, Exercise 2.1, packaged as a family indexed by `Fin 3`.
`ℂ²` is modelled by `EuclideanSpace ℂ (Fin 2)`. -/
def dependentTripleC2 : Fin 3 → EuclideanSpace ℂ (Fin 2) :=
  ![!₂[1, -1], !₂[1, 2], !₂[2, 1]]

/-- The explicit nontrivial linear relation witnessing the dependence of
`dependentTripleC2`: in `ℂ²`,
`(-1)·(1, -1) + (-1)·(1, 2) + 1·(2, 1) = 0`. This is a zero linear combination
whose coefficients are not all zero — the form required by N&C (2.9). -/
theorem dependentTripleC2_combination_eq_zero :
    (-1 : ℂ) • dependentTripleC2 0 + (-1 : ℂ) • dependentTripleC2 1
      + (1 : ℂ) • dependentTripleC2 2 = 0 := by
  ext i
  fin_cases i <;> simp [dependentTripleC2] <;> ring

/-- **Nielsen & Chuang, Exercise 2.1.** The vectors `(1, -1)`, `(1, 2)` and
`(2, 1)` of `ℂ²` are linearly dependent: they are *not* linearly independent.
Unfolding `¬ LinearIndependent` via `Fintype.not_linearIndependent_iff` gives
exactly N&C's definition (2.9) — a family of coefficients, not all zero, whose
linear combination of the vectors is `0`; the witness is `(-1, -1, 1)`, supplied
by `dependentTripleC2_combination_eq_zero`. -/
theorem not_linearIndependent_dependentTripleC2 :
    ¬ LinearIndependent ℂ dependentTripleC2 := by
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨![-1, -1, 1], ?_, 2, by simp⟩
  rw [Fin.sum_univ_three]
  simpa using dependentTripleC2_combination_eq_zero

end AxQM.Concrete
