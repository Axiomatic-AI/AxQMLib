/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrix representations depend on the chosen bases (Nielsen & Chuang, Exercise 2.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.2
(p. 64, "Matrix representations: example") takes a two-dimensional space `V` with
basis vectors `|0⟩`, `|1⟩` and the linear operator `A` determined by
`A|0⟩ = |1⟩`, `A|1⟩ = |0⟩`. It asks to (1) give the matrix representation of `A`
with respect to the input and output basis `|0⟩, |1⟩`, and (2) exhibit input and
output bases giving a *different* matrix representation of the same `A`.

`V` is modelled by
`EuclideanSpace ℂ (Fin 2)`, the library's model of `ℂ²`, and `|0⟩`,
`|1⟩` by its standard basis `EuclideanSpace.basisFun`. Matrix representation is a
purely module-theoretic notion (`LinearMap.toMatrix` relative to `Module.Basis`
data), so the inner-product structure plays no role; every proof here uses only
the `Module.Basis` interface (`constr`, `repr`), never the concrete model of `ℂ²`.

* `swapOperator` — the operator `A` with `A|0⟩ = |1⟩`, `A|1⟩ = |0⟩`, built by
  `Module.Basis.constr` so that it is *defined* by its action on the basis (as in
  the exercise); `swapOperator_apply_zero` / `swapOperator_apply_one` record that
  action.
* `toMatrix_swapOperator_std` — **Part 1**: with respect to the standard basis
  `|0⟩, |1⟩` for both input and output, `A` has matrix `!![0, 1; 1, 0]`.
* `hadamardBasis` — a *different* basis `{|0⟩ + |1⟩, |0⟩ - |1⟩}` (the unnormalised
  `|±⟩` basis; these are the eigenvectors of `A`).
* `toMatrix_swapOperator_hadamard` — **Part 2**: with respect to `hadamardBasis`
  for both input and output, the *same* `A` has the diagonal matrix
  `!![1, 0; 0, -1]`.
* `toMatrix_swapOperator_std_ne_hadamard` — the two matrices differ, so these
  bases genuinely give a different matrix representation of `A`.
-/

namespace AxQM.Concrete

open scoped Matrix

noncomputable section

/-- The standard (computational) basis `|0⟩, |1⟩` of `ℂ² = EuclideanSpace ℂ (Fin 2)`,
as a `Module.Basis`. This is `EuclideanSpace.basisFun` viewed through
`OrthonormalBasis.toBasis`; only its `Module.Basis` structure is used below. -/
def compBasis : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis

/-- **Nielsen & Chuang, Exercise 2.2**, the operator `A`: the linear operator on
`ℂ²` determined by `A|0⟩ = |1⟩` and `A|1⟩ = |0⟩`. It is defined by its action on
the standard basis via `Module.Basis.constr`, mirroring the exercise, which
specifies `A` by that action. -/
def swapOperator : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  compBasis.constr ℂ ![compBasis 1, compBasis 0]

/-- `A|0⟩ = |1⟩`: the defining action of `swapOperator` on the first standard
basis vector. -/
@[simp] theorem swapOperator_apply_zero : swapOperator (compBasis 0) = compBasis 1 := by
  simp [swapOperator]

/-- `A|1⟩ = |0⟩`: the defining action of `swapOperator` on the second standard
basis vector. -/
@[simp] theorem swapOperator_apply_one : swapOperator (compBasis 1) = compBasis 0 := by
  simp [swapOperator]

/-- **Part 1.** The matrix representation of `A` with respect to the standard
basis `|0⟩, |1⟩` for both the input and the output is `!![0, 1; 1, 0]`. -/
theorem toMatrix_swapOperator_std :
    LinearMap.toMatrix compBasis compBasis swapOperator = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply]

/-- The family `{|0⟩ + |1⟩, |0⟩ - |1⟩}` is linearly independent. -/
theorem hadamardFamily_linearIndependent :
    LinearIndependent ℂ ![compBasis 0 + compBasis 1, compBasis 0 - compBasis 1] := by
  have hb : LinearIndependent ℂ ![compBasis 0, compBasis 1] := by
    have h := compBasis.linearIndependent
    have he : (![compBasis 0, compBasis 1] : Fin 2 → EuclideanSpace ℂ (Fin 2)) = compBasis := by
      funext i; fin_cases i <;> simp
    rw [he]; exact h
  rw [LinearIndependent.pair_iff] at hb ⊢
  intro s t h
  obtain ⟨h1, h2⟩ := hb (s + t) (s - t) (by rw [← h]; module)
  exact ⟨by linear_combination (h1 + h2) / 2, by linear_combination (h1 - h2) / 2⟩

/-- A *different* basis of `ℂ²`: the unnormalised `|±⟩` basis
`{|0⟩ + |1⟩, |0⟩ - |1⟩}`, whose vectors are the eigenvectors of `A`. -/
def hadamardBasis : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  basisOfLinearIndependentOfCardEqFinrank hadamardFamily_linearIndependent
    (by simp [Module.finrank_eq_card_basis compBasis])

/-- The first `hadamardBasis` vector is `|0⟩ + |1⟩`. -/
theorem hadamardBasis_apply_zero : hadamardBasis 0 = compBasis 0 + compBasis 1 := by
  simp [hadamardBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The second `hadamardBasis` vector is `|0⟩ - |1⟩`. -/
theorem hadamardBasis_apply_one : hadamardBasis 1 = compBasis 0 - compBasis 1 := by
  simp [hadamardBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- `|0⟩ + |1⟩` is a `+1`-eigenvector of `A`. -/
theorem swapOperator_apply_hadamard_zero :
    swapOperator (hadamardBasis 0) = hadamardBasis 0 := by
  rw [hadamardBasis_apply_zero]
  simp [add_comm]

/-- `|0⟩ - |1⟩` is a `-1`-eigenvector of `A`. -/
theorem swapOperator_apply_hadamard_one :
    swapOperator (hadamardBasis 1) = -hadamardBasis 1 := by
  rw [hadamardBasis_apply_one]
  simp [neg_sub]

/-- **Part 2.** The matrix representation of the *same* operator `A` with respect
to the basis `{|0⟩ + |1⟩, |0⟩ - |1⟩}` for both input and output is the diagonal
matrix `!![1, 0; 0, -1]`. -/
theorem toMatrix_swapOperator_hadamard :
    LinearMap.toMatrix hadamardBasis hadamardBasis swapOperator = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, swapOperator_apply_hadamard_zero,
      swapOperator_apply_hadamard_one]

/-- The two matrix representations of `A` are different, so these bases genuinely
give rise to a different matrix representation, as Exercise 2.2 asks. -/
theorem toMatrix_swapOperator_std_ne_hadamard :
    LinearMap.toMatrix compBasis compBasis swapOperator
      ≠ LinearMap.toMatrix hadamardBasis hadamardBasis swapOperator := by
  rw [toMatrix_swapOperator_std, toMatrix_swapOperator_hadamard]
  intro h
  have := congrFun (congrFun h 0) 0
  simp at this

end

end AxQM.Concrete
