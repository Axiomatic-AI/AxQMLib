/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.Composite
import Mathlib.LinearAlgebra.TensorProduct.Basis
import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Postulates.API — the three-qubit computational basis

The three-qubit register `qubit ⊗ (qubit ⊗ qubit)`: its
computational basis and the tools needed to prove operator identities on it. It is used in
`AxQM/Postulates/API/ControlledControlledUnitary.lean`.

* `qubitThreeBasis (q₁, q₂, q₃) = |q₁⟩ ⊗ (|q₂⟩ ⊗ |q₃⟩)` — the computational basis as a family of
  pure states (the three-qubit analogue of `qubitBasis`).
* `qubitThreeModuleBasis` — the same family as a `Module.Basis` (the tensor product of three copies
  of `qubitModuleBasis`), with `qubitThreeModuleBasis_apply` identifying its vectors with the kets.
* `qubitThree_op_ext` — **extensionality**: two operators on the three-qubit register are equal once
  they agree on every computational basis ket. The workhorse for reducing an operator identity to a
  finite per-basis-vector check.
* `qubitThreeBasis_orthonormal` and `qubitThreeBasis_rankOne_apply` (`|s⟩⟨s| · |b⟩ = δ_{s,b} |s⟩`) —
  orthonormality of the basis and the resulting action of a rank-one projector on a basis ket.
* `qubitThreeFlip` / `qubitThreeCoord` — the index combinatorics shared by every single-qubit
  operator on the register: flip the bit at a position (a bit-flip `X`/`Y`), read the bit at a
  position (the sign exponent of a `Z`); `qubitThreeFlip_involutive` records that a double flip is
  the identity.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The computational basis of the three-qubit system** `qubit ⊗ (qubit ⊗ qubit)`, as a family of
pure states indexed by the bit string `(q₁, q₂, q₃)`: `|q₁, q₂, q₃⟩ = |q₁⟩ ⊗ (|q₂⟩ ⊗ |q₃⟩)`. The
three-qubit analogue of `qubitBasis`, usable as an orthonormal frame — e.g. as the reference basis
for a relative-phase comparison of three-qubit states (`PureState.RelativePhaseEquiv`), or as the
computational basis diagonalising the bit-flip syndrome observables. -/
def qubitThreeBasis : Fin 2 × Fin 2 × Fin 2 → PureState (qubit ⊗ (qubit ⊗ qubit)) :=
  fun i => qubitBasis i.1 ⊗ (qubitBasis i.2.1 ⊗ qubitBasis i.2.2)

/-- The **three-qubit computational basis** as a `Module.Basis`, the tensor product of three copies
of the single-qubit `qubitModuleBasis`. -/
noncomputable def qubitThreeModuleBasis :
    Module.Basis (Fin 2 × Fin 2 × Fin 2) ℂ (qubit.space ⊗[ℂ] (qubit.space ⊗[ℂ] qubit.space)) :=
  qubitModuleBasis.tensorProduct (qubitModuleBasis.tensorProduct qubitModuleBasis)

/-- The basis vector at `(q₁, q₂, q₃)` is the computational ket `|q₁q₂q₃⟩`. -/
theorem qubitThreeModuleBasis_apply (b : Fin 2 × Fin 2 × Fin 2) :
    qubitThreeModuleBasis b = (qubitThreeBasis b).vec := by
  obtain ⟨b1, b2, b3⟩ := b
  rw [qubitThreeModuleBasis, Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply',
    qubitModuleBasis_apply, qubitModuleBasis_apply, qubitModuleBasis_apply]
  rfl

/-- **Extensionality on the computational basis:** two operators on the three-qubit register are
equal once they agree on every computational basis ket `|q₁q₂q₃⟩`. -/
theorem qubitThree_op_ext {T1 T2 : (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ]
    (qubit ⊗ (qubit ⊗ qubit)).space}
    (h : ∀ b : Fin 2 × Fin 2 × Fin 2, T1 (qubitThreeBasis b).vec = T2 (qubitThreeBasis b).vec) :
    T1 = T2 := by
  apply ContinuousLinearMap.coe_injective
  apply Module.Basis.ext qubitThreeModuleBasis
  intro b
  rw [qubitThreeModuleBasis_apply]
  exact h b

/-- **The three-qubit computational basis kets are orthonormal.** -/
theorem qubitThreeBasis_orthonormal : Orthonormal ℂ (fun b => (qubitThreeBasis b).vec) := by
  rw [show (fun b => (qubitThreeBasis b).vec) = ⇑qubitThreeModuleBasis from
    funext fun b => (qubitThreeModuleBasis_apply b).symm]
  exact qubitModuleBasis_orthonormal.basisTensorProduct
    (qubitModuleBasis_orthonormal.basisTensorProduct qubitModuleBasis_orthonormal)

/-- **Distinct three-qubit computational basis kets are orthogonal:**
`⟪|a⟩, |b⟩⟫ = 0` whenever `a ≠ b`, the `if_neg` branch of `qubitThreeBasis_orthonormal`. The
foundational orthogonality fact behind the weight-mismatch overlaps of the Shor-code error
vectors. -/
theorem qubitThreeBasis_inner_eq_zero_of_ne {a b : Fin 2 × Fin 2 × Fin 2} (h : a ≠ b) :
    (inner ℂ (qubitThreeBasis a).vec (qubitThreeBasis b).vec : ℂ) = 0 := by
  rw [orthonormal_iff_ite.mp qubitThreeBasis_orthonormal, ite_eq_right h]

/-- **A rank-one projector onto a basis ket acts as a Kronecker delta:**
`|s⟩⟨s| · |b⟩ = δ_{s,b} |s⟩`, from orthonormality of the computational basis. -/
theorem qubitThreeBasis_rankOne_apply (s b : Fin 2 × Fin 2 × Fin 2) :
    (rankOne ℂ (qubitThreeBasis s).vec (qubitThreeBasis s).vec) (qubitThreeBasis b).vec
      = (if s = b then (1 : ℂ) else 0) • (qubitThreeBasis s).vec := by
  rw [InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp qubitThreeBasis_orthonormal s b]

/-! ### Bit-flip combinatorics on the three-qubit index

Two elementary combinators on the index type `Fin 2 × Fin 2 × Fin 2`, shared by every single-qubit
operator placed on the three-qubit register (a bit flip `X`/`Y`, or a sign `Z`): flipping the bit
at a position, and reading the bit at a position. -/

/-- **Flip the bit at position `pos`** of a three-qubit index `(q₁, q₂, q₃)` (mod `2`):
`pos = 0 ↦ (q₁+1, q₂, q₃)`, `pos = 1 ↦ (q₁, q₂+1, q₃)`, `pos = 2 ↦ (q₁, q₂, q₃+1)`. The
combinatorial shadow of a bit-flip (`X` or `Y`) on the `pos`-th qubit. -/
def qubitThreeFlip : Fin 3 → (Fin 2 × Fin 2 × Fin 2) → (Fin 2 × Fin 2 × Fin 2)
  | 0, (a, b, c) => (a + 1, b, c)
  | 1, (a, b, c) => (a, b + 1, c)
  | 2, (a, b, c) => (a, b, c + 1)

/-- **`qubitThreeFlip pos` is an involution:** flipping the bit at `pos` twice restores the
index. -/
theorem qubitThreeFlip_involutive (pos : Fin 3) (b : Fin 2 × Fin 2 × Fin 2) :
    qubitThreeFlip pos (qubitThreeFlip pos b) = b := by
  obtain ⟨b1, b2, b3⟩ := b
  fin_cases pos <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

/-- **The bit value at position `pos`** of a three-qubit index `(q₁, q₂, q₃)`: `q₁`, `q₂`, `q₃` for
`pos = 0, 1, 2`. The exponent of the `(-1)` sign a `Z` (or the phase of a `Y`) at `pos` produces. -/
def qubitThreeCoord : Fin 3 → (Fin 2 × Fin 2 × Fin 2) → Fin 2
  | 0, (a, _, _) => a
  | 1, (_, b, _) => b
  | 2, (_, _, c) => c

end AxQM
