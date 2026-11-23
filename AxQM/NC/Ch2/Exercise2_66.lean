/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellState

/-!
# Nielsen & Chuang, Exercise 2.66

Show average value of X1 Z2 for two-qubit state (|00>+|11>)/sqrt2 is zero.

Here `X₁Z₂ = X ⊗ Z` is the observable measuring Pauli `X` on the first qubit and Pauli `Z` on the
second, and `(|00⟩ + |11⟩)/√2` is the Bell state `|Φ⁺⟩`. The **average value** is the expectation
`⟪X ⊗ Z⟫ = ⟨Φ⁺|X ⊗ Z|Φ⁺⟩` of Postulate 3 (Nielsen & Chuang (2.113)).

## The answer

Expanding the Bell state,
`⟨Φ⁺|X ⊗ Z|Φ⁺⟩ = ½ Σᵢⱼ ⟨i|X|j⟩⟨i|Z|j⟩ = ½ Σᵢⱼ Xᵢⱼ Zᵢⱼ = 0`.
`X` is purely off-diagonal (`Xᵢⱼ ≠ 0` only for `i ≠ j`) while `Z` is diagonal (`Zᵢⱼ ≠ 0` only for
`i = j`), so the elementwise product `Xᵢⱼ Zᵢⱼ` vanishes for **every** `(i, j)`, and the average is
`0`. (Concretely the four terms are `X₀₀Z₀₀ = 0·1`, `X₀₁Z₀₁ = 1·0`, `X₁₀Z₁₀ = 1·0`,
`X₁₁Z₁₁ = 0·(−1)`.)

Here `|Φ⁺⟩` is a
`PureState (qubit ⊗ qubit)` (Postulate 4, composite systems), `X ⊗ Z` is
`pauliXObservable ⊗ pauliZObservable` (`Observable.tmul`, N&C Exercise 2.30), and the
average is `PureState.expectation` (Postulate 3).

* `bellPhiPlus_expectation_pauliX_tmul_pauliZ_eq_zero` — the average value `⟪X ⊗ Z⟫_{Φ⁺} = 0`.

The objects used are in `AxQM/Postulates/API/`: the Bell state
`bellPhiPlus` and its vector `bellVec` in `BellState.lean`; the Pauli `Z` observable
`pauliZObservable` and the computational-basis matrix elements `pauliXObservable_inner_qubitBasis` /
`pauliZObservable_inner_qubitBasis` (`⟨i|X|j⟩ = Xᵢⱼ`, `⟨i|Z|j⟩ = Zᵢⱼ`) in `Qubit.lean`. The
inner-product computation `⟨Φ⁺|X ⊗ Z|Φ⁺⟩ = 0` is carried out in the proof body.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.66.** The average value of the observable `X₁Z₂ = X ⊗ Z` in the
Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` is zero: `⟪X ⊗ Z⟫_{Φ⁺} = 0`. Because `X` is off-diagonal and
`Z` is diagonal in the computational basis, every term `⟨i|X|j⟩⟨i|Z|j⟩` of the Bell-state
expectation vanishes. Stated with `PureState.expectation` (Postulate 3) and
`Observable.tmul` (`⊗`) (Postulate 4 / N&C Exercise 2.30). -/
theorem bellPhiPlus_expectation_pauliX_tmul_pauliZ_eq_zero :
    bellPhiPlus.expectation (pauliXObservable ⊗ pauliZObservable) = 0 := by
  -- Core computation: `⟨β|X ⊗ Z|β⟩ = 0` on the unnormalised vector `β = |00⟩ + |11⟩`. Restated
  -- over the raw tensor product, `X ⊗ Z` distributes over the two elementary tensors and the four
  -- resulting inner products collapse to the vanishing sum `Σᵢⱼ Xᵢⱼ Zᵢⱼ`.
  have hcore : inner ℂ bellVec ((pauliXObservable ⊗ pauliZObservable).op bellVec) = (0 : ℂ) := by
    change (@inner ℂ (TensorProduct ℂ qubit.space qubit.space) _ bellVec
      ((TensorProduct.mapL pauliXObservable.op pauliZObservable.op) bellVec) : ℂ) = 0
    rw [bellVec, map_add, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
      inner_add_left, inner_add_right, inner_add_right,
      TensorProduct.inner_tmul, TensorProduct.inner_tmul,
      TensorProduct.inner_tmul, TensorProduct.inner_tmul,
      pauliXObservable_inner_qubitBasis, pauliXObservable_inner_qubitBasis,
      pauliXObservable_inner_qubitBasis, pauliXObservable_inner_qubitBasis,
      pauliZObservable_inner_qubitBasis, pauliZObservable_inner_qubitBasis,
      pauliZObservable_inner_qubitBasis, pauliZObservable_inner_qubitBasis]
    simp [Concrete.pauliX, Concrete.pauliZ]
  -- Pull the normalising scalar `(√2)⁻¹` out of both slots; the core inner product is zero.
  have key : inner ℂ bellPhiPlus.vec ((pauliXObservable ⊗ pauliZObservable).op bellPhiPlus.vec)
      = (0 : ℂ) := by
    rw [bellPhiPlus_vec, ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right,
      hcore, mul_zero, mul_zero]
  rw [PureState.expectation, key, Complex.zero_re]

end AxQM
