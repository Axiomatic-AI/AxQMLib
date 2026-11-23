/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.Adjoint
import ToMathlib.Analysis.InnerProductSpace.LinearMap
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete: computational-basis operators on an abstract qubit

Reusable operators on an arbitrary two-dimensional complex inner product space `H`
(a qubit) equipped with a chosen computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`:
the projectors `Pᵢ = |i⟩⟨i|`, the Pauli bit-flip `X = |0⟩⟨1| + |1⟩⟨0|`, and the lowering operator
`σ₋ = |0⟩⟨1|` (its adjoint `σ₊ = |1⟩⟨0|` the raising operator), together with their elementary
algebra (orthogonal idempotence, resolution of identity `P₀ + P₁ = I`, self-adjointness, `X² = I`,
`σ₊ σ₋ = P₁`). These are shared building blocks for the operator-sum cluster of Nielsen & Chuang
§8.2 (Ex 8.4/8.5/…), so they live in their own `Concrete/` module rather than in any exercise file.

Everything is expressed as bare `LinearMap`s — the category the abstract operator-sum /
partial-trace infrastructure (`ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract`,
`…/OperatorSum`) works in — but the operators themselves are **not** reinvented: each is a coercion
of Mathlib's `InnerProductSpace.rankOne` (`|x⟩⟨y|`), and the algebra is derived from the existing
`rankOne` API (`rankOne_apply`, `adjoint_rankOne`, `rankOne_comp_rankOne`,
`OrthonormalBasis.sum_rankOne_eq_id`) bridged into the `LinearMap` category by the `coe` lemmas
(`ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace`, `coe_comp`, `coe_smul`, `coe_sum`,
`coe_id`).
-/

open scoped InnerProductSpace

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

variable (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The computational-basis **projector** `Pᵢ = |i⟩⟨i|` of the qubit, as the bare `LinearMap`
coercion of `InnerProductSpace.rankOne ℂ (b i) (b i)`. -/
noncomputable def qubitProj (i : Fin 2) : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b i) (b i) : H →ₗ[ℂ] H)

/-- The qubit **bit-flip** (Pauli `X`) operator `X = |0⟩⟨1| + |1⟩⟨0|`. -/
noncomputable def qubitFlip : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b 0) (b 1) : H →ₗ[ℂ] H)
    + (InnerProductSpace.rankOne ℂ (b 1) (b 0) : H →ₗ[ℂ] H)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem qubitProj_apply (i : Fin 2) (v : H) :
    qubitProj b i v = (inner ℂ (b i) v) • b i := by
  simp only [qubitProj, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]

/-- Each projector is self-adjoint: `Pᵢ† = Pᵢ` (reusing `adjoint_rankOne`). -/
@[simp] theorem adjoint_qubitProj (i : Fin 2) :
    LinearMap.adjoint (qubitProj b i) = qubitProj b i := by
  simp only [qubitProj]
  rw [← ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace, InnerProductSpace.adjoint_rankOne]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The projectors are orthogonal idempotents:
`Pᵢ Pⱼ = δᵢⱼ Pᵢ` (`rankOne_comp_rankOne` + orthonormality). -/
theorem qubitProj_comp_qubitProj (i j : Fin 2) :
    qubitProj b i ∘ₗ qubitProj b j = if i = j then qubitProj b i else 0 := by
  simp only [qubitProj]
  rw [← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.rankOne_comp_rankOne,
    ContinuousLinearMap.toLinearMap_smul, b.inner_eq_ite]
  split_ifs with h
  · subst h; simp
  · simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The square of a **diagonal qubit operator** `P₀ + c • P₁` is `(P₀ + c • P₁)² = P₀ + c² • P₁`:
the projectors are orthogonal idempotents (`qubitProj_comp_qubitProj`), so the cross terms vanish
and the `P₁` coefficient squares. This is the shared engine for squaring the diagonal operation
element `E₀ = diag(1, √(1-x))` of the amplitude- and phase-damping channels (`ampDampKrausZero`,
`phaseDampKrausZero`), which are both this operator. -/
theorem qubitProjDiag_comp_self (c : ℂ) :
    (qubitProj b 0 + c • qubitProj b 1) ∘ₗ (qubitProj b 0 + c • qubitProj b 1)
      = qubitProj b 0 + (c * c) • qubitProj b 1 := by
  simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul,
    qubitProj_comp_qubitProj, Fin.isValue, Fin.reduceEq, ↓reduceIte, smul_zero, add_zero,
    zero_add, smul_smul]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Completeness of the computational basis: `P₀ + P₁ = I` (`sum_rankOne_eq_id`). -/
theorem sum_qubitProj : qubitProj b 0 + qubitProj b 1 = LinearMap.id := by
  simp only [qubitProj]
  rw [← ContinuousLinearMap.coe_id (R₁ := ℂ), ← b.sum_rankOne_eq_id,
      ContinuousLinearMap.toLinearMap_sum,
    Fin.sum_univ_two]

/-- The bit-flip is self-adjoint: `X† = X`. -/
theorem adjoint_qubitFlip : LinearMap.adjoint (qubitFlip b) = qubitFlip b := by
  simp only [qubitFlip]
  rw [map_add, ← ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace,
      ← ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace,
    InnerProductSpace.adjoint_rankOne, InnerProductSpace.adjoint_rankOne, add_comm]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem qubitFlip_apply_zero : qubitFlip b (b 0) = b 1 := by
  simp only [qubitFlip, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, b.inner_eq_ite]
  simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem qubitFlip_apply_one : qubitFlip b (b 1) = b 0 := by
  simp only [qubitFlip, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, b.inner_eq_ite]
  simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The bit-flip is an involution: `X² = I`. The cross terms vanish and the diagonal terms are the
two projectors, which sum to the identity. -/
theorem qubitFlip_comp_qubitFlip : qubitFlip b ∘ₗ qubitFlip b = LinearMap.id := by
  simp only [qubitFlip, LinearMap.comp_add, LinearMap.add_comp,
    ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.rankOne_comp_rankOne,
    ContinuousLinearMap.toLinearMap_smul, b.inner_eq_ite]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, one_smul, zero_smul, add_zero, zero_add]
  rw [add_comm]
  exact sum_qubitProj b

/-- The atomic **lowering operator** `σ₋ = |0⟩⟨1|` of the qubit (N&C §8.4.1): it sends the excited
state `|1⟩` to the ground state `|0⟩` and annihilates `|0⟩`. As the bare `LinearMap` coercion of
`InnerProductSpace.rankOne ℂ (b 0) (b 1)`; it is the first summand of the bit-flip `qubitFlip`. -/
noncomputable def qubitLower : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b 0) (b 1) : H →ₗ[ℂ] H)

/-- The lowering operator's adjoint is the **raising operator** `σ₊ = σ₋† = |1⟩⟨0|`
(`adjoint_rankOne` swaps the two vectors). -/
theorem adjoint_qubitLower :
    LinearMap.adjoint (qubitLower b) = (InnerProductSpace.rankOne ℂ (b 1) (b 0) : H →ₗ[ℂ] H) := by
  rw [qubitLower, ← ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace,
      InnerProductSpace.adjoint_rankOne]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem qubitLower_apply_one : qubitLower b (b 1) = b 0 := by
  simp only [qubitLower, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    b.inner_eq_ite]
  simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem qubitLower_apply_zero : qubitLower b (b 0) = 0 := by
  simp only [qubitLower, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    b.inner_eq_ite]
  simp

/-- `σ₊ σ₋ = |1⟩⟨0| |0⟩⟨1| = |1⟩⟨1| = P₁`: the raising-then-lowering product is the excited-state
projector (`rankOne_comp_rankOne` with `⟨0|0⟩ = 1`). -/
theorem qubitLower_adjoint_comp_self :
    LinearMap.adjoint (qubitLower b) ∘ₗ qubitLower b = qubitProj b 1 := by
  rw [adjoint_qubitLower, qubitLower, qubitProj,
    ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.rankOne_comp_rankOne,
    ContinuousLinearMap.toLinearMap_smul, b.inner_eq_ite]
  simp

/-- `σ₋ σ₊ = |0⟩⟨1| |1⟩⟨0| = |0⟩⟨0| = P₀`: the lowering-then-raising product is the ground-state
projector (the companion of `qubitLower_adjoint_comp_self`, `σ₊ σ₋ = P₁`; `rankOne_comp_rankOne`
with `⟨1|1⟩ = 1`). -/
theorem qubitLower_comp_adjoint_self :
    qubitLower b ∘ₗ LinearMap.adjoint (qubitLower b) = qubitProj b 0 := by
  rw [adjoint_qubitLower, qubitLower, qubitProj,
    ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.rankOne_comp_rankOne,
    ContinuousLinearMap.toLinearMap_smul, b.inner_eq_ite]
  simp

/-- The computational-basis **matrix unit** `|i⟩⟨j|` of the qubit, as the bare `LinearMap` coercion
of `InnerProductSpace.rankOne ℂ (b i) (b j)`. It generalizes the projector `Pᵢ = |i⟩⟨i|`
(`qubitProj b i = qubitUnit b i i`, definitionally) and the lowering operator `σ₋ = |0⟩⟨1|`
(`qubitLower b = qubitUnit b 0 1`, definitionally); every computational-basis operator product then
reduces to the single matrix-unit product law `qubitUnit_comp`. -/
noncomputable def qubitUnit (i j : Fin 2) : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b i) (b j) : H →ₗ[ℂ] H)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
@[simp] theorem qubitUnit_apply (i j : Fin 2) (v : H) :
    qubitUnit b i j v = (inner ℂ (b j) v) • b i := by
  simp only [qubitUnit, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The **matrix-unit product law** `|i⟩⟨j| |k⟩⟨l| = δⱼₖ |i⟩⟨l|` (`rankOne_comp_rankOne` with the
orthonormality of `b`): every product of computational-basis operators is an instance of this. -/
theorem qubitUnit_comp (i j k l : Fin 2) :
    qubitUnit b i j ∘ₗ qubitUnit b k l = if j = k then qubitUnit b i l else 0 := by
  simp only [qubitUnit]
  rw [← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.rankOne_comp_rankOne,
    ContinuousLinearMap.toLinearMap_smul, b.inner_eq_ite]
  split_ifs with h
  · subst h; simp
  · simp

/-- The matrix unit's adjoint swaps its indices: `|i⟩⟨j|† = |j⟩⟨i|` (`adjoint_rankOne`). -/
@[simp] theorem adjoint_qubitUnit (i j : Fin 2) :
    LinearMap.adjoint (qubitUnit b i j) = qubitUnit b j i := by
  rw [qubitUnit, ← ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace,
      InnerProductSpace.adjoint_rankOne,
    qubitUnit]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The projector is the diagonal matrix unit: `Pᵢ = |i⟩⟨i|`. -/
theorem qubitProj_eq_qubitUnit (i : Fin 2) : qubitProj b i = qubitUnit b i i := rfl

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The lowering operator is the off-diagonal matrix unit: `σ₋ = |0⟩⟨1|`. -/
theorem qubitLower_eq_qubitUnit : qubitLower b = qubitUnit b 0 1 := rfl

/-! ### The Pauli `Z` operator -/

/-- The qubit **Pauli `Z`** operator `Z = |0⟩⟨0| - |1⟩⟨1| = P₀ - P₁`, the difference of the two
computational-basis projectors. -/
noncomputable def qubitPauliZ : H →ₗ[ℂ] H := qubitProj b 0 - qubitProj b 1

/-- `Z` is self-adjoint: `Z† = Z`. -/
theorem adjoint_qubitPauliZ : LinearMap.adjoint (qubitPauliZ b) = qubitPauliZ b := by
  simp [qubitPauliZ, map_sub, adjoint_qubitProj]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `Z` is an involution: `Z ∘ Z = I` (orthogonal idempotence of the projectors and `P₀ + P₁ = I`).
Together with self-adjointness this makes `Z` unitary. -/
theorem qubitPauliZ_comp_qubitPauliZ : qubitPauliZ b ∘ₗ qubitPauliZ b = LinearMap.id := by
  simp only [qubitPauliZ, LinearMap.comp_sub, LinearMap.sub_comp, qubitProj_comp_qubitProj,
    Fin.reduceEq, reduceIte, sub_zero, zero_sub, sub_neg_eq_add]
  exact sum_qubitProj b

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `Z` applied to a vector: `Z v = P₀ v - P₁ v`. -/
theorem qubitPauliZ_apply (v : H) :
    qubitPauliZ b v = qubitProj b 0 v - qubitProj b 1 v := by
  rw [qubitPauliZ, LinearMap.sub_apply]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Resolution of the identity, pointwise: `P₀ v + P₁ v = v`. -/
theorem qubitProj_add_apply (v : H) : qubitProj b 0 v + qubitProj b 1 v = v := by
  rw [← LinearMap.add_apply, sum_qubitProj, LinearMap.id_apply]

/-! ### The `|+⟩⟨+|`, `|-⟩⟨-|` projectors as `½(I ± X)` -/

/-- The rank-one projector `|+⟩⟨+| = ½(I + X)` onto the `+1`-eigenvector of the bit-flip `X`. -/
noncomputable def qubitPlusProj : H →ₗ[ℂ] H := (2 : ℂ)⁻¹ • (LinearMap.id + qubitFlip b)

/-- The rank-one projector `|-⟩⟨-| = ½(I - X)` onto the `-1`-eigenvector of the bit-flip `X`. -/
noncomputable def qubitMinusProj : H →ₗ[ℂ] H := (2 : ℂ)⁻¹ • (LinearMap.id - qubitFlip b)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `X` fixes the `+`-projector on the right: `X ∘ P₊ = P₊` (since `X|+⟩ = |+⟩`). -/
theorem qubitFlip_comp_qubitPlusProj :
    qubitFlip b ∘ₗ qubitPlusProj b = qubitPlusProj b := by
  rw [qubitPlusProj, LinearMap.comp_smul, LinearMap.comp_add, LinearMap.comp_id,
    qubitFlip_comp_qubitFlip, add_comm]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `X` fixes the `+`-projector on the left: `P₊ ∘ X = P₊`. -/
theorem qubitPlusProj_comp_qubitFlip :
    qubitPlusProj b ∘ₗ qubitFlip b = qubitPlusProj b := by
  rw [qubitPlusProj, LinearMap.smul_comp, LinearMap.add_comp, LinearMap.id_comp,
    qubitFlip_comp_qubitFlip, add_comm]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `X` negates the `-`-projector on the right: `X ∘ P₋ = -P₋` (since `X|-⟩ = -|-⟩`). -/
theorem qubitFlip_comp_qubitMinusProj :
    qubitFlip b ∘ₗ qubitMinusProj b = -qubitMinusProj b := by
  rw [qubitMinusProj, LinearMap.comp_smul, LinearMap.comp_sub, LinearMap.comp_id,
    qubitFlip_comp_qubitFlip, ← smul_neg, neg_sub]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `X` negates the `-`-projector on the left: `P₋ ∘ X = -P₋`. -/
theorem qubitMinusProj_comp_qubitFlip :
    qubitMinusProj b ∘ₗ qubitFlip b = -qubitMinusProj b := by
  rw [qubitMinusProj, LinearMap.smul_comp, LinearMap.sub_comp, LinearMap.id_comp,
    qubitFlip_comp_qubitFlip, ← smul_neg, neg_sub]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `X` fixes `P₊ y`, pointwise: `X (P₊ y) = P₊ y`. -/
theorem qubitFlip_qubitPlusProj_apply (y : H) :
    qubitFlip b (qubitPlusProj b y) = qubitPlusProj b y := by
  rw [← LinearMap.comp_apply, qubitFlip_comp_qubitPlusProj]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `X` negates `P₋ y`, pointwise: `X (P₋ y) = -(P₋ y)`. -/
theorem qubitFlip_qubitMinusProj_apply (y : H) :
    qubitFlip b (qubitMinusProj b y) = -(qubitMinusProj b y) := by
  rw [← LinearMap.comp_apply, qubitFlip_comp_qubitMinusProj, LinearMap.neg_apply]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `P₋` composed with `X`, pointwise: `P₋ (X y) = -(P₋ y)`. -/
theorem qubitMinusProj_qubitFlip_apply (y : H) :
    qubitMinusProj b (qubitFlip b y) = -(qubitMinusProj b y) := by
  rw [← LinearMap.comp_apply, qubitMinusProj_comp_qubitFlip, LinearMap.neg_apply]

end AxQM.Concrete
