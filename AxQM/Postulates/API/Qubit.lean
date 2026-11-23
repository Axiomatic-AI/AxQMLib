/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Observable
import AxQM.Concrete.Pauli
import AxQM.Concrete.PauliOuterProduct
import AxQM.Concrete.PauliEigenvectors
import ToMathlib.Analysis.CStarAlgebra.Matrix
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Postulates.API — the qubit and its Pauli vector observables

The two-level system and its spin observables.

* `qubit` — the two-level quantum system, `QSystem.ofModel (EuclideanSpace ℂ (Fin 2))`.
* `pauliObservable n` (`n · σ`) — for a real three-vector `n`, the **observable**
  `n₀ X + n₁ Y + n₂ Z` on the qubit, obtained by promoting the concrete Pauli matrix
  `Concrete.pauliDot n` to a continuous linear operator via the C\*-algebra isomorphism
  `Matrix.toEuclideanCLM`. It is self-adjoint because `n · σ` is Hermitian
  (`Concrete.pauliDot_isHermitian`).
* `pauliObservable_op_mul_self` — for a **unit** vector `n`, `(n · σ)² = 1` in the operator
  ring, the involution property. This is the operator-level counterpart of
  `Concrete.pauliDot_mul_self_of_unit`, and is the key input that makes the two-qubit Pauli
  operators a CHSH tuple (Nielsen & Chuang Problem 2.3 / Tsirelson's inequality).
* `qubitBasis i` (`|i⟩`) — the **computational-basis pure state** `|0⟩` / `|1⟩` of the qubit,
  the normalized standard basis vector `EuclideanSpace.single i 1`. These are the states
  `|0⟩, |1⟩` used throughout Chapter 2 (e.g. the input `|0⟩` of Exercises 2.59 and 2.61).
* `pauliXObservable` (`X`) / `pauliYObservable` (`Y`) / `pauliZObservable` (`Z`) — the **Pauli `X` /
  `Y` / `Z` observables** on the qubit, the Pauli vector observables for the unit directions
  `(1, 0, 0)` / `(0, 1, 0)` / `(0, 0, 1)`. `pauliXObservable_op` / `pauliYObservable_op` /
  `pauliZObservable_op` identify their operators with `Matrix.toEuclideanCLM Concrete.pauliX` /
  `Concrete.pauliY` / `Concrete.pauliZ`, and `pauliXObservable_op_mul_self` records `X² = 1` (the
  special case of the involution at `(1, 0, 0)`).
* `pauliXObservable_apply_toLp` / `pauliYObservable_apply_toLp` / `pauliZObservable_apply_toLp`
  — the **operator-application bridges** `σ (WithLp.toLp 2 v) = WithLp.toLp 2 (σ.mulVec v)`,
  lifting a concrete matrix eigenvalue equation `pauli* *ᵥ v = μ • v` to the observable
  (e.g. the Pauli-eigenstate certifications of Exercise 4.1).
* `pauliXObservable_apply_{xPlus,xMinus}` / `pauliYObservable_apply_{yPlus,yMinus}` /
  `pauliZObservable_apply_{ket0,ket1}` — the **operator eigenvalue equations**
  `σ (toLp v) = ±1 • toLp v` of the six normalized Pauli eigenvectors (Exercise 2.11), the
  inputs to Exercise 4.1's eigenstate certifications (the `-1` cases state the eigenvalue as
  `((-1 : ℝ) : ℂ)`).
* `qubitBasis_inner_qubitBasis` — **orthonormality** `⟨i|j⟩ = δᵢⱼ` of the computational basis.
* `pauliXObservable_inner_qubitBasis` / `pauliZObservable_inner_qubitBasis` — the **basis matrix
  elements** `⟨i|X|j⟩ = Xᵢⱼ` / `⟨i|Z|j⟩ = Zᵢⱼ`, reading the Pauli operator's entries off the
  concrete matrices. These feed the two-qubit expectation computations (e.g. Exercise 2.66).

## Design notes

* The bridge is `Matrix.toEuclideanCLM : Matrix n n ℂ ≃⋆ₐ[ℂ] EuclideanSpace ℂ n →L[ℂ] …`, a
  `⋆`-algebra *equivalence*. Because it is a `⋆`-algebra homomorphism it transports every
  structural fact about `Concrete.pauliDot n` to its operator: `map_star` turns Hermiticity
  into self-adjointness, and `map_mul`/`map_one` turn `(n·σ)² = I` into `op * op = 1`. No
  entrywise operator computation is needed.
* `pauliObservable` is defined for an *arbitrary* `n` (self-adjointness holds unconditionally);
  the unit-vector hypothesis is required only for the involution lemma, and is threaded there,
  matching how Problem 2.3 restricts to unit vectors `q⃗, r⃗, s⃗, t⃗`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **qubit**: the two-level quantum system, whose state space is the standard
two-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 2)`. -/
def qubit : QSystem := QSystem.ofModel (EuclideanSpace ℂ (Fin 2))

/-- **The qubit state space is nontrivial** (it is `EuclideanSpace ℂ (Fin 2)`, dimension `2`). Lets
constructions that need a nonzero space — e.g. `maximallyMixedState qubit` — resolve the
`Nontrivial` side-condition automatically. -/
instance : Nontrivial qubit.space :=
  inferInstanceAs (Nontrivial (EuclideanSpace ℂ (Fin 2)))

/-- **The qubit has dimension `2`**: `finrank ℂ qubit.space = 2`, since `qubit.space` is
`EuclideanSpace ℂ (Fin 2)`. -/
theorem finrank_qubit_space : Module.finrank ℂ qubit.space = 2 := by
  change Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2
  exact finrank_euclideanSpace_fin

/-- The **computational basis state `|0⟩ = (1, 0)`** as a pure state of the qubit — the standard
basis ket `Concrete.ket 0` viewed in `EuclideanSpace`. The fundamental single-qubit state, shared by
all qubit items (measurements, expectations, …). -/
def qubitKet0 : PureState qubit where
  vec := WithLp.toLp 2 (Concrete.ket 0)
  normalized := by
    have h : ‖(WithLp.toLp 2 (Concrete.ket 0) : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [Concrete.ket, Fin.sum_univ_two]
    exact h

@[simp]
theorem qubitKet0_vec : qubitKet0.vec = WithLp.toLp 2 (Concrete.ket 0) := rfl

/-- The **Pauli vector observable** `n · σ = n₀ X + n₁ Y + n₂ Z` on the qubit, for a real
three-vector `n`. Its operator is the concrete Hermitian matrix `Concrete.pauliDot n` promoted
to a continuous linear map through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`;
self-adjointness follows from `Concrete.pauliDot_isHermitian` since that isomorphism preserves
`star`. These are the observables `Q, R, S, T` of Nielsen & Chuang Problem 2.3. -/
def pauliObservable (n : Fin 3 → ℝ) : Observable qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n)
  selfAdjoint :=
    (Concrete.pauliDot_isHermitian n).isSelfAdjoint.map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))

/-- The underlying operator of `pauliObservable n` is the `Matrix.toEuclideanCLM` image of the
concrete matrix `Concrete.pauliDot n`. A `simp` lemma exposing the operator for
operator computations (e.g. assembling the two-qubit CHSH tuple of Problem 2.3). -/
@[simp]
theorem pauliObservable_op (n : Fin 3 → ℝ) :
    (pauliObservable n).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n) :=
  rfl

/-- **The Pauli vector observable of a unit vector is an involution:** `(n · σ)² = 1` in the
qubit's operator ring, for a unit vector `n` (`n₀² + n₁² + n₂² = 1`). This transports the
concrete matrix identity `Concrete.pauliDot_mul_self_of_unit` across the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM` (via `map_mul` and `map_one`). It is the input that makes
`Q, R, S, T` self-adjoint involutions — hence a CHSH tuple — in Problem 2.3. -/
theorem pauliObservable_op_mul_self {n : Fin 3 → ℝ}
    (h : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    (pauliObservable n).op * (pauliObservable n).op = 1 := by
  -- The operator multiplication lives at `↑qubit →L ↑qubit`; restate it at the definitionally
  -- equal `EuclideanSpace ℂ (Fin 2) →L …` so the `⋆`-algebra homomorphism lemmas apply.
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n)
       * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n) = 1
  rw [← map_mul, Concrete.pauliDot_mul_self_of_unit h, map_one]

/-- The **computational-basis pure state** `|i⟩` of the qubit: the standard basis vector
`EuclideanSpace.single i 1`, which is normalized because `‖EuclideanSpace.single i 1‖ = ‖(1 : ℂ)‖
= 1` (`EuclideanSpace.norm_single`). Instantiating `i = 0` / `i = 1` gives the states `|0⟩` and
`|1⟩` of Chapter 2. -/
def qubitBasis (i : Fin 2) : PureState qubit where
  vec := EuclideanSpace.single i 1
  normalized := by
    change ‖EuclideanSpace.single i (1 : ℂ)‖ = 1
    simp

/-- The underlying unit vector of the computational-basis state `|i⟩` is `EuclideanSpace.single
i 1`. A `simp` lemma exposing the state vector for inner-product computations. -/
@[simp]
theorem qubitBasis_vec (i : Fin 2) :
    (qubitBasis i).vec = EuclideanSpace.single i 1 := rfl

/-- The **Pauli `X` observable** on the qubit: the Pauli vector observable `n · σ` for the unit
direction `n = (1, 0, 0)`, i.e. `X = pauliObservable ![1, 0, 0]`. Constructed through the
established `pauliObservable` API so that `X² = 1` is the involution
`pauliObservable_op_mul_self` at a unit vector. -/
def pauliXObservable : Observable qubit := pauliObservable ![1, 0, 0]

/-- The operator of the Pauli `X` observable is `Matrix.toEuclideanCLM Concrete.pauliX`: the
Pauli direction `(1, 0, 0)` collapses `Concrete.pauliDot ![1, 0, 0]` to the concrete matrix
`Concrete.pauliX = !![0, 1; 1, 0]`. -/
@[simp]
theorem pauliXObservable_op :
    pauliXObservable.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX := by
  rw [pauliXObservable, pauliObservable_op]
  congr 1
  rw [Concrete.pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Concrete.pauliX]

/-- **`X² = 1`:** the Pauli `X` observable is an involution in the qubit's operator ring. The
special case of `pauliObservable_op_mul_self` at the unit vector `(1, 0, 0)`. -/
theorem pauliXObservable_op_mul_self :
    pauliXObservable.op * pauliXObservable.op = 1 := by
  rw [pauliXObservable]
  exact pauliObservable_op_mul_self
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons])

/-- The **Pauli `Y` observable** on the qubit: the Pauli vector observable `n · σ` for the unit
direction `n = (0, 1, 0)`, i.e. `Y = pauliObservable ![0, 1, 0]`. Constructed through the
established `pauliObservable` API, mirroring `pauliXObservable`; the `Y`-analogue that the library
lacked (the `Y`-eigenstate certifications of Exercise 4.1 need it as their observable). -/
def pauliYObservable : Observable qubit := pauliObservable ![0, 1, 0]

/-- The operator of the Pauli `Y` observable is `Matrix.toEuclideanCLM Concrete.pauliY`: the Pauli
direction `(0, 1, 0)` collapses `Concrete.pauliDot ![0, 1, 0]` to the concrete matrix
`Concrete.pauliY = !![0, -i; i, 0]`. -/
@[simp]
theorem pauliYObservable_op :
    pauliYObservable.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliY := by
  rw [pauliYObservable, pauliObservable_op]
  congr 1
  rw [Concrete.pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Concrete.pauliY]

/-- The **Pauli `Z` observable** on the qubit: the Pauli vector observable `n · σ` for the unit
direction `n = (0, 0, 1)`, i.e. `Z = pauliObservable ![0, 0, 1]`. Constructed through the
established `pauliObservable` API, mirroring `pauliXObservable`. -/
def pauliZObservable : Observable qubit := pauliObservable ![0, 0, 1]

/-- The operator of the Pauli `Z` observable is `Matrix.toEuclideanCLM Concrete.pauliZ`: the Pauli
direction `(0, 0, 1)` collapses `Concrete.pauliDot ![0, 0, 1]` to the concrete matrix
`Concrete.pauliZ = !![1, 0; 0, -1]`. -/
@[simp]
theorem pauliZObservable_op :
    pauliZObservable.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ := by
  rw [pauliZObservable, pauliObservable_op]
  congr 1
  rw [Concrete.pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Concrete.pauliZ]

/-! ### Operator-level products and (anti)commutators of the Pauli observables

The single-qubit Pauli operator identities `Z² = 1`, `{X, Z} = {Y, Z} = 0` (N&C eq. 2.75), and the
"raising-operator absorption" `i (X Z) + Y Z = i X + Y`, all lifted from the concrete `2 × 2`
matrices through the `⋆`-algebra map `Matrix.toEuclideanCLM`. They sit beside
`pauliXObservable_op_mul_self` (`X² = 1`) as the shared home for Pauli operator algebra. -/

/-- **`Z² = 1`:** the Pauli `Z` observable is an involution in the qubit's operator ring. The
special case of `pauliObservable_op_mul_self` at the unit vector `(0, 0, 1)`. -/
theorem pauliZObservable_op_mul_self :
    pauliZObservable.op * pauliZObservable.op = 1 := by
  rw [pauliZObservable]
  exact pauliObservable_op_mul_self
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons])

/-- **`Y² = 1`:** the Pauli `Y` observable is an involution in the qubit's operator ring. The
special case of `pauliObservable_op_mul_self` at the unit vector `(0, 1, 0)`. -/
theorem pauliYObservable_op_mul_self :
    pauliYObservable.op * pauliYObservable.op = 1 := by
  rw [pauliYObservable]
  exact pauliObservable_op_mul_self
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons])

/-- **`X Z = −Z X`:** the Pauli `X` and `Z` observables anticommute (N&C eq. 2.75), lifted to the
qubit operator ring through the `⋆`-algebra map `Matrix.toEuclideanCLM`. -/
theorem pauliXObservable_op_anticomm_pauliZObservable_op :
    pauliXObservable.op * pauliZObservable.op = -(pauliZObservable.op * pauliXObservable.op) := by
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
    (eq_neg_of_add_eq_zero_left Concrete.pauliX_anticomm_pauliZ)
  simp only [map_mul, map_neg] at h
  rw [pauliXObservable_op, pauliZObservable_op]
  exact h

/-- **`Y Z = −Z Y`:** the Pauli `Y` and `Z` observables anticommute (N&C eq. 2.75). -/
theorem pauliYObservable_op_anticomm_pauliZObservable_op :
    pauliYObservable.op * pauliZObservable.op = -(pauliZObservable.op * pauliYObservable.op) := by
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
    (eq_neg_of_add_eq_zero_left Concrete.pauliY_anticomm_pauliZ)
  simp only [map_mul, map_neg] at h
  rw [pauliYObservable_op, pauliZObservable_op]
  exact h

/-- **`X Y = −Y X`:** the Pauli `X` and `Y` observables anticommute (N&C eq. 2.75), the third member
of the anticommutation trio alongside `pauliXObservable_op_anticomm_pauliZObservable_op` and
`pauliYObservable_op_anticomm_pauliZObservable_op`. -/
theorem pauliXObservable_op_anticomm_pauliYObservable_op :
    pauliXObservable.op * pauliYObservable.op = -(pauliYObservable.op * pauliXObservable.op) := by
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
    (eq_neg_of_add_eq_zero_left Concrete.pauliX_anticomm_pauliY)
  simp only [map_mul, map_neg] at h
  rw [pauliXObservable_op, pauliYObservable_op]
  exact h

/-- **Raising-operator absorption `i (X Z) + Y Z = i X + Y`.** The single-qubit raising operator
`i X + Y` (proportional to `σ₊ = (X + i Y)/2` up to a phase) is fixed by *right* multiplication by
`Z`, i.e. `(i X + Y) Z = i X + Y`. Proved from the concrete `2 × 2` identity lifted through
`Matrix.toEuclideanCLM`. -/
theorem pauliRaising_op_mul_pauliZObservable_op :
    Complex.I • (pauliXObservable.op * pauliZObservable.op)
        + pauliYObservable.op * pauliZObservable.op
      = Complex.I • pauliXObservable.op + pauliYObservable.op := by
  have hmat : Complex.I • (Concrete.pauliX * Concrete.pauliZ) + Concrete.pauliY * Concrete.pauliZ
      = Complex.I • Concrete.pauliX + Concrete.pauliY := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliX, Concrete.pauliY, Concrete.pauliZ, Matrix.add_apply]
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) hmat
  simp only [map_add, map_mul, map_smul] at h
  rw [pauliXObservable_op, pauliYObservable_op, pauliZObservable_op]
  exact h

/-- **`Z Y = −i X`:** the Pauli `Z`·`Y` product (N&C eq. 2.40), lifted to the qubit operator ring
through the `⋆`-algebra map `Matrix.toEuclideanCLM`. -/
theorem pauliZObservable_op_mul_pauliYObservable_op :
    pauliZObservable.op * pauliYObservable.op = -Complex.I • pauliXObservable.op := by
  have hmat : Concrete.pauliZ * Concrete.pauliY = -Complex.I • Concrete.pauliX := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliZ, Concrete.pauliY, Concrete.pauliX, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.smul_apply]
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) hmat
  simp only [map_mul, map_smul] at h
  rw [pauliZObservable_op, pauliYObservable_op, pauliXObservable_op]
  exact h

/-- **Applying `X` to a `toLp` vector is `X *ᵥ`:** `X (toLp v) = toLp (Concrete.pauliX *ᵥ v)`. The
operator-application bridge that lifts a concrete eigenvalue equation `pauliX *ᵥ v = μ • v` to the
observable `X` (`Matrix.toEuclideanCLM_toLp`, whose `EuclideanSpace`-typed application is
brought to `X.op`'s form by `exact`). -/
theorem pauliXObservable_apply_toLp (v : Fin 2 → ℂ) :
    pauliXObservable.op (WithLp.toLp 2 v) = WithLp.toLp 2 (Concrete.pauliX.mulVec v) := by
  rw [pauliXObservable_op]; exact Matrix.toEuclideanCLM_toLp Concrete.pauliX v

/-- **Applying `Y` to a `toLp` vector is `Y *ᵥ`:** `Y (toLp v) = toLp (Concrete.pauliY *ᵥ v)`. -/
theorem pauliYObservable_apply_toLp (v : Fin 2 → ℂ) :
    pauliYObservable.op (WithLp.toLp 2 v) = WithLp.toLp 2 (Concrete.pauliY.mulVec v) := by
  rw [pauliYObservable_op]; exact Matrix.toEuclideanCLM_toLp Concrete.pauliY v

/-- **Applying `Z` to a `toLp` vector is `Z *ᵥ`:** `Z (toLp v) = toLp (Concrete.pauliZ *ᵥ v)`. -/
theorem pauliZObservable_apply_toLp (v : Fin 2 → ℂ) :
    pauliZObservable.op (WithLp.toLp 2 v) = WithLp.toLp 2 (Concrete.pauliZ.mulVec v) := by
  rw [pauliZObservable_op]; exact Matrix.toEuclideanCLM_toLp Concrete.pauliZ v

/-! ### Operator eigenvalue equations of the Pauli eigenvectors

The `X`/`Y`/`Z` observables act on the six normalized Pauli eigenvectors of Exercise 2.11
(`Concrete.xPlus`/…) as multiplication by `±1`, obtained from the concrete matrix eigenvalue
equations `Concrete.pauli*_mulVec_*` through the `_apply_toLp` bridges above. The `−1` cases state
the eigenvalue as `((-1 : ℝ) : ℂ)` so that each feeds `Observable.hasEigenstate_of_smul` directly in
`AxQM/NC/Ch4/Exercise4_1.lean` (which reads the eigenvalue as a real `μ`). -/

/-- `X |+⟩ = |+⟩`: `X`'s `+1` operator eigenvalue equation on `Concrete.xPlus`. -/
theorem pauliXObservable_apply_xPlus :
    pauliXObservable.op (WithLp.toLp 2 Concrete.xPlus)
      = (1 : ℂ) • WithLp.toLp 2 Concrete.xPlus := by
  rw [pauliXObservable_apply_toLp, Concrete.pauliX_mulVec_xPlus, WithLp.toLp_smul]

/-- `X |-⟩ = -|-⟩`: `X`'s `-1` operator eigenvalue equation on `Concrete.xMinus`. -/
theorem pauliXObservable_apply_xMinus :
    pauliXObservable.op (WithLp.toLp 2 Concrete.xMinus)
      = ((-1 : ℝ) : ℂ) • WithLp.toLp 2 Concrete.xMinus := by
  rw [pauliXObservable_apply_toLp, Concrete.pauliX_mulVec_xMinus, WithLp.toLp_smul,
    Complex.ofReal_neg, Complex.ofReal_one]

/-- `Y |+i⟩ = |+i⟩`: `Y`'s `+1` operator eigenvalue equation on `Concrete.yPlus`. -/
theorem pauliYObservable_apply_yPlus :
    pauliYObservable.op (WithLp.toLp 2 Concrete.yPlus)
      = (1 : ℂ) • WithLp.toLp 2 Concrete.yPlus := by
  rw [pauliYObservable_apply_toLp, Concrete.pauliY_mulVec_yPlus, WithLp.toLp_smul]

/-- `Y |-i⟩ = -|-i⟩`: `Y`'s `-1` operator eigenvalue equation on `Concrete.yMinus`. -/
theorem pauliYObservable_apply_yMinus :
    pauliYObservable.op (WithLp.toLp 2 Concrete.yMinus)
      = ((-1 : ℝ) : ℂ) • WithLp.toLp 2 Concrete.yMinus := by
  rw [pauliYObservable_apply_toLp, Concrete.pauliY_mulVec_yMinus, WithLp.toLp_smul,
    Complex.ofReal_neg, Complex.ofReal_one]

/-- `Z |0⟩ = |0⟩`: `Z`'s `+1` operator eigenvalue equation on `Concrete.ket 0`. -/
theorem pauliZObservable_apply_ket0 :
    pauliZObservable.op (WithLp.toLp 2 (Concrete.ket 0))
      = (1 : ℂ) • WithLp.toLp 2 (Concrete.ket 0) := by
  rw [pauliZObservable_apply_toLp, Concrete.pauliZ_mulVec_ket_zero, WithLp.toLp_smul]

/-- `Z |1⟩ = -|1⟩`: `Z`'s `-1` operator eigenvalue equation on `Concrete.ket 1`. -/
theorem pauliZObservable_apply_ket1 :
    pauliZObservable.op (WithLp.toLp 2 (Concrete.ket 1))
      = ((-1 : ℝ) : ℂ) • WithLp.toLp 2 (Concrete.ket 1) := by
  rw [pauliZObservable_apply_toLp, Concrete.pauliZ_mulVec_ket_one, WithLp.toLp_smul,
    Complex.ofReal_neg, Complex.ofReal_one]

/-- **`Z |i⟩ = (-1)ⁱ |i⟩`** at the observable operator level: the Pauli `Z` observable acts on the
computational-basis ket `|i⟩` by the eigenvalue `(-1)ⁱ`. The uniform (`i : Fin 2`) form of
`pauliZObservable_apply_ket0` / `pauliZObservable_apply_ket1`, the shared eigenvalue equation
used wherever a `Z` acts on a computational-basis register (e.g. the `Z₁Z₂` coupling Hamiltonian,
the bit-flip syndrome observables). -/
theorem pauliZObservable_op_apply_qubitBasis (i : Fin 2) :
    pauliZObservable.op (qubitBasis i).vec = (-1 : ℂ) ^ (i : ℕ) • (qubitBasis i).vec := by
  fin_cases i
  · change pauliZObservable.op (WithLp.toLp 2 (Concrete.ket 0))
      = (-1 : ℂ) ^ (0 : ℕ) • WithLp.toLp 2 (Concrete.ket 0)
    rw [pow_zero]
    exact pauliZObservable_apply_ket0
  · change pauliZObservable.op (WithLp.toLp 2 (Concrete.ket 1))
      = (-1 : ℂ) ^ (1 : ℕ) • WithLp.toLp 2 (Concrete.ket 1)
    rw [pow_one]
    have h1 := pauliZObservable_apply_ket1
    simp only [Complex.ofReal_neg, Complex.ofReal_one] at h1
    exact h1

/-- **`X |i⟩ = |i ⊕ 1⟩`** at the observable operator level: the Pauli `X` observable flips the
computational-basis ket `|i⟩`. The `X` analogue of `pauliZObservable_op_apply_qubitBasis`, reduced
to the matrix action `pauliX ·ᵥ ket i = ket (i+1)` of `Concrete.pauliX = !![0,1;1,0]` on the
standard basis vector `Concrete.ket i`; the shared bit-flip equation used wherever an `X` acts on a
computational-basis register (e.g. the `X⊗X⊗X` block sign-readout of the Shor code). -/
theorem pauliXObservable_op_apply_qubitBasis (i : Fin 2) :
    pauliXObservable.op (qubitBasis i).vec = (qubitBasis (i + 1)).vec := by
  have hket : ∀ k : Fin 2, (qubitBasis k).vec = WithLp.toLp 2 (Concrete.ket k) := fun k => by
    rw [qubitBasis_vec]; rfl
  rw [hket, pauliXObservable_apply_toLp, Concrete.pauliX_mulVec_ket, hket]

/-- **`Y |i⟩ = i · (-1)ⁱ · |i ⊕ 1⟩`** at the observable operator level: the Pauli `Y` observable
flips the computational-basis ket `|i⟩` with a phase (`Y|0⟩ = i|1⟩`, `Y|1⟩ = -i|0⟩`). The `Y`
analogue of `pauliXObservable_op_apply_qubitBasis` / `pauliZObservable_op_apply_qubitBasis`, reduced
to the matrix action `pauliY ·ᵥ ket i = i(-1)ⁱ • ket (i+1)` of `Concrete.pauliY = !![0,-I;I,0]` on
the standard basis vector `Concrete.ket i`. -/
theorem pauliYObservable_op_apply_qubitBasis (i : Fin 2) :
    pauliYObservable.op (qubitBasis i).vec
      = (Complex.I * (-1) ^ (i : ℕ)) • (qubitBasis (i + 1)).vec := by
  have hket : ∀ k : Fin 2, (qubitBasis k).vec = WithLp.toLp 2 (Concrete.ket k) := fun k => by
    rw [qubitBasis_vec]; rfl
  rw [hket, pauliYObservable_apply_toLp, Concrete.pauliY_mulVec_ket, WithLp.toLp_smul, hket (i + 1)]
  rfl

/-- **Orthonormality of the computational basis:** `⟨i|j⟩ = δᵢⱼ`. The inner product of the
computational-basis states `|i⟩`, `|j⟩` of the qubit is `1` when `i = j` and `0` otherwise, since
`|i⟩ = EuclideanSpace.single i 1` is the standard orthonormal basis. -/
theorem qubitBasis_inner_qubitBasis (i j : Fin 2) :
    inner ℂ (qubitBasis i).vec (qubitBasis j).vec = if i = j then (1 : ℂ) else 0 := by
  change inner ℂ (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j (1 : ℂ)) = _
  rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]

/-- **The qubit computational basis is orthonormal** as a family of state vectors:
`Orthonormal ℂ (fun i => |i⟩)`, from `qubitBasis_inner_qubitBasis` (`⟨i|j⟩ = δᵢⱼ`) via
`orthonormal_iff_ite`. The single-qubit analogue of `bellState_orthonormal`; a citable
computational-basis fact reused wherever a Schmidt/spectral decomposition uses `{|0⟩, |1⟩}` as an
orthonormal frame. -/
theorem qubitBasis_vec_orthonormal : Orthonormal ℂ (fun i => (qubitBasis i).vec) :=
  orthonormal_iff_ite.mpr qubitBasis_inner_qubitBasis

/-- **The computational basis `|0⟩, |1⟩` as a `ℂ`-basis of the qubit state space.** The two
computational kets are orthonormal (`qubitBasis_vec_orthonormal`) and number `2 = finrank ℂ
qubit.space` (`finrank_qubit_space`), so they form a `Module.Basis (Fin 2) ℂ qubit.space`. This is
the qubit counterpart of `quditOrthonormalBasis`, packaged as a `Module.Basis` for use with
`Basis.ext` / `Basis.piTensorProduct` — e.g. to reduce a computational-basis truth table to an
`Evolution` identity (`Evolution.ext_qubitBasis`). -/
noncomputable def qubitModuleBasis : Module.Basis (Fin 2) ℂ qubit.space :=
  basisOfLinearIndependentOfCardEqFinrank
    qubitBasis_vec_orthonormal.linearIndependent
    (by rw [Fintype.card_fin, finrank_qubit_space])

/-- The `i`-th vector of `qubitModuleBasis` is the computational ket `|i⟩`, `(qubitBasis i).vec`. -/
@[simp] theorem qubitModuleBasis_apply (i : Fin 2) :
    qubitModuleBasis i = (qubitBasis i).vec :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

/-- **The computational basis `qubitModuleBasis` is orthonormal.** The `Module.Basis`-form of
`qubitBasis_vec_orthonormal`, i.e. `Orthonormal ℂ ⇑qubitModuleBasis`, since the two agree pointwise
(`qubitModuleBasis_apply`). Feeds `Orthonormal.basisTensorProduct` to orthonormalize multi-qubit
tensor bases. -/
theorem qubitModuleBasis_orthonormal : Orthonormal ℂ ⇑qubitModuleBasis := by
  rw [show (⇑qubitModuleBasis) = (fun i => (qubitBasis i).vec) from funext qubitModuleBasis_apply]
  exact qubitBasis_vec_orthonormal

/-- **Matrix element of `X` in the computational basis:** `⟨i|X|j⟩ = Xᵢⱼ`. The inner product
`⟨i|X|j⟩` is the `(i, j)` entry of the Pauli matrix `Concrete.pauliX = !![0, 1; 1, 0]`, read off
via the matrix-to-operator bridge `Matrix.toEuclideanCLM`. -/
theorem pauliXObservable_inner_qubitBasis (i j : Fin 2) :
    inner ℂ (qubitBasis i).vec (pauliXObservable.op (qubitBasis j).vec) = Concrete.pauliX i j := by
  rw [pauliXObservable_op]
  change inner ℂ (EuclideanSpace.single i (1 : ℂ))
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX)
        (EuclideanSpace.single j 1)) = _
  rw [EuclideanSpace.inner_single_left, Matrix.ofLp_toEuclideanCLM]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mulVec, dotProduct, Concrete.pauliX]

/-- **Matrix element of `Z` in the computational basis:** `⟨i|Z|j⟩ = Zᵢⱼ`. The inner product
`⟨i|Z|j⟩` is the `(i, j)` entry of the Pauli matrix `Concrete.pauliZ = !![1, 0; 0, -1]`, read off
via the matrix-to-operator bridge `Matrix.toEuclideanCLM`. -/
theorem pauliZObservable_inner_qubitBasis (i j : Fin 2) :
    inner ℂ (qubitBasis i).vec (pauliZObservable.op (qubitBasis j).vec) = Concrete.pauliZ i j := by
  rw [pauliZObservable_op]
  change inner ℂ (EuclideanSpace.single i (1 : ℂ))
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ)
        (EuclideanSpace.single j 1)) = _
  rw [EuclideanSpace.inner_single_left, Matrix.ofLp_toEuclideanCLM]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mulVec, dotProduct, Concrete.pauliZ]

/-! ### Traces of the Pauli observables (single-qubit Hilbert–Schmidt building blocks)

The single-qubit trace facts underlying two-qubit Hilbert–Schmidt orthogonality: the Paulis are
traceless (`tr X = tr Y = tr Z = 0`), `tr 1 = 2`, and the product `X Y = i Z` (hence `tr(XY) = 0`).
Each operator trace reduces to the matrix trace through `Matrix.trace_toEuclideanCLM`. -/

/-- The identity on a single qubit has **trace `2`** (`= dim`). -/
theorem trace_one_qubit :
    LinearMap.trace ℂ qubit.space (1 : qubit.space →ₗ[ℂ] qubit.space) = 2 := by
  rw [LinearMap.trace_one, finrank_qubit_space]; norm_num

/-- The Pauli `X` observable is **traceless**: `tr X = 0`. -/
theorem trace_pauliXObservable : LinearMap.trace ℂ qubit.space ↑pauliXObservable.op = 0 := by
  rw [pauliXObservable_op]; exact (Matrix.trace_toEuclideanCLM _).trans Concrete.pauliX_trace

/-- The Pauli `Y` observable is **traceless**: `tr Y = 0`. -/
theorem trace_pauliYObservable : LinearMap.trace ℂ qubit.space ↑pauliYObservable.op = 0 := by
  rw [pauliYObservable_op]; exact (Matrix.trace_toEuclideanCLM _).trans Concrete.pauliY_trace

/-- The Pauli `Z` observable is **traceless**: `tr Z = 0`. -/
theorem trace_pauliZObservable : LinearMap.trace ℂ qubit.space ↑pauliZObservable.op = 0 := by
  rw [pauliZObservable_op]; exact (Matrix.trace_toEuclideanCLM _).trans Concrete.pauliZ_trace

/-- **`X Y = i Z`** in the qubit operator ring (N&C eq. 2.40), lifted through
`Matrix.toEuclideanCLM`. -/
theorem pauliXObservable_op_mul_pauliYObservable_op :
    pauliXObservable.op * pauliYObservable.op = Complex.I • pauliZObservable.op := by
  have hmat : Concrete.pauliX * Concrete.pauliY = Complex.I • Concrete.pauliZ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliX, Concrete.pauliY, Concrete.pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply]
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) hmat
  simp only [map_mul, map_smul] at h
  rw [pauliXObservable_op, pauliYObservable_op, pauliZObservable_op]
  exact h

/-- **`tr(X Y) = 0`:** the Pauli `X`·`Y` product is traceless (`XY = iZ`, itself traceless). -/
theorem trace_pauliXObservable_op_mul_pauliYObservable_op :
    LinearMap.trace ℂ qubit.space ↑(pauliXObservable.op * pauliYObservable.op) = 0 := by
  rw [pauliXObservable_op_mul_pauliYObservable_op, ContinuousLinearMap.toLinearMap_smul, map_smul,
    trace_pauliZObservable, smul_zero]

end AxQM
