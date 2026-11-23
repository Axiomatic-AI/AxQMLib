/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardGate
import AxQM.Postulates.API.PureState
import AxQM.Postulates.API.Eigenstate
import AxQM.Postulates.Observable
import Mathlib.Tactic.LinearCombination

/-!
# AxQM.Postulates.API — eigenvalues and eigenvectors of the Hadamard gate

The eigenvalues and eigenvectors of the Hadamard gate: **Nielsen & Chuang, Exercise 2.53**
("What are the eigenvalues and eigenvectors of `H`?", §2.2.2, p. 82). The Hadamard gate
`H = (1/√2)!![1,1;1,-1]` is both unitary (Exercise 2.51, `hadamardGate : Evolution qubit`) and
**Hermitian**, so it is a legitimate `Observable qubit` — a structure whose real spectrum is a set
of measurement values. Its eigenvalues are the possible measurement outcomes and its eigenvectors
the corresponding eigenstates, which is exactly what the exercise asks for. We therefore state the
eigendecomposition for the `Observable`.

## The answer

`H` is Hermitian with `H² = I` (Exercise 2.52), so its eigenvalues are `±1`. The (normalized)
eigenvectors are, in the computational basis,

* `|h₊⟩ ∝ (1, √2 − 1)` with eigenvalue `+1`;
* `|h₋⟩ ∝ (√2 − 1, −1)` with eigenvalue `−1`

(equivalently `cos(π/8)|0⟩ + sin(π/8)|1⟩` and `sin(π/8)|0⟩ − cos(π/8)|1⟩`: `H` is the reflection
about the line at angle `π/8`). The eigenvalues are *exactly* `±1` — nothing else is an eigenvalue,
because `H² = I` forces `μ² = 1` — and the two eigenvectors are orthogonal (an orthonormal pair).

## What is formalised

* the general eigenstate notions `Observable.HasEigenstate A μ ψ` (the predicate that the pure
  state `ψ` is an eigenstate of the observable `A` with real eigenvalue `μ`: `A ψ = μ ψ`),
  `Observable.hasEigenstate_of_smul` (an eigenstate is unchanged by rescaling the underlying
  vector), and `PureState.expectation_of_hasEigenstate` (the expectation value in an eigenstate *is*
  the eigenvalue — the physical meaning of "eigenvalue"), which are used here and are in
  `AxQM/Postulates/API/Eigenstate.lean` (imported above); and
  `Observable.eigenvalue_eq_of_op_mul_self` (an involution `A² = 1` has only `±1` as
  eigenvalues — the exhaustiveness lever), which is proved here.
* `hadamardObservable : Observable qubit` — the Hadamard gate as an observable, with the same
  operator as `hadamardGate` (`hadamardObservable_op_eq_hadamardGate`), and `H² = I`
  (`hadamardObservable_op_mul_self`).
* `hadamardEigenstatePlus`, `hadamardEigenstateMinus : PureState qubit` — the normalized
  eigenstates, with the eigenvalue equations `hadamardObservable_apply_eigenvecPlus`
  / `_eigenvecMinus` (`H v = ±v` on the unnormalized directions).
* `hadamardEigenstate_orthogonal` — the two eigenstates are orthogonal.

That these are eigenstates with eigenvalues `±1`
(`Observable.HasEigenstate`), that the eigenvalues are *exactly* `±1`
(`hadamardObservable_eigenvalue_eq_one_or_neg_one`), and that `⟪H⟫ = ±1` in each, is stated in
`AxQM/NC/Ch2/Exercise2_53.lean`.

## Design notes

* **Observable, not evolution.** Eigenvalues/eigenvectors are the spectral content of an operator;
  real eigenvalues signal Hermiticity, which is what `Observable` bundles. `H` really
  is self-adjoint (`Concrete.hadamardC_isHermitian`), so presenting the eigendecomposition through
  `Observable` is faithful — and `hadamardObservable_op_eq_hadamardGate` records that it is the same
  operator as the Exercise 2.51 gate. The unitary/`H²=I` facts belong to Exercises 2.51/2.52.
* **Linear reduction.** The eigenvalue equation `A v = μ v` is linear, so it is proved once on the
  simple *unnormalized* directions `(1, √2−1)` / `(√2−1, −1)` (`hadamardC_mulVec_plus/minus`); the
  messy normalization constant enters only the `‖·‖ = 1` obligation of `PureState`, via
  `hasEigenstate_of_smul`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

open Matrix Complex

variable {S : QSystem}

/-! ### Involutive observables have `±1` spectrum

The general eigenstate predicate `Observable.HasEigenstate` and its helpers
`Observable.hasEigenstate_of_smul` / `PureState.expectation_of_hasEigenstate` are in
`AxQM/Postulates/API/Eigenstate.lean` (imported above), and are also used in
`AxQM/Postulates/API/Variance.lean`. -/

/-- **An involutive observable has only `±1` as eigenvalues.** If `A² = 1` (in the operator ring),
then every eigenvalue `μ` of `A` satisfies `μ = 1` or `μ = −1`. Applying `A` twice to an eigenstate
`A ψ = μ ψ` gives `ψ = A² ψ = μ² ψ`, and `ψ ≠ 0` (it is normalized) forces `μ² = 1`. This is the
`⊆` (exhaustiveness) direction of an eigenvalue computation for any self-adjoint involution. -/
theorem Observable.eigenvalue_eq_of_op_mul_self {A : Observable S} (hA : A.op * A.op = 1)
    {μ : ℝ} {ψ : PureState S} (h : A.HasEigenstate μ ψ) : μ = 1 ∨ μ = -1 := by
  have hop : A.op ψ.vec = (μ : ℂ) • ψ.vec := h
  have hsq : A.op (A.op ψ.vec) = ψ.vec := by
    have := congrArg (fun T : S →L[ℂ] S => T ψ.vec) hA
    simpa [mul_apply_eq_comp] using this
  rw [hop, map_smul, hop, smul_smul] at hsq
  have hne : ψ.vec ≠ 0 := fun hz => by
    have := ψ.normalized; rw [hz, norm_zero] at this; norm_num at this
  have hc : (μ : ℂ) * (μ : ℂ) = 1 := by
    have hz : (((μ : ℂ) * (μ : ℂ)) - 1) • ψ.vec = 0 := by rw [sub_smul, hsq, one_smul, sub_self]
    rcases smul_eq_zero.mp hz with h' | h'
    · linear_combination h'
    · exact absurd h' hne
  exact mul_self_eq_one_iff.mp (by exact_mod_cast hc)

/-! ### The Hadamard observable and its complex-matrix eigen-equations -/

/-- The **Hadamard gate as an observable** on the qubit: the operator of `Concrete.hadamardC`
promoted through `Matrix.toEuclideanCLM`. It is self-adjoint because `H` is Hermitian
(`Concrete.hadamardC_isHermitian`); this is the same operator as `hadamardGate`
(`hadamardObservable_op_eq_hadamardGate`). Its `±1` spectrum is the content of Exercise 2.53. -/
def hadamardObservable : Observable qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC
  selfAdjoint :=
    Concrete.hadamardC_isHermitian.isSelfAdjoint.map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))

/-- The operator of `hadamardObservable` is the `Matrix.toEuclideanCLM` image of the concrete
Hadamard matrix `Concrete.hadamardC`. A `simp` bridge exposing the underlying operator. -/
@[simp]
theorem hadamardObservable_op :
    hadamardObservable.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC :=
  rfl

/-- `hadamardObservable` and `hadamardGate` (Exercise 2.51) are the **same operator**: the Hadamard
matrix `H` viewed as a self-adjoint observable and as a unitary evolution. This records that the
eigendecomposition below is of the very gate of Exercise 2.51. -/
theorem hadamardObservable_op_eq_hadamardGate : hadamardObservable.op = hadamardGate.op := rfl

/-- **`H² = I` at the operator level** (Exercise 2.52's content, `Concrete.hadamardC_mul_self`,
transported through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` by `map_mul` / `map_one`).
This is the involution property that pins the Hadamard eigenvalues to `±1`. -/
theorem hadamardObservable_op_mul_self :
    hadamardObservable.op * hadamardObservable.op = 1 := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC
       * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC = 1
  rw [← map_mul, Concrete.hadamardC_mul_self, map_one]

/-- `(√2 : ℂ) · (√2 : ℂ) = 2`. -/
private theorem sqrt_two_mul_self : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- `(√2 : ℂ) ≠ 0`. -/
private theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]; positivity

/-- **Eigenvalue equation for `+1` at the matrix level:** `H · (1, √2−1) = (1, √2−1)`, i.e. the
column vector `(1, √2−1)` is a `+1`-eigenvector of the concrete Hadamard matrix. Proved from the
`(1/√2)`-free identity `!![1,1;1,-1] · (1, √2−1) = √2 · (1, √2−1)` after cancelling the `1/√2`. -/
theorem hadamardC_mulVec_plus :
    Concrete.hadamardC *ᵥ ![1, (Real.sqrt 2 - 1 : ℂ)] = (1 : ℂ) • ![1, (Real.sqrt 2 - 1 : ℂ)] := by
  have base : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![1, (Real.sqrt 2 - 1 : ℂ)]
      = (Real.sqrt 2 : ℂ) • ![1, (Real.sqrt 2 - 1 : ℂ)] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -sqrt_two_mul_self
  rw [Concrete.hadamardC, Matrix.smul_mulVec, base, smul_smul,
    inv_mul_cancel₀ sqrt_two_ne_zero, one_smul]

/-- **Eigenvalue equation for `−1` at the matrix level:** `H · (√2−1, −1) = −(√2−1, −1)`, i.e.
`(√2−1, −1)` is a `−1`-eigenvector of the concrete Hadamard matrix. -/
theorem hadamardC_mulVec_minus :
    Concrete.hadamardC *ᵥ ![(Real.sqrt 2 - 1 : ℂ), -1]
      = (-1 : ℂ) • ![(Real.sqrt 2 - 1 : ℂ), -1] := by
  have base : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![(Real.sqrt 2 - 1 : ℂ), -1]
      = (-(Real.sqrt 2 : ℂ)) • ![(Real.sqrt 2 - 1 : ℂ), -1] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination sqrt_two_mul_self
  rw [Concrete.hadamardC, Matrix.smul_mulVec, base, smul_smul,
    show (Real.sqrt 2 : ℂ)⁻¹ * (-(Real.sqrt 2)) = -1 by
      rw [mul_neg, inv_mul_cancel₀ sqrt_two_ne_zero]]

/-! ### The eigenvectors and normalized eigenstates -/

/-- The unnormalized `+1`-eigenvector `(1, √2 − 1)` of `H`, as a qubit vector. -/
def hadamardEigenvecPlus : qubit := WithLp.toLp 2 ![1, (Real.sqrt 2 - 1 : ℂ)]

/-- The unnormalized `−1`-eigenvector `(√2 − 1, −1)` of `H`, as a qubit vector. -/
def hadamardEigenvecMinus : qubit := WithLp.toLp 2 ![(Real.sqrt 2 - 1 : ℂ), -1]

/-- `hadamardObservable` acts on `(1, √2−1)` as multiplication by `+1` (operator form of
`hadamardC_mulVec_plus`). -/
theorem hadamardObservable_apply_eigenvecPlus :
    hadamardObservable.op hadamardEigenvecPlus = (1 : ℂ) • hadamardEigenvecPlus := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC
      (WithLp.toLp 2 ![1, (Real.sqrt 2 - 1 : ℂ)])
      = (1 : ℂ) • WithLp.toLp 2 ![1, (Real.sqrt 2 - 1 : ℂ)]
  rw [Matrix.toEuclideanCLM_toLp, hadamardC_mulVec_plus, WithLp.toLp_smul]

/-- `hadamardObservable` acts on `(√2−1, −1)` as multiplication by `−1` (operator form of
`hadamardC_mulVec_minus`). -/
theorem hadamardObservable_apply_eigenvecMinus :
    hadamardObservable.op hadamardEigenvecMinus = (-1 : ℂ) • hadamardEigenvecMinus := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC
      (WithLp.toLp 2 ![(Real.sqrt 2 - 1 : ℂ), -1])
      = (-1 : ℂ) • WithLp.toLp 2 ![(Real.sqrt 2 - 1 : ℂ), -1]
  rw [Matrix.toEuclideanCLM_toLp, hadamardC_mulVec_minus, WithLp.toLp_smul]

/-- `(1, √2−1)` is nonzero (its first component is `1`), so it is a genuine eigenvector. -/
theorem hadamardEigenvecPlus_ne_zero : hadamardEigenvecPlus ≠ 0 := by
  intro h
  have : (WithLp.ofLp hadamardEigenvecPlus) 0 = 0 := by rw [h]; rfl
  simp [hadamardEigenvecPlus, WithLp.ofLp_toLp] at this

/-- `(√2−1, −1)` is nonzero (its second component is `−1`), so it is a genuine eigenvector. -/
theorem hadamardEigenvecMinus_ne_zero : hadamardEigenvecMinus ≠ 0 := by
  intro h
  have : (WithLp.ofLp hadamardEigenvecMinus) 1 = 0 := by rw [h]; rfl
  simp [hadamardEigenvecMinus, WithLp.ofLp_toLp] at this

/-! ### The normalized eigenstates -/

/-- The normalized `+1`-eigenstate `|h₊⟩` of the Hadamard observable, via the shared
`PureState.normalize`. -/
def hadamardEigenstatePlus : PureState qubit :=
  PureState.normalize hadamardEigenvecPlus hadamardEigenvecPlus_ne_zero

/-- The normalized `−1`-eigenstate `|h₋⟩` of the Hadamard observable, via the shared
`PureState.normalize`. -/
def hadamardEigenstateMinus : PureState qubit :=
  PureState.normalize hadamardEigenvecMinus hadamardEigenvecMinus_ne_zero

/-- The underlying vector of `|h₊⟩` is `‖v₊‖⁻¹ • v₊`, a scalar multiple of the `+1`-eigenvector
`v₊ = (1, √2−1)`. The bridge used to transport the eigenvalue equation to the normalized state. -/
theorem hadamardEigenstatePlus_vec :
    hadamardEigenstatePlus.vec
      = ((‖hadamardEigenvecPlus‖ : ℝ) : ℂ)⁻¹ • hadamardEigenvecPlus := rfl

/-- The underlying vector of `|h₋⟩` is `‖v₋‖⁻¹ • v₋`, a scalar multiple of the `−1`-eigenvector
`v₋ = (√2−1, −1)`. -/
theorem hadamardEigenstateMinus_vec :
    hadamardEigenstateMinus.vec
      = ((‖hadamardEigenvecMinus‖ : ℝ) : ℂ)⁻¹ • hadamardEigenvecMinus := rfl

/-- The two unnormalized Hadamard eigenvectors `(1, √2−1)` and `(√2−1, −1)` are orthogonal:
`⟪(1, √2−1), (√2−1, −1)⟫ = (√2−1) − (√2−1) = 0`. -/
theorem hadamardEigenvec_orthogonal :
    ⟪hadamardEigenvecPlus, hadamardEigenvecMinus⟫_ℂ = 0 := by
  change ⟪(WithLp.toLp 2 ![1, (Real.sqrt 2 - 1 : ℂ)] : EuclideanSpace ℂ (Fin 2)),
    WithLp.toLp 2 ![(Real.sqrt 2 - 1 : ℂ), -1]⟫_ℂ = 0
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, Complex.conj_ofReal]

/-- The two Hadamard eigenstates are **orthogonal** — an orthonormal pair, as befits eigenvectors of
a self-adjoint operator for distinct eigenvalues. (That `±1` are *all* the eigenvalues is proved
separately, from `H² = I`, by `hadamardObservable_eigenvalue_eq_one_or_neg_one`.) -/
theorem hadamardEigenstate_orthogonal :
    ⟪hadamardEigenstatePlus.vec, hadamardEigenstateMinus.vec⟫_ℂ = 0 := by
  unfold hadamardEigenstatePlus hadamardEigenstateMinus
  simp only [PureState.normalize_vec, inner_smul_left, inner_smul_right,
    hadamardEigenvec_orthogonal, mul_zero]

end AxQM
