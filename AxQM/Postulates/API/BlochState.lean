/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qubit
import AxQM.Concrete.BlochMatrix
import AxQM.Concrete.BlochPureState
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Postulates.API — the qubit Bloch state `ρ = ½(I + r·σ)`

The promotion of the concrete Bloch matrix `Concrete.blochMatrix r = ½(I + r·σ)`
to a genuine density operator of the `qubit`, for a Bloch vector `r` in the closed unit ball
(Nielsen & Chuang, Exercise 2.72(1)(2)).

* `blochState r h` — for a real three-vector `r` with `‖r‖² = r₀² + r₁² + r₂² ≤ 1`, the **state**
  `½(I + r·σ)` of the qubit: the concrete Hermitian trace-one matrix `Concrete.blochMatrix r`
  promoted to a continuous linear operator through the C\*-algebra isomorphism
  `Matrix.toEuclideanCLM`, packaged as a `State qubit`. It is a density operator because
  `Concrete.blochMatrix r` is positive semidefinite (`Concrete.blochMatrix_posSemidef_iff`, using
  `‖r‖² ≤ 1`) and has trace one (`Concrete.blochMatrix_trace`), both transported across the
  isomorphism. This is the same bridge route used by `pauliObservable`.
* `blochState_op` — exposes the underlying operator `Matrix.toEuclideanCLM (Concrete.blochMatrix
  r)`.
* `blochState_zero_op` — **`(blochState 0).op = ½ I`** (Nielsen & Chuang, Exercise 2.72(2)): the
  state with Bloch vector `r⃗ = 0` is the maximally mixed state `I/2`. This identifies the operator;
  together with the correspondence/uniqueness theorems in `AxQM/NC/Ch2/Exercise2_72.lean` it answers
  part (2) ("the Bloch vector representation of `ρ = I/2` is `r⃗ = 0`").
* `blochPureState θ φ` — the **§1.2 pure state** `|ψ(θ,φ)⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩`
  (Nielsen & Chuang eq. 1.4) as a `PureState qubit`, the concrete unit vector `Concrete.blochKet θ
  φ` embedded into `EuclideanSpace` (normalization `cos²(θ/2) + sin²(θ/2) = 1`).
* `blochPureState_toState_op` — **`|ψ(θ,φ)⟩⟨ψ(θ,φ)| = Matrix.toEuclideanCLM (Concrete.blochMatrix
  (blochSphereVector θ φ))`** (Nielsen & Chuang, Exercise 2.72(4)): the density
  operator of the §1.2 pure state is the Bloch state of the §1.2 Cartesian vector. This is the
  content behind the state-level coincidence in `AxQM/NC/Ch2/Exercise2_72.lean`.

The construction and its inverse (the density-operator correspondence) rest on
two general matrix↔operator bridges, in
`ToMathlib/Analysis/CStarAlgebra/MatrixToEuclideanCLM.lean`:
`Matrix.isPositive_toEuclideanCLM_iff` (operator positivity `↔` matrix `PosSemidef`) and
`Matrix.trace_toEuclideanCLM` (operator trace `= A.trace`).

## Design notes

* The bridge `Matrix.toEuclideanCLM` is a `⋆`-algebra *equivalence*, so it preserves positivity and
  trace (through its coercion to `Matrix.toEuclideanLin`). Building `blochState` on the concrete
  matrix layer keeps every analytic fact (positivity, trace, determinant) in `Concrete/` and reuses
  it here with no operator-level recomputation.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

/-- The **Bloch state** `ρ = ½(I + r·σ)` of the qubit, for a Bloch vector `r` in the closed unit
ball `‖r‖² = r₀² + r₁² + r₂² ≤ 1` (Nielsen & Chuang, Exercise 2.72(1), eq. 2.175). Its density
operator is the concrete matrix `Concrete.blochMatrix r` promoted through the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM`; it is positive because `Concrete.blochMatrix r` is positive
semidefinite (`Concrete.blochMatrix_posSemidef_iff`, using `‖r‖² ≤ 1`) and of trace one
(`Concrete.blochMatrix_trace`). -/
def blochState (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) : State qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix r)
  isDensity := by
    have h' : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix
        r)).IsDensityOp := by
      rw [ContinuousLinearMap.isDensityOp_iff]
      refine ⟨?_, ?_⟩
      · exact (Matrix.isPositive_toEuclideanCLM_iff _).mpr
          ((Concrete.blochMatrix_posSemidef_iff r).mpr h)
      · exact (Matrix.trace_toEuclideanCLM _).trans (Concrete.blochMatrix_trace r)
    exact h'

/-- The underlying density operator of `blochState r h` is the `Matrix.toEuclideanCLM` image of the
concrete Bloch matrix `Concrete.blochMatrix r`. A `simp` lemma exposing the operator. -/
@[simp]
theorem blochState_op (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    (blochState r h).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix r) :=
  rfl

/-- **Congruence for the Bloch state in its Bloch vector.** Equal Bloch vectors give equal Bloch
states: `r = s` implies `blochState r hr = blochState s hs`, regardless of the (proof-irrelevant)
ball-membership witnesses `hr`, `hs`. -/
theorem blochState_congr {r s : Fin 3 → ℝ} (hrs : r = s)
    {hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1} {hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 ≤ 1} :
    blochState r hr = blochState s hs := by
  subst hrs; rfl

/-- **`(blochState 0).op = ½ I` (Nielsen & Chuang, Exercise 2.72(2)).** The state with Bloch vector
`r⃗ = 0` has density operator `I/2`, the maximally mixed state of the qubit: `Concrete.blochMatrix 0
= ½ I` (`Concrete.blochMatrix_zero`) and `Matrix.toEuclideanCLM` carries `½ I` to `½·1`. This is
the operator content of part (2): the Bloch vector representation of `ρ = I/2` is `r⃗ = 0`. -/
theorem blochState_zero_op :
    (blochState (0 : Fin 3 → ℝ) (by simp)).op = (2⁻¹ : ℂ) • 1 := by
  rw [blochState_op, Concrete.blochMatrix_zero, map_smul, map_one]
  rfl

/-- The **§1.2 pure state** `|ψ(θ,φ)⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩` of the qubit (Nielsen &
Chuang eq. 1.4), as a `PureState qubit`: the concrete unit vector `Concrete.blochKet θ φ` embedded
into `EuclideanSpace ℂ (Fin 2)`. It is normalized because `‖cos(θ/2)‖² + ‖e^{iφ} sin(θ/2)‖²
= cos²(θ/2) + sin²(θ/2) = 1` (`‖e^{iφ}‖ = 1`). Its Bloch vector is computed in
`blochPureState_toState_op` (Exercise 2.72(4)). -/
noncomputable def blochPureState (θ φ : ℝ) : PureState qubit where
  vec := WithLp.toLp 2 (Concrete.blochKet θ φ)
  normalized := by
    change ‖(WithLp.toLp 2 (Concrete.blochKet θ φ) : EuclideanSpace ℂ (Fin 2))‖ = 1
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Concrete.blochKet, Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul,
      Complex.norm_real, Complex.norm_exp_ofReal_mul_I, one_mul, Real.norm_eq_abs, sq_abs]
    rw [Real.cos_sq_add_sin_sq, Real.sqrt_one]

/-- The underlying unit vector of `blochPureState θ φ` is `Concrete.blochKet θ φ` in
`EuclideanSpace`. A `simp` lemma exposing the vector for the density-operator computation. -/
@[simp]
theorem blochPureState_vec (θ φ : ℝ) :
    (blochPureState θ φ).vec = WithLp.toLp 2 (Concrete.blochKet θ φ) := rfl

/-- **`|ψ(θ,φ)⟩⟨ψ(θ,φ)| = Matrix.toEuclideanCLM (Concrete.blochMatrix (blochSphereVector θ φ))`
(Nielsen & Chuang, Exercise 2.72(4)).** The density operator of the §1.2 pure state
`blochPureState θ φ` is the operator of the Bloch state with the §1.2 Cartesian vector
`r⃗ = (sin θ cos φ, sin θ sin φ, cos θ)`.

Proof: the density operator is the rank-one projector `|ψ⟩⟨ψ| = InnerProductSpace.rankOne ℂ v v`
(`PureState.toState_op`) for `v = blochKet θ φ`. Under the `Matrix.toEuclideanCLM` isomorphism a
rank-one projector is `Matrix.toEuclideanCLM` of the outer product `Concrete.outerSelf v = vecMulVec
v (star v)` (via `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin` and
`InnerProductSpace.symm_toEuclideanLin_rankOne`), and `Concrete.outerSelf_blochKet_eq_blochMatrix`
identifies that outer product with `Concrete.blochMatrix (blochSphereVector θ φ)`. -/
theorem blochPureState_toState_op (θ φ : ℝ) :
    (blochPureState θ φ).toState.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
      (Concrete.blochMatrix (Concrete.blochSphereVector θ φ)) := by
  rw [PureState.toState_op, blochPureState_vec]
  change InnerProductSpace.rankOne ℂ (WithLp.toLp 2 (Concrete.blochKet θ φ))
        (WithLp.toLp 2 (Concrete.blochKet θ φ))
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Concrete.blochMatrix (Concrete.blochSphereVector θ φ))
  rw [← Concrete.outerSelf_blochKet_eq_blochMatrix, Concrete.outerSelf]
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ← InnerProductSpace.symm_toEuclideanLin_rankOne,
    LinearEquiv.apply_symm_apply]

end AxQM
