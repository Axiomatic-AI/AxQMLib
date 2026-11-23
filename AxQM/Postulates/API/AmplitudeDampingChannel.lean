/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingKrausMatrix
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.QuantumChannel
import ToMathlib.Analysis.InnerProductSpace.OperatorSumMatrix

/-!
# AxQM.Postulates.API — the grounded amplitude-damping qubit channel

The **single-qubit amplitude-damping channel** `E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (Nielsen & Chuang
eq. 10.46, §8.3.5) with operation elements `E₀ = diag(1, √(1-γ))` and `E₁ = √γ |0⟩⟨1|`, packaged as
a genuine `State qubit → State qubit` map. This is the *grounded* channel needed to state the
minimum-fidelity result of Nielsen & Chuang Exercise 10.13 (`AxQM/NC/Ch10/Exercise10_13`),
whose fidelities are `State.fidelity`.

* `AxQM.amplitudeDampingKraus` — the operation elements as a `Fin 2`-indexed family of
  operators `qubit.space →L[ℂ] qubit.space`, the `Matrix.toEuclideanCLM` images of the concrete
  Kraus matrices `Concrete.amplitudeDampingKrausMatrix`. `amplitudeDampingKraus_completeness` gives
  `∑ₖ Eₖ† Eₖ = I` (trace preservation), transported from the matrix completeness
  `Concrete.amplitudeDampingKrausMatrix_completeness`.
* `AxQM.amplitudeDampingChannel` — the induced state map `ρ ↦ ∑ₖ Eₖ ρ Eₖ†`, a genuine
  `State qubit → State qubit` (the operator sum of a completeness-satisfying Kraus family sends
  density operators to density operators, `isDensityOp_krausSumₗ`), with
  `amplitudeDampingChannel_isChannel` (it is CPTP, `IsChannel`).
* `AxQM.amplitudeDampingChannel_apply_blochState` — its **Bloch action**: it sends the
  Bloch state `ρ = ½(I + r·σ)` to the Bloch state of the *affine* transform
  `Concrete.ampDampBlochVec γ r = (√(1-γ) r₀, √(1-γ) r₁, (1-γ) r₂ + γ)`, transported from the
  concrete `Concrete.amplitudeDampingKrausMatrix_conj_blochMatrix` through the general matrix Kraus
  bridge `ContinuousLinearMap.krausSumₗ_toEuclideanCLM`. Unlike the isotropic depolarizing shrink
  (Ex 10.12), the `+γ` longitudinal offset makes this map affine — amplitude damping is not unital.

-/

open Matrix ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The operation elements of the amplitude-damping qubit channel** (Nielsen & Chuang eq. 10.46):
the `Fin 2`-indexed family `![E₀, E₁]` of operators `qubit.space →L[ℂ] qubit.space`, obtained by
promoting the concrete Kraus matrices `Concrete.amplitudeDampingKrausMatrix γ` (`E₀ = diag(1,
√(1-γ))`, `E₁ = √γ |0⟩⟨1|`) through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`. -/
def amplitudeDampingKraus (γ : ℝ) (a : Fin 2) : qubit.space →L[ℂ] qubit.space :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.amplitudeDampingKrausMatrix γ a)

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the amplitude-damping operation elements
(`0 ≤ γ ≤ 1`), certifying trace preservation. Each summand `Eₖ† Eₖ = toEuclideanCLM (Eₖᴴ Eₖ)`
(via `Matrix.toEuclideanCLM_conjTranspose_eq_adjoint` and `map_mul`); the sum is
`toEuclideanCLM (∑ₖ Eₖᴴ Eₖ) = toEuclideanCLM I = I` by the matrix completeness
`Concrete.amplitudeDampingKrausMatrix_completeness`. -/
theorem amplitudeDampingKraus_completeness (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ∑ i, (adjoint (amplitudeDampingKraus γ i)).comp (amplitudeDampingKraus γ i) = 1 := by
  have hkey : ∑ i, (adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
      (Concrete.amplitudeDampingKrausMatrix γ i))).comp
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Concrete.amplitudeDampingKrausMatrix γ i)) = 1 := by
    calc ∑ i, (adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
        (Concrete.amplitudeDampingKrausMatrix γ i))).comp
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
            (Concrete.amplitudeDampingKrausMatrix γ i))
        = ∑ i, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
            ((Concrete.amplitudeDampingKrausMatrix γ i)ᴴ
              * Concrete.amplitudeDampingKrausMatrix γ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hadj : adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
              (Concrete.amplitudeDampingKrausMatrix γ i))
              = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
                  ((Concrete.amplitudeDampingKrausMatrix γ i)ᴴ) :=
            (Matrix.toEuclideanCLM_conjTranspose_eq_adjoint _).symm
          rw [hadj, ← ContinuousLinearMap.mul_def]
          exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) _ _).symm
      _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
            (∑ i, (Concrete.amplitudeDampingKrausMatrix γ i)ᴴ
              * Concrete.amplitudeDampingKrausMatrix γ i) :=
          (map_sum (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) _ _).symm
      _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) 1 := by
          rw [Concrete.amplitudeDampingKrausMatrix_completeness γ h0 h1]
      _ = 1 := map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
  exact hkey

/-- **The single-qubit amplitude-damping channel** `E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (Nielsen & Chuang
eq. 10.46) as a state map, for damping parameter `0 ≤ γ ≤ 1`: the operator sum of the operation
elements `amplitudeDampingKraus`. It is a genuine `State qubit → State qubit` — the operator sum of
a completeness-satisfying Kraus family sends density operators to density operators
(`isDensityOp_krausSumₗ` with `amplitudeDampingKraus_completeness`). -/
def amplitudeDampingChannel (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ρ : State qubit) : State qubit where
  op := krausSumₗ (amplitudeDampingKraus γ) ρ.op
  isDensity :=
    isDensityOp_krausSumₗ (amplitudeDampingKraus γ) (amplitudeDampingKraus_completeness γ h0 h1)
      ρ.isDensity

/-- The operator of the amplitude-damping channel is the Kraus sum `∑ₖ Eₖ ρ Eₖ†`. -/
@[simp]
theorem amplitudeDampingChannel_op (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ρ : State qubit) :
    (amplitudeDampingChannel γ h0 h1 ρ).op = krausSumₗ (amplitudeDampingKraus γ) ρ.op := rfl

/-- **The amplitude-damping channel is a genuine CPTP quantum channel** (`IsChannel`): the operator
sum of the completeness-satisfying operation elements `amplitudeDampingKraus`
(`isChannel_of_kraus`). -/
theorem amplitudeDampingChannel_isChannel (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsChannel (amplitudeDampingChannel γ h0 h1) :=
  isChannel_of_kraus (amplitudeDampingKraus γ) (amplitudeDampingKraus_completeness γ h0 h1)
    fun _ => rfl

/-- **The affine Bloch transform stays in the closed unit ball**, for `0 ≤ γ ≤ 1`:
`‖(√(1-γ) r₀, √(1-γ) r₁, (1-γ) r₂ + γ)‖² ≤ 1` whenever `‖r‖² ≤ 1`. The excess over `1` is
`-γ(1-γ)(r₂ - 1)² ≤ 0`. -/
private theorem ampDampBlochVec_sq_le (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) {r : Fin 3 → ℝ}
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    (Concrete.ampDampBlochVec γ r) 0 ^ 2 + (Concrete.ampDampBlochVec γ r) 1 ^ 2
        + (Concrete.ampDampBlochVec γ r) 2 ^ 2 ≤ 1 := by
  have hs : Real.sqrt (1 - γ) ^ 2 = 1 - γ := Real.sq_sqrt (by linarith)
  simp only [Concrete.ampDampBlochVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, mul_pow, hs]
  nlinarith [h, mul_nonneg (mul_nonneg h0 (show (0:ℝ) ≤ 1 - γ by linarith)) (sq_nonneg (r 2 - 1)),
    sq_nonneg (r 0), sq_nonneg (r 1)]

/-- **The Bloch action of the amplitude-damping channel.** For a Bloch state `ρ = ½(I + r·σ)` and
`0 ≤ γ ≤ 1`, `E(ρ)` is the Bloch state of the affine transform
`Concrete.ampDampBlochVec γ r = (√(1-γ) r₀, √(1-γ) r₁, (1-γ) r₂ + γ)`:
`amplitudeDampingChannel γ (blochState r) = blochState (ampDampBlochVec γ r)`.

Proof: the channel's operator is the Kraus sum on `(blochState r).op = toEuclideanCLM (blochMatrix
r)` (`amplitudeDampingChannel_op`, `blochState_op`), which by the general matrix Kraus bridge
`krausSumₗ_toEuclideanCLM` is `toEuclideanCLM (∑ₖ Eₖ (blochMatrix r) Eₖᴴ)`; that matrix sum is
`blochMatrix (ampDampBlochVec γ r)` (`Concrete.amplitudeDampingKrausMatrix_conj_blochMatrix`), i.e.
`(blochState (ampDampBlochVec γ r)).op` (`blochState_op`). The transverse components shrink by
`√(1-γ)`; the longitudinal one contracts toward the ground state `+1` — the (non-unital)
amplitude-damping map on the Bloch ball. -/
theorem amplitudeDampingChannel_apply_blochState (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (r : Fin 3 → ℝ)
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    amplitudeDampingChannel γ h0 h1 (blochState r h)
      = blochState (Concrete.ampDampBlochVec γ r) (ampDampBlochVec_sq_le γ h0 h1 h) := by
  apply State.ext
  simp only [amplitudeDampingChannel_op, blochState_op]
  change (krausSumₗ fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
      (Concrete.amplitudeDampingKrausMatrix γ a))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix r)) = _
  rw [krausSumₗ_toEuclideanCLM, Concrete.amplitudeDampingKrausMatrix_conj_blochMatrix γ h0 h1]

end AxQM
