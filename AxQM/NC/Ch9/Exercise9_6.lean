/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochTraceDistance
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.BlochStateMix
import AxQM.Postulates.API.TraceDistance
import AxQM.Postulates.API.Mixture
import AxQM.NC.Ch2.Exercise2_72
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 9.6 (Trace distance between qubit density operators)

Compute trace distance between given qubit density operators.

The **trace distance** is `D(ρ, σ) ≡ ½ tr|ρ − σ|` (N&C `(9.11)`,
`AxQM.State.traceDistance`). For a qubit the states have Bloch representations
`ρ = ½(I + r⃗·σ)`, and N&C's own computation (eqs. 9.18–9.20, the paragraph following this
exercise) gives the geometric answer `D = ‖r⃗ − s⃗‖ / 2` — *half the Euclidean distance
between the Bloch vectors*. The two answers are

* part (a): `‖(0,0,½) − (0,0,⅓)‖ / 2 = (1/6)/2 = 1/12`;
* part (b): `‖(0,0,½) − (⅓,0,0)‖ / 2 = √(1/9 + 1/4)/2 = (√13/6)/2 = √13/12`.

## Formalisation

The main physics content is the Bloch trace-distance formula (N&C `(9.20)`), stated for the
states `blochState` and `State.traceDistance`:

* `blochState_traceDistance` — **N&C `(9.20)`**: for Bloch vectors `r⃗, s⃗` in the closed unit
  ball, `D(½(I + r⃗·σ), ½(I + s⃗·σ)) = ‖r⃗ − s⃗‖ / 2`. Proved from the trace-norm
  identity `‖t⃗·σ‖₁ = 2‖t⃗‖` (`Concrete.traceNorm_toEuclideanCLM_pauliDot`) via
  `ρ.op − σ.op = ½·((r⃗ − s⃗)·σ)` (`Concrete.blochMatrix_sub`).

The three density operators the exercise names are built *as the textbook mixtures* — convex
combinations of the pure-state projectors `|0⟩⟨0|`, `|1⟩⟨1|`, `|+⟩⟨+|`, `|−⟩⟨−|` via
`State.mix` — and then each is *proved equal* to its Bloch state, so no fidelity is lost to a
premature Bloch reparametrisation:

* `qubitMix34Zero`, `qubitMix23Zero`, `qubitMix23Plus` — the three states
  `¾|0⟩⟨0| + ¼|1⟩⟨1|`, `⅔|0⟩⟨0| + ⅓|1⟩⟨1|`, `⅔|+⟩⟨+| + ⅓|−⟩⟨−|`.
* `qubitMix34Zero_eq_blochState`, `qubitMix23Zero_eq_blochState`, `qubitMix23Plus_eq_blochState`
  — each mixture equals `blochState (0,0,½)`, `blochState (0,0,⅓)`, `blochState (⅓,0,0)`
  respectively. Each basis projector `|ψ⟩⟨ψ|` is the Bloch state of its point on the sphere
  (`blochPureState_toState_eq_blochState`, N&C Ex 2.72(4)), and the shared state-level lemma
  `AxQM.blochState_mix` (a two-point mixture of Bloch states is the Bloch state of the
  averaged Bloch vector) then averages the two poles/equator points to the target vector.
* `traceDistance_qubitMix_zBasis` — **part (a)**: `D(ρ, σ) = 1/12`.
* `traceDistance_qubitMix_xBasis` — **part (b)**: `D(ρ, σ') = √13/12`.

The trace-norm identity `‖t⃗·σ‖₁ = 2‖t⃗‖` is in `AxQM/Concrete/BlochTraceDistance.lean`.
-/

open Matrix ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang `(9.20)`: the qubit trace distance is half the Euclidean Bloch
distance.** For Bloch vectors `r⃗, s⃗` in the closed unit ball, the trace distance between the
qubit states `ρ = ½(I + r⃗·σ)` and `σ = ½(I + s⃗·σ)` is `D(ρ, σ) = ‖r⃗ − s⃗‖ / 2`. The difference
of density operators is `½·((r⃗ − s⃗)·σ)` (`Concrete.blochMatrix_sub`), whose trace norm is
`‖r⃗ − s⃗‖` (`Concrete.traceNorm_toEuclideanCLM_pauliDot`), so `D = ‖r⃗ − s⃗‖/2`. -/
theorem blochState_traceDistance (r s : Fin 3 → ℝ)
    (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 ≤ 1) :
    (blochState r hr).traceDistance (blochState s hs)
      = Real.sqrt ((r 0 - s 0) ^ 2 + (r 1 - s 1) ^ 2 + (r 2 - s 2) ^ 2) / 2 := by
  have hop : (blochState r hr).op - (blochState s hs).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot ((2⁻¹ : ℝ) • (r - s))) := by
    rw [blochState_op, blochState_op, ← Concrete.blochMatrix_sub]
    exact (map_sub _ (Concrete.blochMatrix r) (Concrete.blochMatrix s)).symm
  rw [State.traceDistance_eq, hop]
  erw [Concrete.traceNorm_toEuclideanCLM_pauliDot]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [show (2⁻¹ * (r 0 - s 0)) ^ 2 + (2⁻¹ * (r 1 - s 1)) ^ 2 + (2⁻¹ * (r 2 - s 2)) ^ 2
        = 2⁻¹ ^ 2 * ((r 0 - s 0) ^ 2 + (r 1 - s 1) ^ 2 + (r 2 - s 2) ^ 2) from by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  ring

/-- The textbook state `ρ = ¾|0⟩⟨0| + ¼|1⟩⟨1|`, as a mixture of the computational basis
projectors. -/
def qubitMix34Zero : State qubit :=
  State.mix ![3/4, 1/4] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) ![qubitKet0.toState, (qubitBasis 1).toState]

/-- The textbook state `σ = ⅔|0⟩⟨0| + ⅓|1⟩⟨1|`, as a mixture of the computational basis
projectors. -/
def qubitMix23Zero : State qubit :=
  State.mix ![2/3, 1/3] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) ![qubitKet0.toState, (qubitBasis 1).toState]

/-- The textbook state `σ' = ⅔|+⟩⟨+| + ⅓|−⟩⟨−|`, as a mixture of the Hadamard basis
projectors. -/
def qubitMix23Plus : State qubit :=
  State.mix ![2/3, 1/3] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) ![qubitPlus.toState, qubitMinus.toState]

/-- `ρ = ¾|0⟩⟨0| + ¼|1⟩⟨1|` is the Bloch state with `r⃗ = (0,0,½)`: `|0⟩⟨0|` and `|1⟩⟨1|` sit at
the poles `(0,0,±1)`, and the `(¾,¼)` mixture averages them to `(0,0,½)`. -/
theorem qubitMix34Zero_eq_blochState :
    qubitMix34Zero = blochState ![0, 0, 1/2]
      (by norm_num [(show (![0,0,1/2] : Fin 3 → ℝ) 0 = 0 from rfl),
        (show (![0,0,1/2] : Fin 3 → ℝ) 1 = 0 from rfl),
        (show (![0,0,1/2] : Fin 3 → ℝ) 2 = 1/2 from rfl)]) := by
  unfold qubitMix34Zero
  rw [qubitKet0_eq_blochPureState, qubitBasis_one_eq_blochPureState,
    blochPureState_toState_eq_blochState, blochPureState_toState_eq_blochState,
    blochState_mix _ _ _ _ _ _
      (by simp [Concrete.blochSphereVector_zero_zero, Concrete.blochSphereVector_pi_zero,
            Pi.add_apply]; norm_num)]
  congr 1
  funext i
  fin_cases i <;>
    norm_num [Concrete.blochSphereVector_zero_zero, Concrete.blochSphereVector_pi_zero,
      Pi.add_apply, Pi.smul_apply]

/-- `σ = ⅔|0⟩⟨0| + ⅓|1⟩⟨1|` is the Bloch state with `r⃗ = (0,0,⅓)`. -/
theorem qubitMix23Zero_eq_blochState :
    qubitMix23Zero = blochState ![0, 0, 1/3]
      (by norm_num [(show (![0,0,1/3] : Fin 3 → ℝ) 0 = 0 from rfl),
        (show (![0,0,1/3] : Fin 3 → ℝ) 1 = 0 from rfl),
        (show (![0,0,1/3] : Fin 3 → ℝ) 2 = 1/3 from rfl)]) := by
  unfold qubitMix23Zero
  rw [qubitKet0_eq_blochPureState, qubitBasis_one_eq_blochPureState,
    blochPureState_toState_eq_blochState, blochPureState_toState_eq_blochState,
    blochState_mix _ _ _ _ _ _
      (by simp [Concrete.blochSphereVector_zero_zero, Concrete.blochSphereVector_pi_zero,
            Pi.add_apply]; norm_num)]
  congr 1
  funext i
  fin_cases i <;>
    norm_num [Concrete.blochSphereVector_zero_zero, Concrete.blochSphereVector_pi_zero,
      Pi.add_apply, Pi.smul_apply]

/-- `σ' = ⅔|+⟩⟨+| + ⅓|−⟩⟨−|` is the Bloch state with `r⃗ = (⅓,0,0)`: `|+⟩⟨+|` and `|−⟩⟨−|` sit at
`(±1,0,0)`, and the `(⅔,⅓)` mixture averages them to `(⅓,0,0)`. -/
theorem qubitMix23Plus_eq_blochState :
    qubitMix23Plus = blochState ![1/3, 0, 0]
      (by norm_num [(show (![1/3,0,0] : Fin 3 → ℝ) 0 = 1/3 from rfl),
        (show (![1/3,0,0] : Fin 3 → ℝ) 1 = 0 from rfl),
        (show (![1/3,0,0] : Fin 3 → ℝ) 2 = 0 from rfl)]) := by
  unfold qubitMix23Plus
  rw [qubitPlus_eq_blochPureState, qubitMinus_eq_blochPureState,
    blochPureState_toState_eq_blochState, blochPureState_toState_eq_blochState,
    blochState_mix _ _ _ _ _ _
      (by simp [Concrete.blochSphereVector_pi_div_two_zero,
            Concrete.blochSphereVector_pi_div_two_pi, Pi.add_apply]; norm_num)]
  congr 1
  funext i
  fin_cases i <;>
    norm_num [Concrete.blochSphereVector_pi_div_two_zero,
      Concrete.blochSphereVector_pi_div_two_pi, Pi.add_apply, Pi.smul_apply]

/-- **Exercise 9.6, part (a).** The trace distance between `ρ = ¾|0⟩⟨0| + ¼|1⟩⟨1|` and
`σ = ⅔|0⟩⟨0| + ⅓|1⟩⟨1|` is `1/12` — the Bloch vectors `(0,0,½)` and `(0,0,⅓)` are `1/6` apart. -/
theorem traceDistance_qubitMix_zBasis :
    qubitMix34Zero.traceDistance qubitMix23Zero = 1 / 12 := by
  rw [qubitMix34Zero_eq_blochState, qubitMix23Zero_eq_blochState, blochState_traceDistance,
    show ((![0,0,1/2] : Fin 3 → ℝ) 0 - (![0,0,1/3] : Fin 3 → ℝ) 0) ^ 2
        + ((![0,0,1/2] : Fin 3 → ℝ) 1 - (![0,0,1/3] : Fin 3 → ℝ) 1) ^ 2
        + ((![0,0,1/2] : Fin 3 → ℝ) 2 - (![0,0,1/3] : Fin 3 → ℝ) 2) ^ 2 = (1/6) ^ 2 from by
      norm_num [(show (![0,0,1/2] : Fin 3 → ℝ) 0 = 0 from rfl),
        (show (![0,0,1/2] : Fin 3 → ℝ) 1 = 0 from rfl),
        (show (![0,0,1/2] : Fin 3 → ℝ) 2 = 1/2 from rfl),
        (show (![0,0,1/3] : Fin 3 → ℝ) 0 = 0 from rfl),
        (show (![0,0,1/3] : Fin 3 → ℝ) 1 = 0 from rfl),
        (show (![0,0,1/3] : Fin 3 → ℝ) 2 = 1/3 from rfl)],
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Exercise 9.6, part (b).** The trace distance between `ρ = ¾|0⟩⟨0| + ¼|1⟩⟨1|` and
`σ' = ⅔|+⟩⟨+| + ⅓|−⟩⟨−|` is `√13/12` — the Bloch vectors `(0,0,½)` and `(⅓,0,0)` are
`√13/6` apart. -/
theorem traceDistance_qubitMix_xBasis :
    qubitMix34Zero.traceDistance qubitMix23Plus = Real.sqrt 13 / 12 := by
  rw [qubitMix34Zero_eq_blochState, qubitMix23Plus_eq_blochState, blochState_traceDistance,
    show ((![0,0,1/2] : Fin 3 → ℝ) 0 - (![1/3,0,0] : Fin 3 → ℝ) 0) ^ 2
        + ((![0,0,1/2] : Fin 3 → ℝ) 1 - (![1/3,0,0] : Fin 3 → ℝ) 1) ^ 2
        + ((![0,0,1/2] : Fin 3 → ℝ) 2 - (![1/3,0,0] : Fin 3 → ℝ) 2) ^ 2 = 13 * (6⁻¹ : ℝ) ^ 2 from by
      norm_num [(show (![0,0,1/2] : Fin 3 → ℝ) 0 = 0 from rfl),
        (show (![0,0,1/2] : Fin 3 → ℝ) 1 = 0 from rfl),
        (show (![0,0,1/2] : Fin 3 → ℝ) 2 = 1/2 from rfl),
        (show (![1/3,0,0] : Fin 3 → ℝ) 0 = 1/3 from rfl),
        (show (![1/3,0,0] : Fin 3 → ℝ) 1 = 0 from rfl),
        (show (![1/3,0,0] : Fin 3 → ℝ) 2 = 0 from rfl)],
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  ring

end AxQM
