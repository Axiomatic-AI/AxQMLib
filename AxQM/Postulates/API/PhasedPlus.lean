/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.CnotXBasis

/-!
# AxQM.Postulates.API — the phased-plus qubit state `|+_θ⟩`

The single-qubit **phased-plus** (equatorial) state

  `|+_θ⟩ = (|0⟩ + e^{iθ}|1⟩)/√2`,

the equal-magnitude superposition of `|0⟩` and `|1⟩` with a relative phase `e^{iθ}` on `|1⟩`. It is
the state a phase-shift gate `P(θ)` produces from `|+⟩`, and it appears throughout interferometry
and phase estimation: after the controlled-power sequence of a phase-estimation circuit each control
wire carries such a state, its phase encoding the eigenvalue read out (the "phase gradient").

## What is formalised

* `qubitPhasePlus θ` — the state `|+_θ⟩`, defined as `P(θ)|+⟩`
  (`(phaseShiftGate θ).evolvePure qubitPlus`) so that its normalization is **inherited** from
  `qubitPlus` (a gate applied to a unit vector), with no separate `{ vec := …, normalized := … }`
  obligation. Its special cases are `qubitPlus` (`θ = 0`), `qubitMinus` (`θ = π`),
  `qubitPlusI` (`θ = π/2`).
* `qubitPhasePlus_vec` — the computational-basis expansion `|+_θ⟩ = (1/√2)(|0⟩ + e^{iθ}|1⟩)`, from
  `qubitPlus`'s expansion `(1/√2)(|0⟩ + |1⟩)` and the phase gate's diagonal action `P(θ)|0⟩ = |0⟩`,
  `P(θ)|1⟩ = e^{iθ}|1⟩`.
* `qubitPhasePlus_zero` — `|+_0⟩ = |+⟩`, the phase-free base case.

The state `qubitPhasePlus` is used, e.g., for the phase-gradient register `qtowerPhaseGrad` in
`AxQM/Core/QtowerPhaseGradient.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The phased-plus qubit state** `|+_θ⟩ = (|0⟩ + e^{iθ}|1⟩)/√2`: the equal-magnitude
superposition of `|0⟩` and `|1⟩` with relative phase `e^{iθ}` on `|1⟩`, defined as the image of
`|+⟩` under the phase-shift gate `P(θ)` (`(phaseShiftGate θ).evolvePure qubitPlus`).
Building it as `P(θ)|+⟩` (a gate applied to the unit vector `|+⟩`) makes normalization automatic —
no explicit norm proof. Generalises the fixed-phase states `qubitPlus` (`θ = 0`), `qubitMinus`
(`θ = π`) and `qubitPlusI` (`θ = π/2`). -/
def qubitPhasePlus (θ : ℝ) : PureState qubit := (phaseShiftGate θ).evolvePure qubitPlus

/-- **Computational-basis expansion of the phased-plus state:**
`|+_θ⟩ = (1/√2)(|0⟩ + e^{iθ}|1⟩)`. From `qubitPlus = (1/√2)(|0⟩ + |1⟩)` and the phase gate's
diagonal action `P(θ)|0⟩ = |0⟩`, `P(θ)|1⟩ = e^{iθ}|1⟩` (`phaseShiftGate_op_apply_qubitBasis`). -/
theorem qubitPhasePlus_vec (θ : ℝ) :
    (qubitPhasePlus θ).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec
          + Complex.exp ((θ : ℂ) * Complex.I) • (qubitBasis 1).vec) := by
  rw [qubitPhasePlus, Evolution.evolvePure_vec, qubitPlus_vec_eq_smul_add, map_smul, map_add,
    phaseShiftGate_op_apply_qubitBasis, phaseShiftGate_op_apply_qubitBasis]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [one_smul]

/-- **The phase-free phased-plus state is `|+⟩`:** `|+_0⟩ = |+⟩`, since `P(0) = 1` fixes `|+⟩`. -/
@[simp] theorem qubitPhasePlus_zero : qubitPhasePlus 0 = qubitPlus := by
  apply PureState.ext
  rw [qubitPhasePlus_vec, qubitPlus_vec_eq_smul_add]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  erw [one_smul]

/-- **Amplitude of the phased-plus state against the computational basis:**
`⟨c|+_ψ⟩ = (1/√2)·e^{iψc}` — the `c`-th coefficient of `|+_ψ⟩ = (1/√2)(|0⟩ + e^{iψ}|1⟩)`. Reads off
`⟨0|+_ψ⟩ = 1/√2` and `⟨1|+_ψ⟩ = (1/√2)e^{iψ}` from `qubitPhasePlus_vec` and the orthonormality of
`|0⟩, |1⟩` (`qubitBasis_inner_qubitBasis`). The single-wire amplitude behind the product
representation of a tower phase gradient (N&C Problem 5.1, eq. 5.4). -/
theorem qubitPhasePlus_inner_qubitBasis (ψ : ℝ) (c : Fin 2) :
    inner ℂ (qubitBasis c).vec (qubitPhasePlus ψ).vec
      = (Concrete.invSqrt2 : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I * (c : ℕ)) := by
  rw [qubitPhasePlus_vec, inner_smul_right, inner_add_right, inner_smul_right,
    qubitBasis_inner_qubitBasis, qubitBasis_inner_qubitBasis]
  fin_cases c <;> simp

/-- **The phased-plus state is `2π`-periodic in its phase:** `|+_{2πm + α}⟩ = |+_α⟩` for `m : ℕ`,
since `e^{i(2πm + α)} = e^{iα}` (`Complex.exp_nat_mul_two_pi_mul_I`). A general property of
`qubitPhasePlus`: two angles differing by an integer multiple of `2π` name the *same*
equatorial state. Used, e.g., to identify quantum-Fourier-transform output wires whose per-wire
phases agree only modulo `2π` (`qftTowerWirePhase_castSucc_qubitPhasePlus`, N&C Problem 5.2). -/
theorem qubitPhasePlus_two_pi_nat_add (m : ℕ) (α : ℝ) :
    qubitPhasePlus (2 * Real.pi * m + α) = qubitPhasePlus α := by
  apply PureState.ext
  rw [qubitPhasePlus_vec, qubitPhasePlus_vec,
    show ((2 * Real.pi * m + α : ℝ) : ℂ) * Complex.I
        = (m : ℂ) * (2 * Real.pi * Complex.I) + (α : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]

/-- **`|−⟩` is the phased-plus state at `θ = π`:** `qubitMinus = |+_π⟩`, since
`|+_π⟩ = (|0⟩ + e^{iπ}|1⟩)/√2 = (|0⟩ − |1⟩)/√2 = |−⟩` (`Complex.exp_pi_mul_I` gives `e^{iπ} = −1`).
Makes the "`qubitMinus` is the `θ = π` special case of `qubitPhasePlus`" claim formal, the companion
of `qubitPhasePlus_zero` (`|+_0⟩ = |+⟩`). -/
theorem qubitMinus_eq_qubitPhasePlus_pi : qubitMinus = qubitPhasePlus Real.pi := by
  apply PureState.ext
  rw [qubitPhasePlus_vec, qubitMinus_vec_eq_smul_add, Complex.exp_pi_mul_I]

/-- **The Hadamard sends a computational basis state to a phased-plus state:** `H|d⟩ = |+_{πd}⟩`.
`H|0⟩ = |+⟩ = |+_0⟩` (`hadamardGate_evolvePure_qubitBasis_zero`, `qubitPhasePlus_zero`) and
`H|1⟩ = |−⟩ = |+_π⟩` (`hadamardGate_evolvePure_qubitBasis_one`, `qubitMinus_eq_qubitPhasePlus_pi`),
uniformly `|+_{π·d}⟩`. The single-qubit state the quantum Fourier transform's head Hadamard produces
from a computational input before the head control wire's controlled-`Rₖ` phase cascade acts on it
(N&C §5.1 Figure 5.1 / Problem 5.2). -/
theorem hadamardGate_evolvePure_qubitBasis_qubitPhasePlus (d : Fin 2) :
    hadamardGate.evolvePure (qubitBasis d) = qubitPhasePlus (Real.pi * ((d : ℕ) : ℝ)) := by
  fin_cases d
  · simp only [Fin.mk_zero, Nat.cast_zero, mul_zero,
      hadamardGate_evolvePure_qubitBasis_zero, qubitPhasePlus_zero]
  · simp only [Fin.mk_one, Nat.cast_one, mul_one,
      hadamardGate_evolvePure_qubitBasis_one, qubitMinus_eq_qubitPhasePlus_pi]

end AxQM
