/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ApproxError
import AxQM.Postulates.API.NMRSwap
import ToMathlib.Analysis.InnerProductSpace.InvolutionRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# AxQM.Postulates.API — the gate-error chaining bound is order-tight

`AxQM/Postulates/API/ApproxError.lean` proves the **upper** half of Nielsen & Chuang's Box 4.1: gate
approximation errors add *at most* linearly along a circuit,
`E(∏ Uⱼ, ∏ Vⱼ) ≤ Σⱼ E(Uⱼ, Vⱼ) ≤ (#gates)·Δ` (eqs. 4.63/4.69, `Evolution.gateError_prod_le` /
`Evolution.gateError_prod_le_uniform`). This file supplies the matching **tightness** — that the
bound cannot be improved to `o((#gates)·Δ)` in general, because per-gate errors of size `≤ Δ` can
accumulate *coherently*.

The witness is a **global phase** `e^{iΔ}·I` (`globalPhaseGate`,
`AxQM/Postulates/API/NMRControlledZ.lean`),
the sharpest tool for this: N&C's error measure `E(U,V) = ‖U.op − V.op‖` is deliberately sensitive
to an overall phase (Box 4.1 notes a global phase on a *sub-circuit* becomes an observable relative
phase), and `E(U, e^{iΔ}U) = ‖1 − e^{iΔ}‖ = 2|sin(Δ/2)| ≤ Δ`, so a global phase is a legitimate
per-gate error of size `≤ Δ`. Composing `k` of them multiplies the phases: the accumulated error is
`E(U, e^{ikΔ}U) = ‖1 − e^{ikΔ}‖ = 2 sin(kΔ/2) ≥ (2/π)·kΔ` in the regime `kΔ ≤ π` (Jordan's
inequality, `Real.mul_le_sin`) — i.e. `Ω((#gates)·Δ)`, matching the `(#gates)·Δ` upper bound up to
the constant `2/π`.

## What this file provides

* `Evolution.norm_op_eq_one` — a unitary evolution's operator has norm **exactly** `1` on a system
  admitting a unit vector (it is an isometry; `norm_op_le_one` is the `≤` half).
* `globalPhaseGate_pow` — `(e^{iθ}·I)^k = e^{ikθ}·I`: iterating a global phase adds the angles.
* `Evolution.gateError_globalPhaseGate_comp` — `E(U, e^{iθ}U) = ‖1 − e^{iθ}‖·‖U.op‖`, the error a
  global phase introduces on a gate.
* `Evolution.exists_factorisation_gateError_ge` — **the tightness theorem.** For any gate `U` with
  `‖U.op‖ = 1` and any target length `k ≥ 1`, in the regime `kΔ ≤ π` there is a length-`k`
  factorisation `∏ Uⱼ = U` in which every gate is implemented to precision `Δ`
  (`E(Uⱼ, Vⱼ) ≤ Δ`) yet the whole-circuit error is `E(U, ∏ Vⱼ) ≥ (2/π)·k·Δ`. So the uniform
  chaining bound `(#gates)·Δ` is achieved up to the constant `2/π`: the linear accumulation is real.

## Scope — what this does and does not establish

This is the tightness of the **abstract** chaining bound over *arbitrary* factorisations: it is
agnostic to `U` (only `‖U.op‖ = 1` is used) and its witness pads with identity gates
(`(U, e^{iΔ}U) :: replicate (k−1) (1, e^{iΔ})`), so it shows the accumulation *mechanism* is
order-tight but says nothing about any *specific* circuit's elementary gates. It is therefore **not,
by itself, a faithful lower bound for a named circuit** whose approximation perturbs *its own*
elementary gates (e.g. the approximate QFT of Exercise 5.6, where `V` perturbs the controlled-`Rₖ`
rotations): that requires the circuit's genuine gate-level decomposition and a coherent perturbation
of the real gates.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A unitary evolution's operator has operator norm **exactly** `1`, provided the system admits a
unit vector `x` (`‖x‖ = 1`). The `≤` half is `Evolution.norm_op_le_one`; the `≥` half is
`1 = ‖U.op x‖ ≤ ‖U.op‖·‖x‖ = ‖U.op‖`, since a unitary is an isometry (`Evolution.norm_op_apply`).
Fails only on the trivial zero-dimensional system, which has no unit vector. -/
theorem Evolution.norm_op_eq_one (U : Evolution S) (x : S) (hx : ‖x‖ = 1) : ‖U.op‖ = 1 := by
  refine le_antisymm U.norm_op_le_one ?_
  calc (1 : ℝ) = ‖U.op x‖ := by rw [U.norm_op_apply, hx]
    _ ≤ ‖U.op‖ * ‖x‖ := U.op.le_opNorm x
    _ = ‖U.op‖ := by rw [hx, mul_one]

/-- Iterating a **global phase** adds its angle: `(e^{iθ}·I)^k = e^{ikθ}·I` as evolutions.
Follows by induction from `globalPhaseGate_comp_globalPhaseGate` (`e^{iα}·e^{iβ} = e^{i(α+β)}`),
with `globalPhaseGate_zero` for the base case. -/
theorem globalPhaseGate_pow (θ : ℝ) (k : ℕ) :
    (globalPhaseGate θ : Evolution S) ^ k = globalPhaseGate (k • θ) := by
  induction k with
  | zero => rw [pow_zero, zero_nsmul, globalPhaseGate_zero]; rfl
  | succ j ih =>
      rw [pow_succ, ih, Evolution.mul_def, globalPhaseGate_comp_globalPhaseGate, succ_nsmul]

/-- The error a **global phase** introduces on a gate (Nielsen & Chuang, Box 4.1 error measure):
`E(U, e^{iθ}U) = ‖1 − e^{iθ}‖·‖U.op‖`. Since `(e^{iθ}·I)∘U = e^{iθ}·U`, the difference is
`(1 − e^{iθ})·U.op`, whose norm factors as `‖1 − e^{iθ}‖·‖U.op‖`. -/
theorem Evolution.gateError_globalPhaseGate_comp (U : Evolution S) (θ : ℝ) :
    U.gateError ((globalPhaseGate θ).comp U)
      = ‖(1 : ℂ) - Complex.exp (↑θ * Complex.I)‖ * ‖U.op‖ := by
  have hop : ((globalPhaseGate θ).comp U).op = Complex.exp (↑θ * Complex.I) • U.op := by
    rw [Evolution.comp_op, globalPhaseGate_op]
    ext v
    simp
  rw [Evolution.gateError, hop,
    show U.op - Complex.exp (↑θ * Complex.I) • U.op
        = ((1 : ℂ) - Complex.exp (↑θ * Complex.I)) • U.op from by rw [sub_smul, one_smul],
    norm_smul]

/-- **The gate-error chaining bound is order-tight** (the `Ω` companion of Box 4.1's `O`). For any
gate `U` whose operator has norm `1` and any target circuit length `k ≥ 1`, in the small-error
regime `k·Δ ≤ π` there is a length-`k` factorisation `∏ⱼ Uⱼ = U` in which **every** gate is
implemented to precision `Δ` (`E(Uⱼ, Vⱼ) ≤ Δ`), yet the accumulated whole-circuit error obeys

`E(U, ∏ⱼ Vⱼ) ≥ (2/π)·k·Δ`.

The witness perturbs the circuit `[U, I, …, I]` (length `k`) by a common global phase `e^{iΔ}` on
each gate: each per-gate error is `‖1 − e^{iΔ}‖ ≤ Δ`, but the phases add, giving a total error
`‖1 − e^{ikΔ}‖ = 2 sin(kΔ/2) ≥ (2/π)·kΔ` (Jordan's inequality `Real.mul_le_sin`). So the uniform
chaining bound `(#gates)·Δ` (`Evolution.gateError_prod_le_uniform`) is achieved up to the constant
`2/π`: per-gate errors genuinely accumulate linearly. -/
theorem Evolution.exists_factorisation_gateError_ge
    (U : Evolution S) (hU : ‖U.op‖ = 1) (k : ℕ) (hk : 1 ≤ k) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hreg : (k : ℝ) * Δ ≤ Real.pi) :
    ∃ l : List (Evolution S × Evolution S),
      (l.map Prod.fst).prod = U ∧
      l.length = k ∧
      (∀ q ∈ l, q.1.gateError q.2 ≤ Δ) ∧
      2 / Real.pi * (k : ℝ) * Δ ≤ U.gateError (l.map Prod.snd).prod := by
  refine ⟨(U, (globalPhaseGate Δ).comp U) :: List.replicate (k - 1) ((1 : Evolution S),
    globalPhaseGate Δ), ?_, ?_, ?_, ?_⟩
  · -- the imperfect circuit factors the ideal gate: `U · Iᵏ⁻¹ = U`.
    have hmap : ((U, (globalPhaseGate Δ).comp U) :: List.replicate (k - 1)
          ((1 : Evolution S), globalPhaseGate Δ)).map Prod.fst
        = U :: List.replicate (k - 1) (1 : Evolution S) := by simp
    rw [hmap, List.prod_cons, List.prod_replicate, one_pow, mul_one]
  · -- length is `k`.
    rw [List.length_cons, List.length_replicate]
    omega
  · -- every gate is within `Δ`: each pair is `(V, e^{iΔ}·V)`, error `‖1 − e^{iΔ}‖ ≤ Δ`.
    intro q hq
    have hq2 : q.2 = (globalPhaseGate Δ).comp q.1 := by
      rcases List.mem_cons.mp hq with h | h
      · rw [h]
      · rw [List.eq_of_mem_replicate h]; simp
    rw [hq2, Evolution.gateError_globalPhaseGate_comp]
    calc ‖(1 : ℂ) - Complex.exp (↑Δ * Complex.I)‖ * ‖q.1.op‖
        ≤ ‖(1 : ℂ) - Complex.exp (↑Δ * Complex.I)‖ * 1 :=
          mul_le_mul_of_nonneg_left q.1.norm_op_le_one (norm_nonneg _)
      _ = ‖(1 : ℂ) - Complex.exp (↑Δ * Complex.I)‖ := mul_one _
      _ ≤ |Δ| := Complex.norm_one_sub_exp_ofReal_mul_I_le Δ
      _ = Δ := abs_of_nonneg hΔ
  · -- the phases accumulate: total error `‖1 − e^{ikΔ}‖ = 2 sin(kΔ/2) ≥ (2/π)·kΔ`.
    have hsnd : (((U, (globalPhaseGate Δ).comp U) :: List.replicate (k - 1)
          ((1 : Evolution S), globalPhaseGate Δ)).map Prod.snd).prod
        = (globalPhaseGate ((k : ℝ) * Δ)).comp U := by
      have hmap : ((U, (globalPhaseGate Δ).comp U) :: List.replicate (k - 1)
            ((1 : Evolution S), globalPhaseGate Δ)).map Prod.snd
          = ((globalPhaseGate Δ).comp U) :: List.replicate (k - 1) (globalPhaseGate Δ) := by simp
      rw [hmap, List.prod_cons, List.prod_replicate, globalPhaseGate_pow]
      have harith : Δ + (k - 1) • Δ = (k : ℝ) * Δ := by
        rw [nsmul_eq_mul, Nat.cast_sub hk, Nat.cast_one]; ring
      calc ((globalPhaseGate Δ).comp U) * globalPhaseGate ((k - 1) • Δ)
          = globalPhaseGate Δ * (U * globalPhaseGate ((k - 1) • Δ)) := by
            rw [← Evolution.mul_def, mul_assoc]
        _ = globalPhaseGate Δ * (globalPhaseGate ((k - 1) • Δ) * U) := by
            rw [Evolution.mul_def U, ← globalPhaseGate_comp_comm, ← Evolution.mul_def]
        _ = (globalPhaseGate Δ * globalPhaseGate ((k - 1) • Δ)) * U := by rw [mul_assoc]
        _ = globalPhaseGate (Δ + (k - 1) • Δ) * U := by
            rw [Evolution.mul_def (globalPhaseGate Δ), globalPhaseGate_comp_globalPhaseGate]
        _ = (globalPhaseGate ((k : ℝ) * Δ)).comp U := by rw [harith, Evolution.mul_def]
    rw [hsnd, Evolution.gateError_globalPhaseGate_comp, hU, mul_one]
    have hsin_nn : 0 ≤ Real.sin ((k : ℝ) * Δ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [hreg, Real.pi_pos])
    rw [norm_sub_rev, mul_comm (↑((k : ℝ) * Δ) : ℂ) Complex.I,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.sin ((k : ℝ) * Δ / 2))]
    have hjordan : 2 / Real.pi * ((k : ℝ) * Δ / 2) ≤ Real.sin ((k : ℝ) * Δ / 2) :=
      Real.mul_le_sin (by positivity) (by linarith [hreg])
    have heq : 2 / Real.pi * (k : ℝ) * Δ = 2 * (2 / Real.pi * ((k : ℝ) * Δ / 2)) := by ring
    rw [heq]
    linarith [hjordan]

end AxQM
