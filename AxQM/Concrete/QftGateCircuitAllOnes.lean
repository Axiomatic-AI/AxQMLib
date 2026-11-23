/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuitStatePerturbed
import AxQM.Concrete.QftCoherentError

/-!
# Concrete: the all-ones action of the ideal and perturbed Figure 5.1 QFT circuits

Toward the faithful `Ω(n²/p(n))` lower bound of Nielsen & Chuang, Exercise 5.6, this file
evaluates both the ideal QFT circuit `U = qftGateCircuit n` and the imperfect transform
`V = qftGateCircuitPerturbed n Δ` (each controlled-`Rₖ` shifted by `+Δ`) on the **all-ones
input** `|1…1⟩`, reading each output as a scaled coherent-phase product vector `phaseProdVec`
(`AxQM/Concrete/QftCoherentError.lean`). This is the specialisation that feeds the
coherent-accumulation distance bound `phaseProdVec_scaled_dist_ge`: the two outputs share the block
phase `φ = qftBlockPhase n 1` and differ only by the per-wire error `εₛ = (n-1-s)·Δ`, whose coherent
sum sets the distance.

## Why the all-ones input

The perturbation shifts each controlled-`Rₖ` gate's phase by `+Δ`. On a *product-state* input
every active control contributes one such shift, and the shifts add in a fixed sign — so to make
the errors accumulate coherently (rather than cancel) one takes the input on which **every** control
of every block is active. Under the little-endian encoding that is the all-ones string `|1…1⟩`
(`qftAllOnes`): wire `t`'s block then has all `n-1-t` of its higher controls active, so its `|1⟩`
amplitude picks up the extra phase `(n-1-t)·Δ` (`qftPhaseError`), and the total coherent phase is
`∑ₜ (n-1-t)·Δ = Δ·n(n-1)/2 = Θ(n²Δ)`.

## What is formalised

* `qftAllOnes n` — the all-ones bit string `|1…1⟩`; `qftPhaseError n Δ` — the per-wire error
  `εₛ = (n-1-s)·Δ`.
* `qftBitReversal_allOnes` — the swap layer fixes `|1…1⟩` (reversing an all-ones string is a
  no-op), so it drops out of the all-ones action of both circuits.
* `norm_qftBlockPhase` — the block phase `qftBlockPhase n a t` has unit modulus (a `±1` times a
  product of unit-modulus phases); the unit-phase hypothesis the coherent bound consumes.
* `qftBlockPhasePerturbed_allOnes` — on the all-ones input the perturbed block phase is the ideal
  one times the coherent phase:
  `qftBlockPhasePerturbed n 1 Δ t = qftBlockPhase n 1 t · e^{i(n-1-t)Δ}`.
* `qftGateCircuit_allOnes_mulVec`, `qftGateCircuitPerturbed_allOnes_mulVec` — **the headlines**: the
  ideal and perturbed circuit outputs on `|1…1⟩`,
  `U|1…1⟩ = (1/√2ⁿ)·phaseProdVec n φ` and `V|1…1⟩ = (1/√2ⁿ)·phaseProdVec n (φ·e^{iε})`,
  with `φ = qftBlockPhase n 1` and `εₛ = qftPhaseError n Δ s`. These are exactly the two vectors
  the coherent distance bound `phaseProdVec_scaled_dist_ge` separates; the boundary assembly reads
  the faithful `Ω` off them.

Both headlines route through the swap-first factorisation (`qftGateCircuit_eq_blocks_mul_perm` /
`qftGateCircuitPerturbed_eq_blocks_mul_perm`), the block-induction product state
(`qftBlocksProd_mulVec_basis` / `qftBlocksProdPerturbed_mulVec_basis`) and its `m = n` amplitude
form (`qftPartialState_full` / `qftPartialStatePerturbed_full`), with the swap collapsed by
`qftBitReversal_allOnes`.

* `qftPhaseError_sum` — the total coherent phase
  `∑ₛ qftPhaseError n Δ s = qftControlledRkCount n · Δ = n(n-1)/2·Δ`: the per-wire errors sum (a
  reflected Gauss sum) to the imprecise-gate count times the per-gate precision, so the `Ω` scaling
  is pinned to the *same* `Θ(n²)` count as the `O` half.
* `qftGateCircuitPerturbed_allOnes_dist_ge` — **the concrete `Ω` heart**: feeding the two all-ones
  outputs, the unit-phase bound `norm_qftBlockPhase`, and `qftPhaseError_sum` into the coherent
  distance bound `phaseProdVec_scaled_dist_ge` gives, in the regime
  `0 ≤ qftControlledRkCount n · Δ ≤ π`, the separation
  `‖U|1…1⟩ − V|1…1⟩‖ ≥ (qftControlledRkCount n · Δ)/π = n(n-1)Δ/(2π)`. This lifts
  (via `Evolution.gateError_apply_le` at the unit input `|1…1⟩`) to the faithful
  `E(U, V) ≥ n(n-1)Δ/(2π)`.

## Setting

Every statement is about complex matrices/vectors (`Matrix`, `Matrix.mulVec`, `Pi.single`),
the little-endian encoding `finFunctionFinEquiv`, the circuit objects of
`QftGateCircuit(Perturbed)`, and the phase-product vector `phaseProdVec`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The all-ones computational-basis input** `|1…1⟩` on `n` wires: every bit is `1`. The
worst-case input for the perturbed QFT, on which every controlled-`Rₖ` gate is active and the phase
errors accumulate coherently. -/
def qftAllOnes (n : ℕ) : Fin n → Fin 2 := Function.const (Fin n) 1

/-- **The coherent per-wire phase error of the all-ones perturbed QFT output**: wire `s` acquires
`(n-1-s)·Δ`, the sum of the `Δ`-shifts of the `n-1-s` controlled-`Rₖ` gates active in its block.
Its total `∑ₛ (n-1-s)·Δ = Δ·n(n-1)/2 = Θ(n²Δ)` is the coherent phase driving the `Ω` bound. -/
noncomputable def qftPhaseError (n : ℕ) (Δ : ℝ) : Fin n → ℝ :=
  fun s => ((n - 1 - (s : ℕ) : ℕ) : ℝ) * Δ

/-- **The wire-reversal fixes the all-ones input**: reversing an all-ones bit string leaves it
unchanged, so the Figure 5.1 swap layer acts trivially on `|1…1⟩` (`qftBitReversal_apply`). -/
theorem qftBitReversal_allOnes (n : ℕ) : qftBitReversal n (qftAllOnes n) = qftAllOnes n := by
  funext s
  simp [qftBitReversal_apply, qftAllOnes, Function.const_apply]

/-- **The block phase has unit modulus**: `‖qftBlockPhase n a t‖ = 1`. Writing it as a single
`Finset.univ` product (`qftBlockPhase_eq_prod`), every factor is either `1` or a phase
`e^{2πi·aₛ/2^{s-t+1}}` with purely imaginary exponent, hence unit-modulus
(`Complex.norm_exp_ofReal_mul_I`); the product of unit-modulus factors is unit-modulus. This is the
unit-phase hypothesis fed to `phaseProdVec_scaled_dist_ge`. -/
theorem norm_qftBlockPhase (n : ℕ) (a : Fin n → Fin 2) (t : Fin n) :
    ‖qftBlockPhase n a t‖ = 1 := by
  rw [qftBlockPhase_eq_prod, norm_prod]
  apply Finset.prod_eq_one
  intro s _
  by_cases h : (t : ℕ) ≤ (s : ℕ)
  · rw [ite_eq_left h,
      show (2 * Real.pi * Complex.I * ((a s : ℕ) : ℂ) / 2 ^ ((s : ℕ) - (t : ℕ) + 1))
          = ((2 * Real.pi * ((a s : ℕ) : ℝ) / 2 ^ ((s : ℕ) - (t : ℕ) + 1) : ℝ) : ℂ) * Complex.I
        from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  · rw [ite_eq_right h, norm_one]

/-- **The all-ones perturbed block phase is the ideal one times the coherent phase**
(Nielsen & Chuang, Exercise 5.6, `Ω` half). On `|1…1⟩` every control of block `t` is active, so
each of its `n-1-t` controlled-`Rₖ'` gates contributes its `+Δ` shift and

`qftBlockPhasePerturbed n 1 Δ t = qftBlockPhase n 1 t · e^{i·(n-1-t)Δ}`,

the ideal block phase multiplied by `e^{i·qftPhaseError n Δ t}`. The proof splits each active
cascade factor `e^{2πi/2^{c-t+1} + iΔ} = e^{2πi/2^{c-t+1}}·e^{iΔ}` (`Complex.exp_add`), collecting
the ideal product and the constant `e^{iΔ}` over the `n-1-t` controls (`length_qftTargetControls`),
the latter becoming `e^{i·(n-1-t)Δ}` (`Complex.exp_natCast_mul`). -/
theorem qftBlockPhasePerturbed_allOnes (n : ℕ) (Δ : ℝ) (t : Fin n) :
    qftBlockPhasePerturbed n (qftAllOnes n) Δ t
      = qftBlockPhase n (qftAllOnes n) t * Complex.exp (↑(qftPhaseError n Δ t) * Complex.I) := by
  have hsplit : ((qftTargetControls n t).map fun c =>
        if qftAllOnes n c = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
        else 1)
      = (qftTargetControls n t).map fun c =>
          (if qftAllOnes n c = 1
            then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1)
          * Complex.exp (↑Δ * Complex.I) := by
    apply List.map_congr_left
    intro c _
    have h : qftAllOnes n c = 1 := rfl
    rw [ite_eq_left h, ite_eq_left h, Complex.exp_add]
  have hconst : ((qftTargetControls n t).map fun _ => Complex.exp (↑Δ * Complex.I)).prod
      = Complex.exp (↑(qftPhaseError n Δ t) * Complex.I) := by
    rw [List.map_const', List.prod_replicate, length_qftTargetControls, ← Complex.exp_natCast_mul]
    simp only [qftPhaseError]
    congr 1
    push_cast
    ring
  rw [qftBlockPhasePerturbed, qftBlockPhase, hsplit, List.prod_map_mul, hconst]
  ring

/-- **The ideal QFT circuit on the all-ones input** (Nielsen & Chuang eqs. 5.5–5.10 at `|1…1⟩`):
`qftGateCircuit n *ᵥ |1…1⟩ = (1/√2ⁿ)·phaseProdVec n (qftBlockPhase n 1)`. The swap layer fixes the
input (`qftBitReversal_allOnes`), so the block sequence maps `|1…1⟩` to the product state
`qftPartialState n 1 n` (`qftBlocksProd_mulVec_basis`, `qftPartialState_full`), whose amplitudes are
exactly `(1/√2ⁿ)·∏ₛ (qftBlockPhase n 1 s)^{kₛ} = (1/√2ⁿ)·phaseProdVec n (qftBlockPhase n 1)`. -/
theorem qftGateCircuit_allOnes_mulVec (n : ℕ) :
    qftGateCircuit n *ᵥ Pi.single (finFunctionFinEquiv (qftAllOnes n)) 1
      = fun i => ((Real.sqrt 2)⁻¹ : ℂ) ^ n * phaseProdVec n (qftBlockPhase n (qftAllOnes n)) i := by
  rw [qftGateCircuit_eq_blocks_mul_perm, ← Matrix.mulVec_mulVec, permGate_mulVec_single,
    qftBitReversal_allOnes, qftBlocksProd_mulVec_basis]
  funext i
  rw [qftPartialState_full, ← Complex.ofReal_inv]
  simp only [phaseProdVec]

/-- **The perturbed QFT circuit on the all-ones input** (Nielsen & Chuang, Exercise 5.6, `Ω` half):
`qftGateCircuitPerturbed n Δ *ᵥ |1…1⟩ = (1/√2ⁿ)·phaseProdVec n (φ·e^{iε})`, with
`φ = qftBlockPhase n 1` and `εₛ = qftPhaseError n Δ s = (n-1-s)Δ`. Mirroring the ideal case through
the perturbed propagation (`qftBlocksProdPerturbed_mulVec_basis`, `qftPartialStatePerturbed_full`),
the swap again fixed by `qftBitReversal_allOnes`, then rewriting each wire's perturbed block phase
as `qftBlockPhase n 1 s · e^{i·εₛ}` (`qftBlockPhasePerturbed_allOnes`). Together with
`qftGateCircuit_allOnes_mulVec` these are the two product states the coherent-accumulation distance
bound `phaseProdVec_scaled_dist_ge` separates, giving the faithful `Ω(n²/p(n))`. -/
theorem qftGateCircuitPerturbed_allOnes_mulVec (n : ℕ) (Δ : ℝ) :
    qftGateCircuitPerturbed n Δ *ᵥ Pi.single (finFunctionFinEquiv (qftAllOnes n)) 1
      = fun i => ((Real.sqrt 2)⁻¹ : ℂ) ^ n
          * phaseProdVec n (fun s => qftBlockPhase n (qftAllOnes n) s
              * Complex.exp (↑(qftPhaseError n Δ s) * Complex.I)) i := by
  rw [qftGateCircuitPerturbed_eq_blocks_mul_perm, ← Matrix.mulVec_mulVec, permGate_mulVec_single,
    qftBitReversal_allOnes, qftBlocksProdPerturbed_mulVec_basis]
  funext i
  rw [qftPartialStatePerturbed_full, ← Complex.ofReal_inv]
  simp only [phaseProdVec]
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  rw [qftBlockPhasePerturbed_allOnes]

/-- **The total coherent phase error of the all-ones perturbed QFT equals the gate count times `Δ`**
(Nielsen & Chuang, Exercise 5.6, `Ω` half). The per-wire errors `qftPhaseError n Δ s = (n-1-s)·Δ`
sum, over the `n` wires, to

`∑ₛ qftPhaseError n Δ s = ∑ₛ (n-1-s)·Δ = (∑ₛ (n-1-s))·Δ = qftControlledRkCount n · Δ = n(n-1)/2·Δ`,

exactly the number of imprecise controlled-`Rₖ` gates (`qftControlledRkCount n`, the reflected Gauss
sum `∑_{s<n}(n-1-s) = ∑_{j<n} j`, `qftControlledRkCount_eq_sum`) times the per-gate precision. This
is the coherent phase `∑ₛ εₛ = Θ(n²Δ)` that `phaseProdVec_scaled_dist_ge` turns into the `Ω`
distance, tying the lower bound to the *same* `Θ(n²)` gate count as the `O` upper bound. -/
theorem qftPhaseError_sum (n : ℕ) (Δ : ℝ) :
    ∑ s : Fin n, qftPhaseError n Δ s = (qftControlledRkCount n : ℝ) * Δ := by
  have hnat : ∑ s : Fin n, (n - 1 - (s : ℕ)) = qftControlledRkCount n := by
    rw [qftControlledRkCount_eq_sum, Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n]
    exact Finset.sum_range_reflect (fun i => i) n
  simp only [qftPhaseError]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hnat]

/-- **The all-ones QFT-approximation distance lower bound** (Nielsen & Chuang, Exercise 5.6, `Ω`
half — the concrete heart). On the worst-case input `|1…1⟩`, the ideal QFT circuit
`U = qftGateCircuit n` and the imperfect transform `V = qftGateCircuitPerturbed n Δ`
(each controlled-`Rₖ` shifted by `+Δ`)
are separated by at least the coherent-accumulation bound

`‖U|1…1⟩ − V|1…1⟩‖ = √(∑ᵢ ‖…‖²) ≥ (qftControlledRkCount n · Δ)/π = n(n-1)Δ/(2π)`,

valid in the small-error regime `0 ≤ qftControlledRkCount n · Δ ≤ π` (`0 ≤ Δ`, `hreg`; the regime is
inherent — `E ≤ 2` always, so a `Θ(n²Δ)` scaling can only hold where `n²Δ` stays bounded). Both
circuit outputs on `|1…1⟩` are scaled coherent-phase product vectors sharing the block phase
`φ = qftBlockPhase n 1` (`qftGateCircuit_allOnes_mulVec`, `qftGateCircuitPerturbed_allOnes_mulVec`),
differing only by the per-wire phase `e^{iεₛ}` with `εₛ = qftPhaseError n Δ s`; `norm_qftBlockPhase`
supplies the unit-phase hypothesis and `qftPhaseError_sum` evaluates the coherent phase, so the
coherent-accumulation bound `phaseProdVec_scaled_dist_ge` applies directly. This is the concrete
`Ω(n²Δ)` that lifts (via `Evolution.gateError_apply_le` at the unit input `|1…1⟩`) to
`E(U, V) ≥ n(n-1)Δ/(2π)`, completing the `Θ` of Exercise 5.6. -/
theorem qftGateCircuitPerturbed_allOnes_dist_ge (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hreg : (qftControlledRkCount n : ℝ) * Δ ≤ Real.pi) :
    (qftControlledRkCount n : ℝ) * Δ / Real.pi
      ≤ Real.sqrt (∑ i, ‖(qftGateCircuit n *ᵥ Pi.single (finFunctionFinEquiv (qftAllOnes n)) 1) i
        - (qftGateCircuitPerturbed n Δ *ᵥ Pi.single (finFunctionFinEquiv (qftAllOnes n)) 1) i‖ ^ 2)
        := by
  have hε0 : 0 ≤ ∑ s, qftPhaseError n Δ s := by
    rw [qftPhaseError_sum]; exact mul_nonneg (Nat.cast_nonneg _) hΔ
  have hεπ : ∑ s, qftPhaseError n Δ s ≤ Real.pi := by rw [qftPhaseError_sum]; exact hreg
  have key := phaseProdVec_scaled_dist_ge n (qftBlockPhase n (qftAllOnes n)) (qftPhaseError n Δ)
    (norm_qftBlockPhase n (qftAllOnes n)) hε0 hεπ
  rw [qftPhaseError_sum] at key
  rw [qftGateCircuit_allOnes_mulVec, qftGateCircuitPerturbed_allOnes_mulVec]
  exact key

end AxQM.Concrete
