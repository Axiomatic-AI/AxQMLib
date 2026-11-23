/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concrete: the perturbed Figure 5.1 QFT gate circuit (each controlled-`Rₖ` shifted by `+Δ`)

Toward the faithful `Ω(n²/p(n))` lower bound of Nielsen & Chuang, Exercise 5.6 — the approximate
quantum Fourier transform — this file supplies the **imperfect transform `V`** the exercise
compares against the ideal QFT: the Figure 5.1 circuit in which *every* controlled-`Rₖ` phase
rotation is implemented not exactly but with its phase shifted by a common error `Δ`,

```
  Rₖ = diag(1, e^{2πi/2ᵏ})   ↦   Rₖ' = diag(1, e^{2πi/2ᵏ + iΔ})       (N&C: "to precision Δ")
```

Every other gate of the circuit — the Hadamards and the wire-reversing swaps — is parameter-free and
is left exact, exactly as in Exercise 5.6 (only the *controlled-`Rₖ`* gates carry a continuous phase
and so are the ones "performed to a precision `Δ = 1/p(n)`"). The perturbed circuit
`qftGateCircuitPerturbed n Δ` is therefore the ideal `qftGateCircuit n` with `qftRk` replaced by the
shifted `qftRkPerturbed` in each conditional rotation, the Hadamard/swap structure reused verbatim.

## What is formalised

* `qftRkPerturbed k Δ` — the shifted phase gate `Rₖ' = diag(1, e^{2πi/2ᵏ + iΔ})`, and
  `qftRkPerturbed_mem_unitaryGroup` — it is unitary (its lone off-`1` entry is again a unit-modulus
  phase); `qftRkPerturbed_eq_diagonal` — its diagonal form.
* **The per-gate precision** (Exercise 5.6's `Δ`): `norm_qftRkPerturbed_sub_qftRk` — the shifted
  gate differs from the ideal `Rₖ` by exactly `‖Rₖ'₁₁ − Rₖ₁₁‖ = 2|sin(Δ/2)|` in its rotation phase,
  and `norm_qftRkPerturbed_sub_qftRk_le` bounds this by `|Δ|`. So performing each `Rₖ` "to precision
  `Δ`" is realised here by the `+Δ` phase shift, whose gate error is `≤ Δ`. (The `2|sin(Δ/2)|` phase
  discrepancy is the operator distance to the ideal for this diagonal gate; it is read off from
  Mathlib's chord-length API — `Complex.norm_exp_ofReal_mul_I`,
  `Complex.norm_exp_I_mul_ofReal_sub_one`, `Real.norm_exp_I_mul_ofReal_sub_one_le` — after the
  `qftRkPerturbed_apply_sub_qftRk` factoring.)
* `qftControlledGatePerturbed`, `qftBlockControlledGatesPerturbed`, `qftBlockPerturbed`,
  `qftGateSequencePerturbed`, `qftGateCircuitPerturbed` — the perturbed conditional rotation, block
  cascade, block, full gate list, and circuit matrix, structurally mirroring
  `AxQM/Concrete/QftGateCircuit.lean` with `qftRk ↦ qftRkPerturbed`;
  `qftControlledGatePerturbed_eq_diagonal` — the perturbed rotation is again a diagonal phase gate
  (the hook the `Ω` state propagation consumes).
* `qftGateCircuitPerturbed_mem_unitaryGroup` — the perturbed circuit is still **unitary** (a genuine
  quantum transform `V`), since every factor — the exact Hadamards/swaps and the shifted rotations —
  is unitary.
* `qftControlledGatesPerturbed` + `length_qftControlledGatesPerturbed` — the perturbed circuit's
  controlled-`Rₖ'` gates still number exactly `qftControlledRkCount n = n(n-1)/2`: **the
  perturbation changes phases, not the gate count**, so the `Θ(n²)` imprecise-gate count of
  Exercise 5.6 is
  unaffected.

## Why this file exists (Exercise 5.6)

The `O(n²/p(n))` half of Exercise 5.6 (`AxQM/NC/Ch5/Exercise5_6.lean`) is universal over
factorisations and needs no specific `V`. The faithful `Ω(n²/p(n))` half is *existential*: it must
exhibit a concrete precision-`Δ` implementation whose error is `≥ c·n²·Δ`, and N&C fixes it as the
QFT with its **own controlled-`Rₖ` gates** perturbed. This file is that `V`. The next step of the
arc (`omega-propagation`) computes its action on the all-ones input `|1…1⟩` — a product state whose
wire phases each pick up the extra factor `e^{i(n-1-t)Δ}`, so that the accumulated phase errors add
coherently (the mechanism of `Concrete.QftCoherentError.lean`); this then yields
`E(qftEvolution, V) ≥ n(n-1)Δ/(2π)` and combines it with the `O` half for the full `Θ`.

## Setting

Every statement is about complex matrices (`Matrix`, `Matrix.unitaryGroup`, `Matrix.diagonal`),
the encoding equivalence `finFunctionFinEquiv`, the gate objects of
`AxQM/Concrete/QftGateCircuit.lean`, and real/complex analysis, alongside the ideal
`qftGateCircuit` it perturbs.
-/

namespace AxQM.Concrete

open Matrix

/-- **The `+Δ`-perturbed `Rₖ` phase gate** `Rₖ' = diag(1, e^{2πi/2ᵏ + iΔ})`: the ideal
`Rₖ = diag(1, e^{2πi/2ᵏ})` (N&C eq. 5.11) with its rotation phase shifted by the precision error
`Δ`. This is the imperfect conditional rotation of Exercise 5.6's approximate QFT. -/
noncomputable def qftRkPerturbed (k : ℕ) (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I)]

/-- **`Rₖ'` is unitary.** Its only off-`1` entry is the unit-modulus phase `e^{2πi/2ᵏ + iΔ}` (the
exponent `2πi/2ᵏ + iΔ` is purely imaginary, so `conj = −` and `conj(e^z)·e^z = e^{-z}·e^{z} = 1`),
so the shifted gate is unitary exactly as the ideal `qftRk` is. -/
theorem qftRkPerturbed_mem_unitaryGroup (k : ℕ) (Δ : ℝ) :
    qftRkPerturbed k Δ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hz : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 2 ^ k + ↑Δ * Complex.I)
      = -(2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I) := by
    simp only [map_add, map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal, map_pow]
    ring
  have hφ : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I))
      * Complex.exp (2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add, hz, neg_add_cancel, Complex.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qftRkPerturbed, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hφ]

/-- **`Rₖ'` in diagonal form**: `qftRkPerturbed k Δ = diagonal ![1, e^{2πi/2ᵏ + iΔ}]`. -/
theorem qftRkPerturbed_eq_diagonal (k : ℕ) (Δ : ℝ) :
    qftRkPerturbed k Δ
      = Matrix.diagonal ![1, Complex.exp (2 * Real.pi * Complex.I / 2 ^ k + ↑Δ * Complex.I)] := by
  rw [qftRkPerturbed, Matrix.diagonal_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-!
### The per-gate precision `Δ`

The shifted gate `Rₖ'` differs from the ideal `Rₖ` only in the rotation phase of its `|1⟩⟨1|`
entry, by the unit-modulus factor `e^{iΔ}`, so the per-gate discrepancy
`‖Rₖ'₁₁ − Rₖ₁₁‖ = ‖e^{iΔ} − 1‖ = 2|sin(Δ/2)| ≤ |Δ|` follows — after the
`qftRkPerturbed_apply_sub_qftRk` factoring below — directly from Mathlib's chord-length API
(`Complex.norm_exp_ofReal_mul_I` for the unit ideal phase, `Complex.norm_exp_I_mul_ofReal_sub_one`
for the equality, `Real.norm_exp_I_mul_ofReal_sub_one_le` for the bound), exhibiting the `+Δ` shift
as a precision-`Δ` implementation of each controlled rotation.
-/

/-- **The perturbed gate's rotation phase, minus the ideal's**, factors as `Rₖ'₁₁ − Rₖ₁₁ =
e^{2πi/2ᵏ}·(e^{iΔ} − 1)` — the ideal phase times the pure `+Δ` shift. -/
theorem qftRkPerturbed_apply_sub_qftRk (k : ℕ) (Δ : ℝ) :
    qftRkPerturbed k Δ 1 1 - qftRk k 1 1
      = Complex.exp (2 * Real.pi * Complex.I / 2 ^ k) * (Complex.exp (↑Δ * Complex.I) - 1) := by
  simp only [qftRkPerturbed, qftRk, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.cons_val_fin_one, Complex.exp_add]
  ring

/-- **The per-gate precision of Exercise 5.6** (exact form): performing the controlled rotation with
its phase shifted by `Δ` incurs the phase error `‖Rₖ'₁₁ − Rₖ₁₁‖ = 2|sin(Δ/2)|`. -/
theorem norm_qftRkPerturbed_sub_qftRk (k : ℕ) (Δ : ℝ) :
    ‖qftRkPerturbed k Δ 1 1 - qftRk k 1 1‖ = 2 * |Real.sin (Δ / 2)| := by
  have harg : (2 * Real.pi * Complex.I / 2 ^ k : ℂ) = ↑(2 * Real.pi / 2 ^ k) * Complex.I := by
    push_cast; ring
  have hunit : ‖Complex.exp (2 * Real.pi * Complex.I / 2 ^ k)‖ = 1 := by
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [qftRkPerturbed_apply_sub_qftRk, norm_mul, hunit, one_mul, mul_comm (↑Δ : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]

/-- **The per-gate precision of Exercise 5.6** (bound): the `+Δ` phase shift implements each
controlled `Rₖ` to precision `‖Rₖ'₁₁ − Rₖ₁₁‖ ≤ |Δ|`, so it is a legitimate precision-`Δ`
realisation of the QFT circuit. This is the `= ⇒ ≤` corollary of the exact per-gate error
`norm_qftRkPerturbed_sub_qftRk` (`= 2|sin(Δ/2)|`) via the chord bound `|sin y| ≤ |y|`
(`Real.abs_sin_le_abs`). -/
theorem norm_qftRkPerturbed_sub_qftRk_le (k : ℕ) (Δ : ℝ) :
    ‖qftRkPerturbed k Δ 1 1 - qftRk k 1 1‖ ≤ |Δ| := by
  rw [norm_qftRkPerturbed_sub_qftRk]
  have h : |Real.sin (Δ / 2)| ≤ |Δ / 2| := Real.abs_sin_le_abs
  rw [abs_div, abs_two] at h
  linarith

/-!
### The perturbed circuit

The gate framework is reused verbatim: only the conditional rotation changes (`qftRk ↦
qftRkPerturbed`), while the Hadamards (`qftHadamardGate`), the control-wire lists
(`qftTargetControls`), and the wire reversal (`qftBitReversal`) are the exact ones.
-/

/-- **The perturbed controlled-`Rₖ'` gate from control wire `c` onto target wire `t`**: apply the
shifted rotation `Rₖ' = qftRkPerturbed ((c−t)+1) Δ` to wire `t` when wire `c` is `1` (the ideal
`qftControlledGate` with `qftRk ↦ qftRkPerturbed`). -/
noncomputable def qftControlledGatePerturbed (n : ℕ) (Δ : ℝ) (t c : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  mcCtrlSingleQubit finFunctionFinEquiv {c} t (qftRkPerturbed ((c : ℕ) - (t : ℕ) + 1) Δ)

/-- **Each perturbed conditional rotation is a diagonal phase gate.** For `t ≠ c`, the
controlled-`Rₖ'` gate multiplies `|enc x⟩` by the shifted phase `e^{2πi/2^{c-t+1} + iΔ}` exactly
when both `x_c = 1` and `x_t = 1`, and by `1` otherwise — the perturbed counterpart of
`qftControlledGate_eq_diagonal`, the hook the `Ω` state propagation consumes. -/
theorem qftControlledGatePerturbed_eq_diagonal (n : ℕ) (Δ : ℝ) (t c : Fin n) (htc : t ≠ c) :
    qftControlledGatePerturbed n Δ t c = Matrix.diagonal fun i =>
      if finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
      then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
      else 1 := by
  rw [qftControlledGatePerturbed, qftRkPerturbed_eq_diagonal,
    mcCtrlSingleQubit_diagonal _ (by simpa using htc)]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  simp only [Finset.mem_singleton, forall_eq]
  by_cases hc : finFunctionFinEquiv.symm i c = 1
  · rw [ite_eq_left hc]
    generalize finFunctionFinEquiv.symm i t = v
    fin_cases v <;> simp [hc]
  · rw [ite_eq_right hc]
    simp [hc]

/-- **The perturbed cascade of target `t`'s block**: the perturbed controlled gates from each of
`t`'s control wires. -/
noncomputable def qftBlockControlledGatesPerturbed (n : ℕ) (Δ : ℝ) (t : Fin n) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  (qftTargetControls n t).map (qftControlledGatePerturbed n Δ t)

/-- **Target `t`'s perturbed Figure-5.1 block**: the exact Hadamard on wire `t`, followed by its
perturbed controlled-`Rₖ'` cascade. -/
noncomputable def qftBlockPerturbed (n : ℕ) (Δ : ℝ) (t : Fin n) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  qftHadamardGate n t :: qftBlockControlledGatesPerturbed n Δ t

/-- **The perturbed Figure 5.1 gate list**: the exact wire-reversal (swap) gate, then each target's
perturbed block in order `t = 0, …, n-1` (the exact `qftGateSequence` with `qftBlock ↦
qftBlockPerturbed`). -/
noncomputable def qftGateSequencePerturbed (n : ℕ) (Δ : ℝ) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  permGate finFunctionFinEquiv (qftBitReversal n)
    :: (List.finRange n).flatMap (qftBlockPerturbed n Δ)

/-- **The perturbed Figure 5.1 QFT circuit** as a `2ⁿ × 2ⁿ` matrix (the imperfect transform `V` of
Exercise 5.6): the reverse product of `qftGateSequencePerturbed`, so the first-listed gate acts
first. It is the ideal `qftGateCircuit n` with every controlled-`Rₖ` performed to precision `Δ`. -/
noncomputable def qftGateCircuitPerturbed (n : ℕ) (Δ : ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (qftGateSequencePerturbed n Δ).reverse.prod

/-- **Every gate of the perturbed Figure 5.1 QFT circuit is unitary**: the swap permutation
(`permGate_mem_unitaryGroup`), the exact Hadamards (`singleQubitOnWire_mem_unitaryGroup`,
`hadamardC_mem_unitaryGroup`), and the perturbed rotations (`mcCtrlSingleQubit_mem_unitaryGroup`,
`qftRkPerturbed_mem_unitaryGroup`) — perturbing the phases preserves unitarity. The perturbed twin
of `qftGateSequence_forall_mem_unitaryGroup`, and the reusable per-factor obligation behind the
circuit's unitarity (`qftGateCircuitPerturbed_mem_unitaryGroup`) and Exercise 5.6's chaining bound
(`qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le`). -/
theorem qftGateSequencePerturbed_forall_mem_unitaryGroup (n : ℕ) (Δ : ℝ) :
    ∀ g ∈ qftGateSequencePerturbed n Δ, g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  intro g hg
  rw [qftGateSequencePerturbed, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact permGate_mem_unitaryGroup _ _
  · rw [List.mem_flatMap] at hg
    obtain ⟨t, _, hgt⟩ := hg
    rw [qftBlockPerturbed, List.mem_cons] at hgt
    rcases hgt with rfl | hmap
    · exact singleQubitOnWire_mem_unitaryGroup _ _ hadamardC_mem_unitaryGroup
    · rw [qftBlockControlledGatesPerturbed, List.mem_map] at hmap
      obtain ⟨c, _, rfl⟩ := hmap
      exact mcCtrlSingleQubit_mem_unitaryGroup _ _ _ (qftRkPerturbed_mem_unitaryGroup _ _)

/-- **The perturbed QFT circuit is unitary** — a genuine quantum transform `V` (Nielsen & Chuang,
p. 219). The reverse product of the gate list `qftGateSequencePerturbed`, whose every factor is
unitary (`qftGateSequencePerturbed_forall_mem_unitaryGroup`), lies in the unitary group
(`Submonoid.list_prod_mem`). -/
theorem qftGateCircuitPerturbed_mem_unitaryGroup (n : ℕ) (Δ : ℝ) :
    qftGateCircuitPerturbed n Δ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  Submonoid.list_prod_mem _ fun g hg =>
    qftGateSequencePerturbed_forall_mem_unitaryGroup n Δ g (List.mem_reverse.mp hg)

/-- **The perturbed circuit's controlled-`Rₖ'` gates**: every block's perturbed cascade,
concatenated over the targets. These are the imprecise gates of Exercise 5.6's `V`. -/
noncomputable def qftControlledGatesPerturbed (n : ℕ) (Δ : ℝ) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  (List.finRange n).flatMap (qftBlockControlledGatesPerturbed n Δ)

/-- **The perturbation does not change the gate count**: the perturbed circuit has exactly
`qftControlledRkCount n = n(n-1)/2` controlled-`Rₖ'` gates, the same `Θ(n²)` count as the ideal
circuit (`length_qftControlledGates`). Only the phases are perturbed; each target `t` still
contributes its `n-1-t` controls. -/
theorem length_qftControlledGatesPerturbed (n : ℕ) (Δ : ℝ) :
    (qftControlledGatesPerturbed n Δ).length = qftControlledRkCount n := by
  rw [qftControlledGatesPerturbed, List.length_flatMap, qftControlledRkCount_eq_sum]
  simp only [qftBlockControlledGatesPerturbed, List.length_map, length_qftTargetControls]
  rw [← List.ofFn_eq_map, List.sum_ofFn, Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n,
    Finset.sum_range_reflect (fun i => i) n]

end AxQM.Concrete
