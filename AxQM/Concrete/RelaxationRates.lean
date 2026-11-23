/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingDensityMatrix
import AxQM.Concrete.PhaseDampingCircuit
import ToMathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Concrete: T₁/T₂ relaxation rates of amplitude and phase damping (N&C Exercise 8.30)

This file works with operators on an
arbitrary two-dimensional complex inner product space (a qubit) with a chosen computational
orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`, it formalises Nielsen & Chuang, *Quantum
Computation and Quantum Information*, **Exercise 8.30** ("`T₂ ≤ T₁/2`", p. 386).

## The exercise, and a note on the printed inequality

In the relaxation model of N&C eq. (7.144), a single-qubit density matrix `!![a, b; b*, 1-a]`
relaxes with its **diagonal** (population) offset decaying as `e^{-t/T₁}` and its **off-diagonal**
(coherence) as `e^{-t/T₂}`. The exercise names `T₁` the "longitudinal" decay *rate* of the diagonal
and `T₂` the "transverse" decay *rate* of the off-diagonal, and asks to show `T₂ = T₁/2` for
amplitude damping, and `T₂ ≤ T₁/2` when amplitude and phase damping are both applied.

Reading `T₁`, `T₂` as N&C's own words demand — *rates* (`decayRate f = -log f`, so a factor
`f = e^{-Γ}` per unit step has rate `Γ`) — the two damping channels, applied to a general qubit
operator `ρ` (`AmplitudeDampingDensityMatrix.lean` / this file), multiply the matrix entries by:

| channel | population factor `⟨1|E(ρ)|1⟩ / ⟨1|ρ|1⟩` | coherence factor `⟨0|E(ρ)|1⟩ / ⟨0|ρ|1⟩` |
| --- | --- | --- |
| amplitude damping `γ` | `1 - γ` | `√(1-γ)` |
| phase damping `λ`     | `1` (populations preserved) | `√(1-λ)` |
| both (phase ∘ amplitude) | `1 - γ` | `√(1-γ)·√(1-λ)` |

Hence the **longitudinal rate** is `Γ₁ = -log(1-γ)`, and the **transverse rate** of the combined
channel is `Γ₂ = -log(√(1-γ)·√(1-λ)) = Γ₁/2 + (-log√(1-λ))`. Writing the **pure-dephasing rate**
`Γ_φ = -log√(1-λ) ≥ 0`, the whole exercise collapses to a single, exact, well-known identity

`Γ₂ = Γ₁/2 + Γ_φ`   (`transverseRate_eq`),

the additive-rate form of the standard textbook relation. Its two specialisations are the two parts
of the exercise:

* pure amplitude damping (`λ = 0`, so `Γ_φ = 0`): `Γ₂ = Γ₁/2` (`transverseRate_amplitudeDamping`) —
  N&C's first claim `T₂ = T₁/2` verbatim (as rates);
* adding phase damping (`Γ_φ ≥ 0`): `Γ₂ ≥ Γ₁/2` (`transverseRate_ge_half_longitudinal`), strictly
  `Γ₂ > Γ₁/2` once `0 < λ` (`transverseRate_gt_half_longitudinal`).

**The printed second relation `T₂ ≤ T₁/2` has a reversed inequality.** Adding phase damping makes
the coherence decay *faster*, so its transverse *rate* can only *increase*: `Γ₂ ≥ Γ₁/2`, not `≤`.
Equivalently, in the relaxation-*time* convention of eq. (7.144) — where `T = 1/Γ`, so a faster rate
is a *shorter* time — the correct statement reads `T₂ ≤ 2 T₁` (with equality `T₂ = 2 T₁` for pure
amplitude damping), the standard "the transverse relaxation time is at most twice the longitudinal
relaxation time". The printed `T₁/2` is a factor-of-four slip for `2 T₁`; under either convention,
the two printed relations `T₂ = T₁/2` and `T₂ ≤ T₁/2` cannot both hold with a fixed reading of
`T₁, T₂`. We formalise the physically correct, convention-independent content — the exact rate
identity `Γ₂ = Γ₁/2 + Γ_φ` and its correctly oriented specialisations — and record the discrepancy
here rather than silently reproducing a mis-oriented inequality.

## Contents and design

* The **phase-damping channel** `phaseDampingChannel` and its elements `Ẽ₀ = diag(1,√(1-λ))`,
  `Ẽ₁ = √λ P₁` already exist in `Concrete/PhaseDampingCircuit.lean` (Exercise 8.26); we reuse them
  and add the matrix-entry lemmas `phaseDampingChannel_inner_zero_one` (coherence damped by
  `√(1-λ)`), `..._one_one` (excited population preserved), `..._zero_zero`.
* `combinedDampChannel = E_PD ∘ E_AD` — amplitude then phase damping (an honest composition), with
  `combinedDampChannel_inner_zero_one` (coherence damped by `√(1-γ)·√(1-λ)`) and `..._one_one`
  (population damped by `1-γ`): the two entry lemmas chain the phase- and amplitude-damping ones, so
  the decay factors underlying the rates are *derived* from the channels, not asserted.
* `decayRate`/`longitudinalRate`/`transverseRate`/`pureDephasingRate` — the rates (`-log` of a decay
  factor above); `transverseRate_eq` (**the exercise**: `Γ₂ = Γ₁/2 + Γ_φ`, needs `γ, λ < 1` for
  finite rates), `transverseRate_amplitudeDamping` (`Γ₂ = Γ₁/2`),
  `transverseRate_ge_half_longitudinal` (`Γ₁/2 ≤ Γ₂`, `0 ≤ λ < 1`), and strict
  `transverseRate_gt_half_longitudinal` (`0 < λ`) refuting the printed `≤`.

Compare the damping developments `AxQM/Concrete/AmplitudeDampingChannel.lean`,
`AxQM/Concrete/AmplitudeDampingDensityMatrix.lean` and `AxQM/Concrete/PhaseDampingCircuit.lean`.
The statement of Exercise 8.30 is in `AxQM/NC/Ch8/Exercise8_30.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-! ### Matrix entries of the (already-defined) phase-damping channel

The phase-damping channel `phaseDampingChannel` and its operation elements `Ẽ₀ = diag(1, √(1-λ))`
(`phaseDampingKrausZero`, itself amplitude damping's self-adjoint `ampDampKrausZero`) and
`Ẽ₁ = √λ P₁` (`phaseDampingKrausOne`), together with their self-adjointness
(`adjoint_phaseDampingKrausZero` /
`…One`), already live in `Concrete/PhaseDampingCircuit.lean` (Exercise 8.26). Here we only add the
matrix-entry lemmas relevant to relaxation. Unlike amplitude damping, phase damping *preserves the
populations* (its `Ẽ₁ = √λ P₁` is diagonal, not the lowering `√γ σ₋`); only the coherences decay, by
`√(1-λ)`. -/

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `Ẽ₀ |0⟩ = |0⟩` — the ground state is untouched (reusing amplitude damping's `E₀`). -/
@[simp] theorem phaseDampingKrausZero_apply_basisZero (lam : ℝ) :
    phaseDampingKrausZero b lam (b 0) = b 0 :=
  ampDampKrausZero_apply_basisZero b lam

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `Ẽ₀ |1⟩ = √(1-λ) |1⟩` — the excited amplitude is shrunk by `√(1-λ)`. -/
@[simp] theorem phaseDampingKrausZero_apply_basisOne (lam : ℝ) :
    phaseDampingKrausZero b lam (b 1) = (Real.sqrt (1 - lam) : ℂ) • b 1 :=
  ampDampKrausZero_apply_basisOne b lam

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `Ẽ₁ |0⟩ = 0` — the diagonal `Ẽ₁ = √λ P₁` annihilates the ground state. -/
@[simp] theorem phaseDampingKrausOne_apply_basisZero (lam : ℝ) :
    phaseDampingKrausOne b lam (b 0) = 0 := by
  simp only [phaseDampingKrausOne, LinearMap.smul_apply, qubitProj_apply, b.inner_eq_ite,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_smul, smul_zero]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `Ẽ₁ |1⟩ = √λ |1⟩` — unlike amplitude damping, `Ẽ₁` shrinks (does not flip) the excited state. -/
@[simp] theorem phaseDampingKrausOne_apply_basisOne (lam : ℝ) :
    phaseDampingKrausOne b lam (b 1) = (Real.sqrt lam : ℂ) • b 1 := by
  simp only [phaseDampingKrausOne, LinearMap.smul_apply, qubitProj_apply, b.inner_eq_ite,
    Fin.isValue, ↓reduceIte, one_smul]

/-- **Structural decomposition of a matrix element of `E_PD(ρ)`.** Moving each (self-adjoint)
operation element to the left of the inner product:
`⟨x, E_PD(ρ) y⟩ = ⟨Ẽ₀ x, ρ (Ẽ₀ y)⟩ + ⟨Ẽ₁ x, ρ (Ẽ₁ y)⟩`. -/
theorem inner_phaseDampingChannel (lam : ℝ) (ρ : H →ₗ[ℂ] H) (x y : H) :
    inner ℂ x (phaseDampingChannel b lam ρ y)
      = inner ℂ (phaseDampingKrausZero b lam x) (ρ (phaseDampingKrausZero b lam y))
        + inner ℂ (phaseDampingKrausOne b lam x) (ρ (phaseDampingKrausOne b lam y)) := by
  rw [phaseDampingChannel]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_right]
  rw [← LinearMap.adjoint_inner_left (phaseDampingKrausZero b lam)
        (ρ (LinearMap.adjoint (phaseDampingKrausZero b lam) y)) x,
      ← LinearMap.adjoint_inner_left (phaseDampingKrausOne b lam)
        (ρ (LinearMap.adjoint (phaseDampingKrausOne b lam) y)) x]
  simp only [adjoint_phaseDampingKrausZero, adjoint_phaseDampingKrausOne]

/-- **`(0,1)` entry.** `⟨0|E_PD(ρ)|1⟩ = √(1-λ) b` — the coherence is damped by `√(1-λ)`, the
characteristic phase-damping decay of the off-diagonal element. -/
theorem phaseDampingChannel_inner_zero_one (lam : ℝ) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 0) (phaseDampingChannel b lam ρ (b 1))
      = (Real.sqrt (1 - lam) : ℂ) * inner ℂ (b 0) (ρ (b 1)) := by
  rw [inner_phaseDampingChannel]
  simp only [phaseDampingKrausZero_apply_basisZero, phaseDampingKrausZero_apply_basisOne,
    phaseDampingKrausOne_apply_basisZero, phaseDampingKrausOne_apply_basisOne, map_smul,
    inner_smul_right, inner_zero_left, mul_zero, add_zero]

/-- **`(1,1)` entry.** `⟨1|E_PD(ρ)|1⟩ = c` — the excited *population is preserved* (`0 ≤ λ ≤ 1`):
phase damping loses phase coherence without exchanging energy. The two contributions `(1-λ)c` (from
`Ẽ₀`) and `λc` (from `Ẽ₁`) sum to `c`. -/
theorem phaseDampingChannel_inner_one_one (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 1) (phaseDampingChannel b lam ρ (b 1)) = inner ℂ (b 1) (ρ (b 1)) := by
  have hsq1 : (Real.sqrt (1 - lam) : ℂ) * (Real.sqrt (1 - lam) : ℂ) = ((1 - lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsqlam : (Real.sqrt lam : ℂ) * (Real.sqrt lam : ℂ) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  rw [inner_phaseDampingChannel]
  simp only [phaseDampingKrausZero_apply_basisOne, phaseDampingKrausOne_apply_basisOne, map_smul,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← mul_assoc, ← mul_assoc, hsq1, hsqlam, ← add_mul]
  push_cast; ring

/-- **`(0,0)` entry.** `⟨0|E_PD(ρ)|0⟩ = a` — the ground population is also preserved. -/
theorem phaseDampingChannel_inner_zero_zero (lam : ℝ) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 0) (phaseDampingChannel b lam ρ (b 0)) = inner ℂ (b 0) (ρ (b 0)) := by
  rw [inner_phaseDampingChannel]
  simp only [phaseDampingKrausZero_apply_basisZero, phaseDampingKrausOne_apply_basisZero, map_zero,
    inner_zero_right, add_zero]

/-! ### The combined channel: amplitude damping followed by phase damping -/

/-- The **combined damping channel** `E(ρ) = E_PD(E_AD(ρ))`: amplitude damping (parameter `γ`)
followed by phase damping (parameter `λ`). Physically this is a system undergoing both energy
relaxation and pure dephasing. -/
noncomputable def combinedDampChannel (γ lam : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  phaseDampingChannel b lam (ampDampChannel b γ ρ)

/-- **Combined coherence decay.** `⟨0|E(ρ)|1⟩ = √(1-γ)·√(1-λ) · b`: the off-diagonal is damped by
the *product* of the amplitude- and phase-damping factors — the two mechanisms compound. -/
theorem combinedDampChannel_inner_zero_one (γ lam : ℝ) (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 0) (combinedDampChannel b γ lam ρ (b 1))
      = (Real.sqrt (1 - γ) : ℂ) * (Real.sqrt (1 - lam) : ℂ) * inner ℂ (b 0) (ρ (b 1)) := by
  rw [combinedDampChannel, phaseDampingChannel_inner_zero_one, ampDampChannel_inner_zero_one]
  ring

/-- **Combined excited-population decay.** `⟨1|E(ρ)|1⟩ = (1-γ) c`: dephasing preserves populations,
so the population decays by `1-γ`, exactly as under amplitude damping alone (`0 ≤ λ ≤ 1`, `γ ≤ 1`).
-/
theorem combinedDampChannel_inner_one_one (γ lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hγ1 : γ ≤ 1)
    (ρ : H →ₗ[ℂ] H) :
    inner ℂ (b 1) (combinedDampChannel b γ lam ρ (b 1))
      = ((1 - γ : ℝ) : ℂ) * inner ℂ (b 1) (ρ (b 1)) := by
  rw [combinedDampChannel, phaseDampingChannel_inner_one_one b lam h0 h1,
    ampDampChannel_inner_one_one b γ hγ1]

/-! ### Relaxation rates

A decay factor `f` per unit time step corresponds, via `f = e^{-Γ}`, to a decay **rate**
`Γ = decayRate f = -log f` (the exponential decay rate of N&C eq. 7.144, at unit `t`). The three
rates below are `-log` of the channel decay factors established above: the *longitudinal* rate `Γ₁`
from the population factor `1-γ`, the *transverse* rate `Γ₂` from the combined coherence factor
`√(1-γ)·√(1-λ)`, and the *pure-dephasing* rate `Γ_φ` from the phase-damping coherence factor
`√(1-λ)`. -/

/-- The exponential **decay rate** `Γ = -log f` associated to a per-step decay factor `f = e^{-Γ}`
(N&C eq. 7.144, at unit time): the larger the rate, the faster the exponential decay. -/
noncomputable def decayRate (f : ℝ) : ℝ := -Real.log f

/-- The **longitudinal (`T₁`, spin–lattice) relaxation rate** of amplitude damping: the decay rate
of the diagonal (excited population), whose amplitude-damping factor is
`⟨1|E_AD(ρ)|1⟩/⟨1|ρ|1⟩ = 1-γ`
(`ampDampChannel_inner_one_one`). -/
noncomputable def longitudinalRate (γ : ℝ) : ℝ := decayRate (1 - γ)

/-- The **transverse (`T₂`, spin–spin) relaxation rate** of the combined channel: the decay rate of
the off-diagonal (coherence), whose combined factor is `⟨0|E(ρ)|1⟩/⟨0|ρ|1⟩ = √(1-γ)·√(1-λ)`
(`combinedDampChannel_inner_zero_one`). -/
noncomputable def transverseRate (γ lam : ℝ) : ℝ :=
  decayRate (Real.sqrt (1 - γ) * Real.sqrt (1 - lam))

/-- The **pure-dephasing rate** contributed by phase damping alone: the decay rate of its coherence
factor `⟨0|E_PD(ρ)|1⟩/⟨0|ρ|1⟩ = √(1-λ)` (`phaseDampingChannel_inner_zero_one`). -/
noncomputable def pureDephasingRate (lam : ℝ) : ℝ := decayRate (Real.sqrt (1 - lam))

/-- **Exercise 8.30 (rate identity).** The transverse relaxation rate of the combined
amplitude-plus-phase-damping channel splits exactly as
`Γ₂ = Γ₁/2 + Γ_φ` — half the longitudinal (amplitude-damping) rate, plus the pure-dephasing rate.
Needs `γ < 1`, `λ < 1` so the decay factors are positive (finite rates). This is the additive-rate
form of the standard `T₁`/`T₂` relation and contains both parts of the exercise (see the two
corollaries below). -/
theorem transverseRate_eq (γ lam : ℝ) (hγ : γ < 1) (hlam : lam < 1) :
    transverseRate γ lam = longitudinalRate γ / 2 + pureDephasingRate lam := by
  unfold transverseRate longitudinalRate pureDephasingRate decayRate
  rw [Real.log_mul (Real.sqrt_ne_zero'.mpr (by linarith)) (Real.sqrt_ne_zero'.mpr (by linarith)),
    Real.log_sqrt (by linarith), Real.log_sqrt (by linarith)]
  ring

/-- The pure-dephasing rate of a *trivial* (`λ = 0`) phase-damping stage is zero: no phase damping
means no extra coherence decay. -/
@[simp] theorem pureDephasingRate_zero : pureDephasingRate 0 = 0 := by
  simp [pureDephasingRate, decayRate]

/-- **Exercise 8.30, part 1 — `T₂ = T₁/2` for amplitude damping.** With no phase damping (`λ = 0`),
the transverse rate is exactly half the longitudinal rate: the coherence decays at half the rate of
the population. -/
theorem transverseRate_amplitudeDamping (γ : ℝ) (hγ : γ < 1) :
    transverseRate γ 0 = longitudinalRate γ / 2 := by
  rw [transverseRate_eq γ 0 hγ (by norm_num), pureDephasingRate_zero, add_zero]

/-- The pure-dephasing rate is nonnegative on the physical range `0 ≤ λ < 1`: its coherence factor
`√(1-λ) ≤ 1`, so `-log√(1-λ) ≥ 0`. -/
theorem pureDephasingRate_nonneg (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    0 ≤ pureDephasingRate lam := by
  have hle : Real.sqrt (1 - lam) ≤ 1 := by
    have h : Real.sqrt (1 - lam) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h
  have hpos : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.mpr (by linarith)
  have := Real.log_nonpos hpos.le hle
  simp only [pureDephasingRate, decayRate]; linarith

/-- The pure-dephasing rate is strictly positive when phase damping is present (`0 < λ < 1`): its
coherence factor `√(1-λ) < 1`, so `-log√(1-λ) > 0`. -/
theorem pureDephasingRate_pos (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    0 < pureDephasingRate lam := by
  have hlt : Real.sqrt (1 - lam) < 1 := by
    have h : Real.sqrt (1 - lam) < Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    rwa [Real.sqrt_one] at h
  have hpos : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.mpr (by linarith)
  have := Real.log_neg hpos hlt
  simp only [pureDephasingRate, decayRate]; linarith

/-- **Exercise 8.30, part 2 — the combined bound.** When amplitude and phase damping are both
applied (`0 ≤ λ < 1`), the transverse rate is at least half the longitudinal rate: `Γ₁/2 ≤ Γ₂`.
Equivalently, in the relaxation-*time* convention (`T = 1/Γ`) this is `T₂ ≤ 2 T₁`, the standard
"transverse relaxation time is at most twice the longitudinal time" — the correctly oriented form of
the exercise's printed `T₂ ≤ T₁/2` (see the module docstring). -/
theorem transverseRate_ge_half_longitudinal (γ lam : ℝ) (hγ : γ < 1) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    longitudinalRate γ / 2 ≤ transverseRate γ lam := by
  rw [transverseRate_eq γ lam hγ h1]
  linarith [pureDephasingRate_nonneg lam h0 h1]

/-- **The bound is strict once phase damping is genuinely present** (`0 < λ < 1`): `Γ₁/2 < Γ₂`. This
formally exhibits that the printed inequality `T₂ ≤ T₁/2` (equivalently `Γ₂ ≤ Γ₁/2` as rates)
*fails* — the transverse rate strictly exceeds half the longitudinal rate. -/
theorem transverseRate_gt_half_longitudinal (γ lam : ℝ) (hγ : γ < 1) (h0 : 0 < lam) (h1 : lam < 1) :
    longitudinalRate γ / 2 < transverseRate γ lam := by
  rw [transverseRate_eq γ lam hγ h1]
  linarith [pureDephasingRate_pos lam h0 h1]

end AxQM.Concrete

end
