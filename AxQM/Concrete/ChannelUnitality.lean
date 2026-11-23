/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import AxQM.Concrete.PhaseDampingChannel
import AxQM.Concrete.Pauli

/-!
# Concrete: unitality of the single-qubit noise channels (N&C Exercise 8.29)

This file records the content of
**Nielsen & Chuang, Exercise 8.29 (Unitality)**.

Show depolarizing and phase damping channels are unital (E(I)=I) but amplitude damping is not.

Unitality mirrors trace preservation: a quantum operation `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` is **trace
preserving** iff `∑ₖ Eₖ† Eₖ = I`, and **unital** iff `E(I) = ∑ₖ Eₖ Eₖ† = I`. This file evaluates
`E(I)` for the three canonical single-qubit noise channels of N&C §8.3, reusing the channel
definitions already developed in the amplitude- and phase-damping cluster.

## Contents

* `depolChannel p ρ` — the **qubit depolarizing channel** in operator-sum form
  `E(ρ) = (1 - 3p/4) ρ + (p/4)(X ρ X + Y ρ Y + Z ρ Z)` (N&C eq. 8.102), on `2 × 2` matrices, and
  `depolChannel_apply_one` — **unital**: `E(I) = I`, since `X X† + Y Y† + Z Z† = 3 I` and
  `(1 - 3p/4) + 3·(p/4) = 1`.
* `phaseDampChannel_apply_one` — the **phase-damping channel is unital**: `E_PD(I) = I`
  (`0 ≤ λ ≤ 1`), via `E₀ E₀† + E₁ E₁† = (P₀ + (1-λ) P₁) + λ P₁ = P₀ + P₁ = I`. (`phaseDampChannel`
  lives in `AxQM/Concrete/PhaseDampingChannel.lean`.)
* `ampDampChannel_apply_one` — the **amplitude-damping channel value at the identity**:
  `E_AD(I) = (1+γ) P₀ + (1-γ) P₁ = I + γ Z` (`0 ≤ γ ≤ 1`), reusing `ampDampChannel`
  (`AxQM/Concrete/AmplitudeDampingChannel.lean`) and the shared ladder identity `σ₋ σ₊ = P₀`
  (`qubitLower_comp_adjoint_self`, in `AxQM/Concrete/QubitBasisOperators.lean` beside its companion
  `qubitLower_adjoint_comp_self`, `σ₊ σ₋ = P₁`).
* `ampDampChannel_not_unital` — **amplitude damping is not unital**: `E_AD(I) ≠ I` for `0 < γ`,
  because `E_AD(I) |0⟩ = (1+γ) |0⟩ ≠ |0⟩` — the extra `γ Z` term biases the excited-state
  population toward the ground state (a channel with a preferred fixed point, the `|0⟩` "north
  pole", not the maximally mixed state).

## Why the operator-sum form for the depolarizing channel

N&C's display `E(ρ) = p (I/2) + (1-p) ρ` (eq. 8.100) is an **affine** map, correct only on
trace-one states (there `I/2 = (ρ + XρX + YρY + ZρZ)/4`, eq. 8.101). Unitality asks for the value
of the *linear* quantum operation at `I` (trace two), so it must be evaluated through the honest
operator-sum (Kraus) form, eq. 8.102 — the map whose operation elements are
`{√(1-3p/4) I, √p X/2, √p Y/2, √p Z/2}`. (Evaluating eq. 8.100 at `I` would give the wrong
`(1 - p/2) I`, precisely because it is not the linear extension.) `depolChannel` is therefore eq.
8.102, and its unitality is a linear-algebra fact holding for the identity of trace two.

## Content

The content of Exercise 8.29 is the direct linear-algebra computation of `E(I) = ∑ₖ Eₖ Eₖ†` for
three explicit channels. Compare Exercises 8.17 (depolarizing average), 8.22 (amplitude-damping
density matrix) and 8.27 (phase damping = phase flip). The statement of Exercise 8.29 is in
`AxQM/NC/Ch8/Exercise8_29.lean`; the declarations are below.

The abstract predicate `AxQM.IsUnital` (`f (I/d) = I/d`, over a channel
`f : State S → State S`) developed for **Problem 8.3** quantifies over the whole *space* of channels
on a `QSystem` — the right tool for Problem 8.3's structural theorems (every unital *qubit* channel
is random-unitary). Exercise 8.29 is the complementary concrete task: computing `E(I)` for three
named channels. The two agree — the facts proved here (`E(I) = I`, `E_AD(I) ≠ I`) are exactly what
`IsUnital` reduces to (`E(I/2) = I/2 ⇔ E(I) = I` by linearity) — but the concrete channels
here are operator-sum maps, so their unitality is naturally an operator-level
statement.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

open Matrix

/-- **The single-qubit depolarizing channel** in operator-sum form
`E(ρ) = (1 - 3p/4) ρ + (p/4)(X ρ X + Y ρ Y + Z ρ Z)` (Nielsen & Chuang eq. 8.102), on `2 × 2`
complex matrices. This is the *linear* quantum operation with operation elements
`{√(1-3p/4) I, √p X/2, √p Y/2, √p Z/2}`; on trace-one states it agrees with N&C's completely-mixing
display `E(ρ) = p (I/2) + (1-p) ρ` (eq. 8.100), via `I/2 = (ρ + XρX + YρY + ZρZ)/4` (eq. 8.101,
`pauliAverage_blochMatrix`). -/
noncomputable def depolChannel (p : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 - 3 * p / 4 : ℝ) : ℂ) • ρ
    + ((p / 4 : ℝ) : ℂ) • (pauliX * ρ * pauliX + pauliY * ρ * pauliY + pauliZ * ρ * pauliZ)

/-- **The depolarizing channel is unital** (Exercise 8.29): `E(I) = I`. Since the Pauli matrices are
involutions (`X I X = X² = I`, likewise `Y`, `Z`), the operator-sum evaluated at the identity is
`(1 - 3p/4) I + (p/4)(I + I + I) = (1 - 3p/4 + 3p/4) I = I`. -/
theorem depolChannel_apply_one (p : ℝ) : depolChannel p 1 = 1 := by
  simp only [depolChannel, mul_one, pauliX_mul_self, pauliY_mul_self, pauliZ_mul_self]
  match_scalars
  ring

section Qubit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- **The phase-damping channel is unital** (Exercise 8.29): `E_PD(I) = I` for `0 ≤ λ ≤ 1`. Both
operation elements are self-adjoint, so `E_PD(I) = E₀ E₀† + E₁ E₁† = E₀² + E₁²`; with
`E₀² = P₀ + (1-λ) P₁` (orthogonal projectors, `(√(1-λ))² = 1-λ`) and `E₁² = λ P₁` (`(√λ)² = λ`),
this is `P₀ + (1-λ) P₁ + λ P₁ = P₀ + P₁ = I`. (Physically consistent with phase damping being the
phase-flip channel, Exercise 8.27 — a random unitary mixture of `I` and `Z`, hence unital.) -/
theorem phaseDampChannel_apply_one (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    phaseDampChannel b lam LinearMap.id = LinearMap.id := by
  have hsq1 : (Real.sqrt (1 - lam) : ℂ) * (Real.sqrt (1 - lam) : ℂ) = ((1 - lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsqL : (Real.sqrt lam : ℂ) * (Real.sqrt lam : ℂ) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  rw [phaseDampChannel, adjoint_phaseDampKrausZero, adjoint_phaseDampKrausOne,
    LinearMap.id_comp, LinearMap.id_comp]
  -- `E₀ E₀ = P₀ + (1-λ) P₁` (square of the diagonal operator, `(√(1-λ))² = 1-λ`).
  have hE0 : phaseDampKrausZero b lam ∘ₗ phaseDampKrausZero b lam
      = qubitProj b 0 + ((1 - lam : ℝ) : ℂ) • qubitProj b 1 := by
    rw [phaseDampKrausZero, qubitProjDiag_comp_self, hsq1]
  -- `E₁ E₁ = λ P₁`.
  have hE1 : phaseDampKrausOne b lam ∘ₗ phaseDampKrausOne b lam = (lam : ℂ) • qubitProj b 1 := by
    rw [phaseDampKrausOne, LinearMap.smul_comp, LinearMap.comp_smul, qubitProj_comp_qubitProj]
    simp only [Fin.isValue, ↓reduceIte, smul_smul, hsqL]
  rw [hE0, hE1, add_assoc, ← add_smul,
    show ((1 - lam : ℝ) : ℂ) + (lam : ℂ) = 1 by push_cast; ring, one_smul, sum_qubitProj]

/-- **The value of the amplitude-damping channel at the identity**:
`E_AD(I) = (1+γ) P₀ + (1-γ) P₁ = I + γ Z` (`0 ≤ γ ≤ 1`). Here `E_AD(I) = E₀ E₀† + E₁ E₁†` with
`E₀ E₀† = P₀ + (1-γ) P₁` (`E₀` self-adjoint, `(√(1-γ))² = 1-γ`) and `E₁ E₁† = γ P₀`
(`σ₋ σ₊ = P₀`, `(√γ)² = γ`). The deviation from the identity is `γ Z = γ(P₀ - P₁)`: the channel
fixes the `|0⟩` "north pole" rather than the maximally mixed state. -/
theorem ampDampChannel_apply_one (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ampDampChannel b γ LinearMap.id
      = ((1 + γ : ℝ) : ℂ) • qubitProj b 0 + ((1 - γ : ℝ) : ℂ) • qubitProj b 1 := by
  have hsq1 : (Real.sqrt (1 - γ) : ℂ) * (Real.sqrt (1 - γ) : ℂ) = ((1 - γ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsqγ : (Real.sqrt γ : ℂ) * (Real.sqrt γ : ℂ) = (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hγ0]
  rw [ampDampChannel, adjoint_ampDampKrausZero, LinearMap.id_comp, LinearMap.id_comp]
  -- `E₀ E₀ = P₀ + (1-γ) P₁` (square of the diagonal operator, `(√(1-γ))² = 1-γ`).
  have hE0 : ampDampKrausZero b γ ∘ₗ ampDampKrausZero b γ
      = qubitProj b 0 + ((1 - γ : ℝ) : ℂ) • qubitProj b 1 := by
    rw [ampDampKrausZero, qubitProjDiag_comp_self, hsq1]
  -- `E₁ E₁† = γ P₀`.
  have hE1 : ampDampKrausOne b γ ∘ₗ LinearMap.adjoint (ampDampKrausOne b γ)
      = (γ : ℂ) • qubitProj b 0 := by
    rw [ampDampKrausOne, LinearMap.adjoint_smul, LinearMap.smul_comp, LinearMap.comp_smul,
      qubitLower_comp_adjoint_self, smul_smul, RCLike.star_def, Complex.conj_ofReal, hsqγ]
  rw [hE0, hE1]
  match_scalars <;> ring

/-- **Amplitude damping is not unital** (Exercise 8.29): `E_AD(I) ≠ I` for `0 < γ`. Evaluating the
value `E_AD(I) = (1+γ) P₀ + (1-γ) P₁` at the ground state gives `E_AD(I) |0⟩ = (1+γ) |0⟩`, whereas
`I |0⟩ = |0⟩`; were they equal we would have `γ |0⟩ = 0`, impossible for `γ ≠ 0` and `|0⟩ ≠ 0`. This
is the asymmetry of amplitude damping: `E₁ = √γ |0⟩⟨1|` moves population into `|0⟩` without a
balancing `|0⟩ → |1⟩` process, so the identity is not preserved. -/
theorem ampDampChannel_not_unital (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ampDampChannel b γ LinearMap.id ≠ LinearMap.id := by
  intro h
  rw [ampDampChannel_apply_one b γ hγ.le hγ1] at h
  have hb0 := LinearMap.congr_fun h (b 0)
  simp only [LinearMap.add_apply, LinearMap.smul_apply, qubitProj_apply, b.inner_eq_ite,
    Fin.isValue, ↓reduceIte, Fin.reduceEq, one_smul, smul_zero, add_zero, zero_smul,
    LinearMap.id_coe, id_eq] at hb0
  -- `hb0 : (1+γ) • b 0 = b 0`, so `γ • b 0 = 0`.
  have hzero : (γ : ℂ) • b 0 = 0 := by
    have h2 : (((1 + γ : ℝ) : ℂ) - 1) • b 0 = 0 := by rw [sub_smul, one_smul, hb0, sub_self]
    rwa [show (((1 + γ : ℝ) : ℂ) - 1) = (γ : ℂ) by push_cast; ring] at h2
  exact smul_ne_zero (by exact_mod_cast ne_of_gt hγ) (b.orthonormal.ne_zero 0) hzero

end Qubit

end AxQM.Concrete

end
