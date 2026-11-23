/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.JaynesCummingsUnitary
import AxQM.Concrete.AmplitudeDampingChannel
import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Concrete: spontaneous emission is amplitude damping (N&C Exercise 8.24)

This file works, at the level of operators on an arbitrary two-dimensional complex inner product
space `H` (a qubit) with a chosen computational orthonormal basis
`b : OrthonormalBasis (Fin 2) ℂ H`, through Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Exercise 8.24** (p. 381–382): *spontaneous emission
is amplitude damping*. Take the resonant Jaynes–Cummings (vacuum-Rabi) unitary `U`
(`Concrete.jaynesCummingsZeroDetuningUnitary`, N&C eq. 7.77 at detuning `δ = 0`, the infrastructure
of `Concrete/JaynesCummingsUnitary.lean`) on `H ⊗[ℂ] H` — the **atom** (left factor) coupled to a
single field **mode** (right factor) — and give the quantum operation obtained by *tracing over the
field*.

## The reduction

The atom (system) is the left factor; the field (environment) is the right factor, prepared in the
vacuum `|0⟩`. The dilation is `V = U (· ⊗ |0⟩_field)` (`spontaneousEmissionDilation`) and the traced
quantum operation is `E(ρ) = tr_field(U (ρ ⊗ |0⟩⟨0|) U†)` (`spontaneousEmissionChannel`, the
operator-sum route via `LinearMap.partialTraceRight`). Reading off the operation elements
`Eₖ = ⟨k_field|U|0_field⟩` (N&C eqs. 8.9–8.10) from `U|00⟩ = |00⟩`,
`U|10⟩ = cos(gt)|10⟩ - i sin(gt)|01⟩` gives, **unconditionally**,

`E₀ = |0⟩⟨0| + cos(gt) |1⟩⟨1| = diag(1, cos gt)`,   `E₁ = -i sin(gt) |0⟩⟨1|`.

These are exactly the amplitude-damping operation elements of N&C eq. 8.108
(`Concrete.ampDampKrausZero`, `Concrete.ampDampKrausOne`) with `γ = sin²(gt)`, up to two
book-keeping points:

* **`E₀`**: `ampDampKrausZero` has `√(1-γ) ≥ 0`, so the identification `√(1 - sin²(gt)) = cos(gt)`
  holds precisely when `cos(gt) ≥ 0` — exactly N&C's implicit regime (their §8.3.5 amplitude damping
  writes `√(1-γ) = cos θ` with `cos θ ≥ 0`; here `θ = gt`, and `γ = sin²(gt) ∈ [0,1]` sweeps the
  full range as `gt` runs over `[0, π/2]`). The channel-equality headline therefore carries the
  hypothesis `0 ≤ cos(gt)`.
* **`E₁`**: the honest trace yields `E₁ = -i sin(gt) |0⟩⟨1|`, whereas amplitude damping (eq. 8.108)
  has `E₁ = √γ |0⟩⟨1|`. The two differ by the global phase `-i`, which is **physically irrelevant**:
  a quantum operation is unchanged by a unit-phase multiple of an operation element, since
  `(c E₁) ρ (c E₁)† = |c|² E₁ ρ E₁†` (here `|-i|² = 1`). We identify at the channel level, where the
  phase provably washes out (`spontaneousEmissionChannel_eq_ampDampChannel`), rather than silently
  dropping the `-i` from `E₁` — that would be a fabrication of the operation element.

The headline `spontaneousEmissionChannel_eq_ampDampChannel` is therefore

`tr_field(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`,   with `γ = sin²(gt)`, for `0 ≤ cos(gt)`,

which is what the exercise asks. The operation elements and the completeness relation
`∑ₖ Eₖ† Eₖ = I` (`sum_adjoint_krausOp_spontaneousEmissionDilation`) hold **unconditionally**: the
traced map is trace preserving for every `gt`, as it must be, being the partial trace of a genuine
unitary conjugation.

## Related items

The objects are `LinearMap`s on an inner product space, `TensorProduct`, an `OrthonormalBasis`,
`InnerProductSpace.rankOne`, and the partial trace / operator sum of
`ToMathlib.Analysis.InnerProductSpace.OperatorSum`. Compare the amplitude-damping items: Exercise
8.20's circuit (`AxQM/Concrete/AmplitudeDampingCircuit.lean`) and the operator-sum interactions of
Exercises 8.4/8.5. The statement of Exercise 8.24 is in `AxQM/NC/Ch8/Exercise8_24.lean`.

## Design

The reduction is a direct application of the operator-sum infrastructure
(`LinearMap.krausOp`, `LinearMap.partialTraceRight_conj_eq_sum_krausOp`), reusing the already-built
Jaynes–Cummings unitary (including its action on the field-vacuum column
`Concrete.jaynesCummingsZeroDetuningUnitary_apply_tmul_zero`) and the amplitude-damping
channel/operation-elements of `Concrete/AmplitudeDampingChannel.lean`; the only genuine work is
reading off the operation elements and the phase-washout algebra `(c L) ρ (c L)† = |c|² L ρ L†`
(`smul_comp_conj`).

## Contents

* `spontaneousEmissionDilation b g t = U (· ⊗ |0⟩_field)` — the dilation `V`.
* `krausOp_spontaneousEmissionDilation_zero_eq` / `_one_eq` — the operation elements
  `E₀ = diag(1, cos gt)`, `E₁ = -i sin(gt) |0⟩⟨1|` (both unconditional).
* `krausOp_spontaneousEmissionDilation_zero_eq_ampDampKrausZero` —
  `E₀ = ampDampKrausZero b (sin²(gt))` for `0 ≤ cos(gt)`.
* `smul_comp_conj` — the phase-washout algebra `(c L) ρ (c L)† = |c|² L ρ L†` (arbitrary `L`).
* `spontaneousEmissionChannel b g t ρ = tr_field(V ρ V†)`, with **the answer**
  `spontaneousEmissionChannel_eq_ampDampChannel : spontaneousEmissionChannel b g t ρ =
  ampDampChannel b (sin²(gt)) ρ` (for `0 ≤ cos(gt)`).
* `sum_adjoint_krausOp_spontaneousEmissionDilation` — completeness `∑ₖ Eₖ† Eₖ = I` (unconditional).
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The conjugation coefficient `|-i s|² = s²` for real `s`:
`conj(-i s) · (-i s) = s²`. The `E₁` operation element `-i sin(gt) σ₋` conjugates `ρ` with this
coefficient (`smul_comp_conj`), matching amplitude damping's `√γ σ₋` at `γ = sin²(gt) = s²`; the
scalar identity behind the `-i` phase washout, shared by the channel and completeness proofs. -/
theorem star_neg_I_mul_ofReal_mul_self (s : ℝ) :
    starRingEnd ℂ (-Complex.I * (s : ℂ)) * (-Complex.I * (s : ℂ)) = ((s ^ 2 : ℝ) : ℂ) := by
  rw [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]
  linear_combination (-(s : ℂ) ^ 2) * Complex.I_sq

/-- The **dilation** `V = U (· ⊗ |0⟩_field) : H →ₗ H ⊗ H`: prepare the field in the vacuum `|0⟩`,
then apply the resonant Jaynes–Cummings (vacuum-Rabi) unitary. Its operation elements
`krausOp b V k` are the Kraus operators of the spontaneous-emission channel. -/
noncomputable def spontaneousEmissionDilation (g t : ℝ) : H →ₗ[ℂ] H ⊗[ℂ] H :=
  jaynesCummingsZeroDetuningUnitary b g t ∘ₗ LinearMap.embedRight b 0

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **The first operation element** `E₀ = ⟨0_field|U|0_field⟩ = |0⟩⟨0| + cos(gt) |1⟩⟨1| =
diag(1, cos gt)` (unconditional). The atom that emitted no photon keeps its ground amplitude and has
its excited amplitude scaled by `cos gt`. -/
theorem krausOp_spontaneousEmissionDilation_zero_eq (g t : ℝ) :
    LinearMap.krausOp b (spontaneousEmissionDilation b g t) 0
      = qubitProj b 0 + (Real.cos (g * t) : ℂ) • qubitProj b 1 := by
  ext x
  rw [LinearMap.krausOp_apply, spontaneousEmissionDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, jaynesCummingsZeroDetuningUnitary_apply_tmul_zero]
  simp only [map_add, map_smul, LinearMap.restrictRight_tmul, b.inner_eq_ite, LinearMap.add_apply,
    LinearMap.smul_apply, qubitProj_apply, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  module

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **The second operation element** `E₁ = ⟨1_field|U|0_field⟩ = -i sin(gt) |0⟩⟨1| = -i sin(gt) σ₋`
(unconditional): the atom decayed to its ground state, emitting a photon into the field, with
amplitude `-i sin(gt)`. The global phase `-i` is physically irrelevant (it washes out of the
channel `E₁ ρ E₁†`); this is amplitude damping's `E₁ = √γ σ₋` at `γ = sin²(gt)` up to that phase. -/
theorem krausOp_spontaneousEmissionDilation_one_eq (g t : ℝ) :
    LinearMap.krausOp b (spontaneousEmissionDilation b g t) 1
      = (-Complex.I * (Real.sin (g * t) : ℂ)) • qubitLower b := by
  ext x
  rw [LinearMap.krausOp_apply, spontaneousEmissionDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, jaynesCummingsZeroDetuningUnitary_apply_tmul_zero]
  simp only [map_add, map_smul, LinearMap.restrictRight_tmul, b.inner_eq_ite, LinearMap.smul_apply,
    qubitLower, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, Fin.isValue,
    ↓reduceIte, Fin.reduceEq]
  module

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The first operation element **is** the amplitude-damping `E₀ = ampDampKrausZero b (sin²(gt))`,
for `0 ≤ cos(gt)` — the regime where `√(1 - sin²(gt)) = cos(gt)` (N&C's implicit regime for
amplitude damping, §8.3.5). -/
theorem krausOp_spontaneousEmissionDilation_zero_eq_ampDampKrausZero (g t : ℝ)
    (hcos : 0 ≤ Real.cos (g * t)) :
    LinearMap.krausOp b (spontaneousEmissionDilation b g t) 0
      = ampDampKrausZero b (Real.sin (g * t) ^ 2) := by
  have hsqrt : (Real.sqrt (1 - Real.sin (g * t) ^ 2) : ℂ) = (Real.cos (g * t) : ℂ) := by
    rw [← Real.cos_sq', Real.sqrt_sq hcos]
  rw [krausOp_spontaneousEmissionDilation_zero_eq, ampDampKrausZero, hsqrt]

omit [CompleteSpace H] in
/-- **Phase washout.** Conjugating `ρ` by a scalar multiple `c L` of any operator `L` depends on `c`
only through `|c|² = c̄ c`: `(c L) ρ (c L)† = (c̄ c) L ρ L†`. In particular a unit-phase multiple of
an operation element leaves the quantum operation `L ρ L†` unchanged — the phase-washout algebra is
`L`-independent, so it is stated here for an arbitrary `L` and instantiated at
`L = σ₋ = qubitLower b` in `spontaneousEmissionChannel_eq_ampDampChannel` (this is why the physical
phase `-i` on `E₁` does not affect the spontaneous-emission channel). -/
theorem smul_comp_conj (c : ℂ) (L ρ : H →ₗ[ℂ] H) :
    (c • L) ∘ₗ ρ ∘ₗ LinearMap.adjoint (c • L)
      = (starRingEnd ℂ c * c) • (L ∘ₗ ρ ∘ₗ LinearMap.adjoint L) := by
  rw [LinearMap.adjoint_smul, LinearMap.comp_smul, LinearMap.comp_smul, LinearMap.smul_comp,
    smul_smul, RCLike.star_def]

/-- The **spontaneous-emission quantum operation**, in dilation form `E(ρ) = tr_field(V ρ V†)` (the
operator-sum route to `tr_field(U (ρ ⊗ |0⟩⟨0|) U†)`). -/
noncomputable def spontaneousEmissionChannel (g t : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b (spontaneousEmissionDilation b g t ∘ₗ ρ ∘ₗ
    LinearMap.adjoint (spontaneousEmissionDilation b g t))

omit [CompleteSpace H] in
/-- **N&C Exercise 8.24 (the answer): spontaneous emission is amplitude damping.** Tracing the field
out of the resonant Jaynes–Cummings evolution returns exactly the amplitude-damping channel `E_AD`
of `Concrete/AmplitudeDampingChannel.lean` at `γ = sin²(gt)`:

`tr_field(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`,   for `0 ≤ cos(gt)`.

The operation elements `Eₖ = ⟨k_field|U|0_field⟩` are `E₀ = diag(1, cos gt)` and
`E₁ = -i sin(gt) |0⟩⟨1|` (`krausOp_spontaneousEmissionDilation_zero`/`_one`), matching N&C eq. 8.108
with `cos(gt) = √(1-γ)` (needing `cos(gt) ≥ 0`) and `E₁`'s coefficient equal to `√γ` up to the
global phase `-i`, which washes out of the channel `E₁ ρ E₁†` (`smul_comp_conj`). The result
is the operator-sum identity `partialTraceRight_conj_eq_sum_krausOp` combined with these
identifications. -/
theorem spontaneousEmissionChannel_eq_ampDampChannel (g t : ℝ) (hcos : 0 ≤ Real.cos (g * t))
    (ρ : H →ₗ[ℂ] H) :
    spontaneousEmissionChannel b g t ρ = ampDampChannel b (Real.sin (g * t) ^ 2) ρ := by
  -- The `-i` on `E₁` and the `√γ` on amplitude damping's `E₁` give the same conjugation coefficient
  -- `|c|² = sin²(gt)`, so the two `E₁` terms coincide (the phase washes out).
  have hR : starRingEnd ℂ (Real.sqrt (Real.sin (g * t) ^ 2) : ℂ) *
      (Real.sqrt (Real.sin (g * t) ^ 2) : ℂ) = ((Real.sin (g * t) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (sq_nonneg _)]
  rw [spontaneousEmissionChannel, LinearMap.partialTraceRight_conj_eq_sum_krausOp, Fin.sum_univ_two,
    krausOp_spontaneousEmissionDilation_zero_eq_ampDampKrausZero b g t hcos,
    krausOp_spontaneousEmissionDilation_one_eq, ampDampChannel, ampDampKrausOne,
    smul_comp_conj, smul_comp_conj, star_neg_I_mul_ofReal_mul_self (Real.sin (g * t)), hR]

/-- **Trace preservation (a genuine quantum operation).** The spontaneous-emission operation
elements satisfy the completeness relation `∑ₖ Eₖ† Eₖ = I` (N&C eq. 8.114 context),
**unconditionally** in
`gt`: `E₀† E₀ = P₀ + cos²(gt) P₁` (`E₀` self-adjoint) and `E₁† E₁ = sin²(gt) P₁` (`σ₊ σ₋ = P₁`,
`|-i sin(gt)|² = sin²(gt)`), summing to `P₀ + (cos²+sin²) P₁ = P₀ + P₁ = I`. The traced map is trace
preserving for every `gt`, as it must be, being the partial trace of a unitary conjugation. -/
theorem sum_adjoint_krausOp_spontaneousEmissionDilation (g t : ℝ) :
    ∑ k, LinearMap.adjoint (LinearMap.krausOp b (spontaneousEmissionDilation b g t) k) ∘ₗ
        LinearMap.krausOp b (spontaneousEmissionDilation b g t) k = LinearMap.id := by
  have hcos2 : (Real.cos (g * t) : ℂ) * (Real.cos (g * t) : ℂ)
      = ((Real.cos (g * t) ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]; norm_num [sq]
  rw [Fin.sum_univ_two, krausOp_spontaneousEmissionDilation_zero_eq,
    krausOp_spontaneousEmissionDilation_one_eq]
  -- `E₀† E₀ = P₀ + cos²(gt) P₁`.
  have hE0 : LinearMap.adjoint (qubitProj b 0 + (Real.cos (g * t) : ℂ) • qubitProj b 1) ∘ₗ
      (qubitProj b 0 + (Real.cos (g * t) : ℂ) • qubitProj b 1)
      = qubitProj b 0 + ((Real.cos (g * t) ^ 2 : ℝ) : ℂ) • qubitProj b 1 := by
    rw [map_add, LinearMap.adjoint_smul, adjoint_qubitProj, adjoint_qubitProj, RCLike.star_def,
      Complex.conj_ofReal]
    simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul,
      qubitProj_comp_qubitProj, Fin.isValue, Fin.reduceEq, ↓reduceIte, smul_zero, add_zero,
      zero_add, smul_smul, hcos2]
  -- `E₁† E₁ = sin²(gt) P₁`.
  have hE1 : LinearMap.adjoint ((-Complex.I * (Real.sin (g * t) : ℂ)) • qubitLower b) ∘ₗ
      ((-Complex.I * (Real.sin (g * t) : ℂ)) • qubitLower b)
      = ((Real.sin (g * t) ^ 2 : ℝ) : ℂ) • qubitProj b 1 := by
    rw [LinearMap.adjoint_smul, LinearMap.smul_comp, LinearMap.comp_smul,
      qubitLower_adjoint_comp_self, smul_smul, RCLike.star_def,
      star_neg_I_mul_ofReal_mul_self (Real.sin (g * t))]
  have hsum : ((Real.cos (g * t) ^ 2 : ℝ) : ℂ) + ((Real.sin (g * t) ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_add, Real.cos_sq_add_sin_sq]; norm_num
  rw [hE0, hE1, add_assoc, ← add_smul, hsum, one_smul, sum_qubitProj]

end AxQM.Concrete

end
