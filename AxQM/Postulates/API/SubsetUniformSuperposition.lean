/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.UniformSuperposition
import AxQM.Postulates.API.QuditMeasurement

/-!
# AxQM.Postulates.API — the uniform superposition over a subset (the solution state `|β⟩`)

The **uniform superposition over a subset** `T` of the computational basis of `qudit d`,

`|β⟩ = M⁻¹ᐟ² ∑_{x ∈ T} |x⟩`   (`M = |T|`, `d = N` the register size),

as a pure state. For the multiple-solution continuous-time search of Nielsen & Chuang,
Exercise 6.11, `T` is the set of the `M` search *solutions*, and `|β⟩` is the equal
superposition over exactly those solutions — the `M`-solution analogue of the single target
`|x⟩`. It generalises `uniformSuperposition d` (`= subsetUniformSuperposition Finset.univ` up to
the empty-check), and its two defining properties drive the exercise:

* **overlap with the full uniform superposition** `|ψ⟩ = N⁻¹ᐟ² ∑_k |k⟩`:
  `⟨β, ψ⟩ = √(M/N)` (real, positive) — the `M`-solution value of the search overlap `α`
  (`= 1/√N` when `M = 1`);
* **support on the solutions**: `⟨x, β⟩ = M⁻¹ᐟ²` for `x ∈ T` and `0` otherwise, so a
  computational-basis measurement of `|β⟩` returns one of the `M` solutions with certainty.

## What is formalised

* `subsetUniformSuperposition T hT` — the pure state `|β⟩ = M⁻¹ᐟ² ∑_{x∈T} |x⟩`.
* `subsetUniformSuperposition_inner_quditBasis` — `⟨x, β⟩ = if x ∈ T then M⁻¹ᐟ² else 0`.
* `subsetUniformSuperposition_inner_uniformSuperposition` — the overlap `⟨β, ψ⟩ = √(M/N)`.
* `bornProb_quditMeasurement_subsetUniformSuperposition` — the Born rule for measuring `|β⟩` in the
  computational basis (`quditMeasurement`, from `Postulates/API/QuditMeasurement`): outcome `x` has
  probability `M⁻¹` for a solution `x ∈ T` and `0` otherwise.

The uniform superposition `uniformSuperposition d` is in `Postulates/API/UniformSuperposition`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **uniform superposition over a subset** `T` of the computational basis of `qudit d`:
`|β⟩ = M⁻¹ᐟ² ∑_{x ∈ T} |x⟩` (`M = |T|`), the equal-amplitude superposition over the basis states
indexed by `T`. It is normalised because the `|x⟩` (`x ∈ T`) are orthonormal, so
`‖∑_{x∈T} |x⟩‖ = √M`, and the prefactor `M⁻¹ᐟ²` cancels it. For Exercise 6.11, `T` is the set of
`M` search solutions and `|β⟩` the state the search evolution rotates `|ψ⟩` onto. -/
def subsetUniformSuperposition (T : Finset (Fin d)) (hT : T.Nonempty) : PureState (qudit d) where
  vec := (Real.sqrt T.card : ℂ)⁻¹ • ∑ x ∈ T, (quditBasis x).vec
  normalized := by
    have hM : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
    change ‖(Real.sqrt T.card : ℂ)⁻¹ • ∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)‖ = 1
    rw [norm_smul]
    have h1 : ‖(Real.sqrt T.card : ℂ)⁻¹‖ = (Real.sqrt T.card)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hcoord : ∀ y : Fin d, (∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)).ofLp y
        = if y ∈ T then 1 else 0 := by
      intro y
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      simp [PiLp.single_apply, Finset.sum_ite_eq]
    have h2 : ‖∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)‖ = Real.sqrt T.card := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      have hnorm : ∀ y : Fin d, ‖(∑ x ∈ T, EuclideanSpace.single x (1 : ℂ)).ofLp y‖ ^ 2
          = if y ∈ T then (1 : ℝ) else 0 := by
        intro y; rw [hcoord]; split <;> simp
      rw [Finset.sum_congr rfl (fun y _ => hnorm y), Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, h2, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hM)]

/-- The underlying vector of `subsetUniformSuperposition T hT` is `M⁻¹ᐟ² ∑_{x∈T} |x⟩`. -/
@[simp]
theorem subsetUniformSuperposition_vec (T : Finset (Fin d)) (hT : T.Nonempty) :
    (subsetUniformSuperposition T hT).vec
      = (Real.sqrt T.card : ℂ)⁻¹ • ∑ x ∈ T, (quditBasis x).vec := rfl

/-- **Amplitude of `|β⟩` on a computational-basis state.** `⟨x, β⟩ = M⁻¹ᐟ²` if `x ∈ T` (a solution)
and `0` otherwise: `|β⟩` is supported exactly on the basis states indexed by `T`. Follows from the
orthonormality of the computational basis, `⟨x, y⟩ = δₓᵧ`. -/
theorem subsetUniformSuperposition_inner_quditBasis (T : Finset (Fin d)) (hT : T.Nonempty)
    (x : Fin d) :
    inner ℂ (quditBasis x).vec (subsetUniformSuperposition T hT).vec
      = if x ∈ T then (Real.sqrt T.card : ℂ)⁻¹ else 0 := by
  rw [subsetUniformSuperposition_vec, inner_smul_right, inner_sum,
    Finset.sum_congr rfl (fun y _ => quditBasis_inner x y),
    Finset.sum_ite_eq T x (fun _ => (1 : ℂ))]
  split <;> simp

/-- **The search overlap `α = ⟨β, ψ⟩ = √(M/N)`** between the solution superposition `|β⟩` and the
full uniform superposition `|ψ⟩ = uniformSuperposition d`. This is the `M`-solution value of the
overlap in Nielsen & Chuang's continuous-time search (`= 1/√N` when `M = 1`); its reality and
positivity are what make the search Hamiltonian `|β⟩⟨β| + |ψ⟩⟨ψ|` rotate `|ψ⟩` onto `|β⟩`
(Exercise 6.11). Computed from `⟨x, ψ⟩ = 1/√N` and `⟨β, ψ⟩ = M⁻¹ᐟ² ∑_{x∈T} ⟨x, ψ⟩ = M·(√M·√N)⁻¹`. -/
theorem subsetUniformSuperposition_inner_uniformSuperposition [NeZero d]
    (T : Finset (Fin d)) (hT : T.Nonempty) :
    inner ℂ (subsetUniformSuperposition T hT).vec (uniformSuperposition d).vec
      = (Real.sqrt (T.card / d) : ℂ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hMpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hM : (0 : ℝ) ≤ T.card := hMpos.le
  -- the real scalar identity `(√M)⁻¹ · (M · (√N)⁻¹) = √(M/N)`
  have key : (Real.sqrt (T.card : ℝ))⁻¹ * ((T.card : ℝ) * (Real.sqrt (d : ℝ))⁻¹)
      = Real.sqrt ((T.card : ℝ) / d) := by
    rw [Real.sqrt_div hM]
    field_simp
    exact (Real.sq_sqrt hM).symm
  rw [subsetUniformSuperposition_vec, inner_smul_left, sum_inner]
  simp only [uniformSuperposition_inner_quditBasis, Finset.sum_const, nsmul_eq_mul, map_inv₀,
    Complex.conj_ofReal]
  rw [← Complex.ofReal_natCast T.card, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
  exact key

/-- **Born rule for measuring `|β⟩` in the computational basis.** The probability of outcome `x`
when the solution superposition `|β⟩ = subsetUniformSuperposition T hT` is measured in the
computational basis (`quditMeasurement`) is `M⁻¹` for a solution `x ∈ T` and `0` for a non-solution:
`|β⟩` collapses to one of its `M` solutions, each equally likely. By the computational-basis Born
rule `bornProb_quditMeasurement_toState` the probability is `‖⟨x, β⟩‖²`, and `⟨x, β⟩ = M⁻¹ᐟ²` for
`x ∈ T` (else `0`, `subsetUniformSuperposition_inner_quditBasis`). -/
theorem bornProb_quditMeasurement_subsetUniformSuperposition (T : Finset (Fin d)) (hT : T.Nonempty)
    (x : Fin d) :
    (quditMeasurement d).bornProb (subsetUniformSuperposition T hT).toState x
      = if x ∈ T then (T.card : ℝ)⁻¹ else 0 := by
  rw [bornProb_quditMeasurement_toState, subsetUniformSuperposition_inner_quditBasis]
  split_ifs with hx
  · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · simp

end AxQM
