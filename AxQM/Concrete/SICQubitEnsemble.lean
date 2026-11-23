/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete data for the tetrahedral (SIC) qubit ensemble (Nielsen & Chuang, Exercise 12.4)

This file collects the matrix-level mathematics behind Nielsen &
Chuang's Exercise 12.4: the four amplitude vectors

* `|X₁⟩ = |0⟩`,
* `|Xₖ₊₁⟩ = √(1/3)·(|0⟩ + √2·ωᵏ·|1⟩)` for `k = 0, 1, 2`, where `ω = e^{2πi/3}`,

together with the algebraic facts needed to show their equal mixture is the maximally mixed state.
The four Bloch vectors form a regular tetrahedron (a symmetric informationally-complete set), so the
average density matrix is `I/2`; the vanishing of the off-diagonal is exactly `1 + ω + ω² = 0`.

The statement in terms of states (`PureState qubit`, the Holevo χ) is in
`AxQM/NC/Ch12/Exercise12_4.lean`, built on `qubitSuperposition_toState_op`
(`AxQM/Postulates/API/QubitSuperpositionMatrix.lean`).

## Main results

* `sicKet` — the four concrete amplitude vectors in `Fin 2 → ℂ`.
* `sicKet_normSq` — each is a unit vector: `‖(sicKet k) 0‖² + ‖(sicKet k) 1‖² = 1`.
* `sicOuterSelf_sum` — the key identity `∑ₖ ¼·|Xₖ⟩⟨Xₖ| = ½·I` at the matrix level.
-/

open Complex Matrix

namespace AxQM.Concrete

/-- The primitive cube root of unity `ω = e^{2πi/3}` used in the SIC amplitudes. -/
noncomputable def sicOmega : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 3)

/-- The defining relation `1 + ω + ω² = 0` for the cube root of unity `ω = e^{2πi/3}` (the sum of
the three cube roots of unity vanishes). This is what makes the SIC average state diagonal. -/
lemma sicOmega_geom : 1 + sicOmega + sicOmega ^ 2 = 0 := by
  have h := (Complex.isPrimitiveRoot_exp 3 (by norm_num)).geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  exact h

/-- The cube root of unity `ω = e^{2πi/3}` lies on the unit circle: `‖ω‖ = 1`. -/
lemma sicOmega_norm : ‖sicOmega‖ = 1 := by
  rw [sicOmega, show (2 * ↑Real.pi * Complex.I / 3) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `ω · conj ω = 1` for the unit-modulus cube root of unity `ω = e^{2πi/3}`. -/
lemma sicOmega_mul_conj : sicOmega * (starRingEnd ℂ) sicOmega = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, sicOmega_norm]; norm_num

/-- The conjugate relation `1 + conj ω + (conj ω)² = 0`, obtained by conjugating `sicOmega_geom`. -/
lemma sicOmega_conj_geom :
    1 + (starRingEnd ℂ) sicOmega + ((starRingEnd ℂ) sicOmega) ^ 2 = 0 := by
  have := congrArg (starRingEnd ℂ) sicOmega_geom
  simpa using this

/-- The four SIC amplitude vectors `|X₁⟩, …, |X₄⟩` of Exercise 12.4, as vectors in `Fin 2 → ℂ`:
`|X₁⟩ = (1, 0)` and `|Xₖ₊₁⟩ = (√(1/3), √(2/3)·ωᵏ)` for `k = 0, 1, 2` with `ω = e^{2πi/3}`. -/
noncomputable def sicKet : Fin 4 → (Fin 2 → ℂ)
  | 0 => ![1, 0]
  | 1 => ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹]
  | 2 => ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega]
  | 3 => ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega ^ 2]

/-- `(1/√3)² = 1/3`, at the complex level. -/
lemma sqrt3_inv_mul_self : (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = (3 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `(√(2/3))² = 2/3`: the squared modulus of the `|1⟩` amplitude of the cone states. -/
lemma sicBeta_sq :
    ((Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹)
      = 2 / 3 := by
  rw [show (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹)
        = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * ((Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹)
      from by ring, sqrt3_inv_mul_self, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Each SIC amplitude vector is a unit vector: `‖(sicKet k) 0‖² + ‖(sicKet k) 1‖² = 1`. -/
lemma sicKet_normSq (k : Fin 4) : ‖sicKet k 0‖ ^ 2 + ‖sicKet k 1‖ ^ 2 = 1 := by
  have h3 : ‖(Real.sqrt 3 : ℂ)⁻¹‖ ^ 2 = 1 / 3 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 3), inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have hβ : ‖(Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹‖ ^ 2 = 2 / 3 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), h3]; norm_num
  have hβω : ‖(Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega‖ ^ 2 = 2 / 3 := by
    rw [norm_mul, mul_pow, sicOmega_norm, one_pow, mul_one, hβ]
  have hβω2 : ‖(Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * sicOmega ^ 2‖ ^ 2 = 2 / 3 := by
    rw [norm_mul, mul_pow, norm_pow, sicOmega_norm, one_pow, one_pow, mul_one, hβ]
  fin_cases k <;>
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp
  · rw [h3, hβ]; norm_num
  · rw [h3, hβω]; norm_num
  · rw [h3, hβω2]; norm_num

/-- **The tetrahedral (SIC) average state is maximally mixed, at the matrix level.**
`∑ₖ ¼·|Xₖ⟩⟨Xₖ| = ½·I`. The diagonal entries are `¼(1 + 3·⅓) = ½` and `¼·3·⅔ = ½`; the
off-diagonal entries vanish because `1 + ω + ω² = 0` (`sicOmega_geom`). -/
lemma sicOuterSelf_sum :
    (∑ k : Fin 4, (4 : ℂ)⁻¹ • Concrete.outerSelf ![sicKet k 0, sicKet k 1])
      = (2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hconj3 : (starRingEnd ℂ) (Real.sqrt 3 : ℂ)⁻¹ = (Real.sqrt 3 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hconj2 : (starRingEnd ℂ) (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := Complex.conj_ofReal _
  have hw2 : sicOmega ^ 2 * ((starRingEnd ℂ) sicOmega) ^ 2 = 1 := by
    rw [← mul_pow, sicOmega_mul_conj, one_pow]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Concrete.outerSelf_apply, smul_eq_mul,
    Matrix.one_apply, Fin.sum_univ_four, sicKet, Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.star_def,
      map_mul, map_pow, hconj3, hconj2, map_one, star_zero, Fin.zero_eta, Fin.mk_one,
      ite_true, mul_zero]
  · linear_combination (3 / 4 : ℂ) * sqrt3_inv_mul_self
  · rw [ite_eq_right (by decide)]
    linear_combination
      (4⁻¹ * (Real.sqrt 2 : ℂ) * ((Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹)) * sicOmega_conj_geom
  · rw [ite_eq_right (by decide)]
    linear_combination
      (4⁻¹ * (Real.sqrt 2 : ℂ) * ((Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹)) * sicOmega_geom
  · linear_combination
      (4⁻¹ * ((Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹)))
          * sicOmega_mul_conj
        + (4⁻¹ * ((Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ *
            ((Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹))) * hw2
        + (3 / 4 : ℂ) * sicBeta_sq

/-- The primitive cube root of unity cubes to one: `ω³ = 1` (`ω = e^{2πi/3}`). -/
lemma sicOmega_pow_three : sicOmega ^ 3 = 1 := by
  have h := (Complex.isPrimitiveRoot_exp 3 (by norm_num)).pow_eq_one
  simpa [sicOmega] using h

/-- For a unit-modulus cube root of unity (`w³ = 1`, `w · conj w = 1`), `conj w = w²`. -/
lemma conj_eq_sq_of_pow_three_eq_one {w : ℂ} (hw3 : w ^ 3 = 1)
    (hmul : w * (starRingEnd ℂ) w = 1) : (starRingEnd ℂ) w = w ^ 2 := by
  calc (starRingEnd ℂ) w = (starRingEnd ℂ) w * w ^ 3 := by rw [hw3, mul_one]
    _ = (w * (starRingEnd ℂ) w) * w ^ 2 := by ring
    _ = w ^ 2 := by rw [hmul, one_mul]

/-- `conj ω = ω²` for the cube root of unity `ω = e^{2πi/3}`: from `ω³ = 1` and `ω · conj ω = 1`. -/
lemma sicOmega_conj_eq_sq : (starRingEnd ℂ) sicOmega = sicOmega ^ 2 :=
  conj_eq_sq_of_pow_three_eq_one sicOmega_pow_three sicOmega_mul_conj

/-- **The `|⅓ + ⅔w|² = ⅓` identity for a primitive cube root of unity `w`** (`1 + w + w² = 0`,
`‖w‖ = 1`, encoded via `w · conj w = 1`). This is the modulus of the off-diagonal SIC overlap:
`⟨Xᵢ|Xⱼ⟩ = ⅓ + ⅔w` with `w ∈ {ω, ω²}` for the two cone states, and its squared modulus is `⅓`
(the SIC condition `|⟨Xᵢ|Xⱼ⟩|² = 1/(d+1) = 1/3` in dimension `d = 2`). The value follows from
`w + conj w = -1` (which `hconj : conj w = -1 - w` encodes), obtained from `w³ = 1` and
`w · conj w = 1`. -/
lemma normSq_third_add (w : ℂ) (hgeom : 1 + w + w ^ 2 = 0)
    (hmul : w * (starRingEnd ℂ) w = 1) :
    Complex.normSq ((3 : ℂ)⁻¹ + (2 / 3) * w) = 1 / 3 := by
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hgeom
  have hconj : (starRingEnd ℂ) w = -1 - w := by
    rw [conj_eq_sq_of_pow_three_eq_one hw3 hmul]; linear_combination hgeom
  have key : ((3 : ℂ)⁻¹ + (2 / 3) * w) * (starRingEnd ℂ) ((3 : ℂ)⁻¹ + (2 / 3) * w) = 1 / 3 := by
    simp only [map_add, map_mul, map_inv₀, map_div₀, map_ofNat, hconj]
    linear_combination (-4 / 9 : ℂ) * hgeom
  have hcast : (Complex.normSq ((3 : ℂ)⁻¹ + (2 / 3) * w) : ℂ) = ((1 / 3 : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, key]; norm_num
  exact_mod_cast hcast

/-- `1 + ω² + (ω²)² = 0`: `ω²` is also a primitive cube root of unity (`ω⁴ = ω` via `ω³ = 1`). -/
lemma sicOmega_sq_geom : 1 + sicOmega ^ 2 + (sicOmega ^ 2) ^ 2 = 0 := by
  linear_combination sicOmega_geom + sicOmega * sicOmega_pow_three

/-- `ω² · conj(ω²) = 1`: `ω²` lies on the unit circle. -/
lemma sicOmega_sq_mul_conj : sicOmega ^ 2 * (starRingEnd ℂ) (sicOmega ^ 2) = 1 := by
  rw [map_pow, ← mul_pow, sicOmega_mul_conj, one_pow]

/-- **The tetrahedral (SIC) states have constant pairwise overlap `|⟨Xᵢ|Xⱼ⟩|² = 1/3`.**
For `i ≠ j`, the squared modulus of the transition amplitude `⟨Xᵢ|Xⱼ⟩ = conj(Xᵢ)₀·(Xⱼ)₀ +
conj(Xᵢ)₁·(Xⱼ)₁` between the amplitude vectors is exactly `1/3` — the symmetric-informationally-
complete condition `|⟨Xᵢ|Xⱼ⟩|² = 1/(d+1) = 1/3` in dimension `d = 2` (the tetrahedron's Bloch
vectors satisfy `rᵢ · rⱼ = -1/3`). Overlaps against `|X₁⟩ = |0⟩` are the real `(√3)⁻¹`; overlaps
among the three cone states are `⅓ + ⅔ω^k` (`normSq_third_add`), with `ω`-powers reduced mod
`ω³ = 1`. -/
lemma sicKet_overlap_normSq_of_ne {i j : Fin 4} (h : i ≠ j) :
    Complex.normSq ((starRingEnd ℂ) (sicKet i 0) * sicKet j 0
        + (starRingEnd ℂ) (sicKet i 1) * sicKet j 1) = 1 / 3 := by
  have hc3 : (starRingEnd ℂ) ((Real.sqrt 3 : ℂ)⁻¹) = (Real.sqrt 3 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hc2 : (starRingEnd ℂ) (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := Complex.conj_ofReal _
  have hA : Complex.normSq ((Real.sqrt 3 : ℂ)⁻¹) = 1 / 3 := by
    rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have hω : Complex.normSq ((3 : ℂ)⁻¹ + (2 / 3) * sicOmega) = 1 / 3 :=
    normSq_third_add sicOmega sicOmega_geom sicOmega_mul_conj
  have hω2 : Complex.normSq ((3 : ℂ)⁻¹ + (2 / 3) * sicOmega ^ 2) = 1 / 3 :=
    normSq_third_add (sicOmega ^ 2) sicOmega_sq_geom sicOmega_sq_mul_conj
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero, one_mul,
      zero_mul, add_zero]; exact hA
  · simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero, one_mul,
      zero_mul, add_zero]; exact hA
  · simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero, one_mul,
      zero_mul, add_zero]; exact hA
  · simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one,
      add_zero, hc3]; exact hA
  · exact absurd rfl h
  · refine (congrArg Complex.normSq ?_).trans hω
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, hc2, hc3]
    linear_combination sqrt3_inv_mul_self + sicOmega * sicBeta_sq
  · refine (congrArg Complex.normSq ?_).trans hω2
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, hc2, hc3]
    linear_combination sqrt3_inv_mul_self + sicOmega ^ 2 * sicBeta_sq
  · simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one,
      add_zero, hc3]; exact hA
  · refine (congrArg Complex.normSq ?_).trans hω2
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, hc2, hc3,
      sicOmega_conj_eq_sq]
    linear_combination sqrt3_inv_mul_self + sicOmega ^ 2 * sicBeta_sq
  · exact absurd rfl h
  · refine (congrArg Complex.normSq ?_).trans hω
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, hc2, hc3,
      sicOmega_conj_eq_sq]
    linear_combination sqrt3_inv_mul_self + sicOmega ^ 4 * sicBeta_sq
      + (2 / 3 * sicOmega) * sicOmega_pow_three
  · simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one,
      add_zero, hc3]; exact hA
  · refine (congrArg Complex.normSq ?_).trans hω
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_pow, hc2, hc3,
      sicOmega_conj_eq_sq]
    linear_combination sqrt3_inv_mul_self + sicOmega ^ 4 * sicBeta_sq
      + (2 / 3 * sicOmega) * sicOmega_pow_three
  · refine (congrArg Complex.normSq ?_).trans hω2
    simp only [sicKet, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_pow, hc2, hc3,
      sicOmega_conj_eq_sq]
    linear_combination sqrt3_inv_mul_self + sicOmega ^ 5 * sicBeta_sq
      + (2 / 3 * sicOmega ^ 2) * sicOmega_pow_three
  · exact absurd rfl h

/-! ### The SIC tight-frame (2-design) collision inequality

The remaining results are the ensemble-specific input to the **strict** accessible-information cap
of Exercise 12.4 (`max_m H(X : Y) < 1` bit). For any POVM element `E` (a positive-semidefinite
operator), the four transition probabilities `⟨Xₓ|E|Xₓ⟩` have a *bounded collision sum*:

`∑ₓ ⟨Xₓ|E|Xₓ⟩² ≤ (4/3)·(tr E)²`,

the qubit SIC/tetrahedron tight-frame second-moment bound. This is what forces every measurement
outcome to have conditional collision probability `≤ 1/3` (hence conditional entropy `≥ log 3`), and
the inequality reduces **exactly** to positive-semidefiniteness of `E` (its off-diagonal Cauchy–
Schwarz bound `|E₀₁|² ≤ E₀₀·E₁₁`). -/

/-- `‖ω‖² = 1` as a `Complex.normSq`, for the SIC cube root of unity `ω = e^{2πi/3}`. -/
lemma sicOmega_normSq : Complex.normSq sicOmega = 1 := by
  rw [Complex.normSq_eq_norm_sq, sicOmega_norm]; norm_num

/-- The three phases `ωᵏ` (`k = 0, 1, 2`) sum to zero when tilted by any `c`: `∑ₖ Re(ωᵏ c) = 0`.
This is `1 + ω + ω² = 0` read on real parts, and kills the linear-in-`Re(c)` cross terms in the
collision sum. -/
lemma sicOmega_re_sum (c : ℂ) :
    c.re + (sicOmega * c).re + (sicOmega ^ 2 * c).re = 0 := by
  rw [← Complex.add_re, ← Complex.add_re,
    show c + sicOmega * c + sicOmega ^ 2 * c = (1 + sicOmega + sicOmega ^ 2) * c by ring,
    sicOmega_geom, zero_mul, Complex.zero_re]

/-- The squared real parts of the tilted phases sum to `(3/2)‖c‖²`: `∑ₖ Re(ωᵏ c)² = (3/2)·normSq c`.
Proved via `Re(z)² = (Re(z²) + normSq z)/2`, using `∑ₖ ω²ᵏ = 1 + ω² + ω⁴ = 0` (`ω⁴ = ω`) and
`‖ωᵏ‖ = 1`. This is the second-moment identity of the tetrahedral tight frame. -/
lemma sicOmega_re_sq_sum (c : ℂ) :
    c.re ^ 2 + (sicOmega * c).re ^ 2 + (sicOmega ^ 2 * c).re ^ 2 = 3 / 2 * Complex.normSq c := by
  have hsq : ∀ z : ℂ, z.re ^ 2 = ((z ^ 2).re + Complex.normSq z) / 2 := by
    intro z
    have h : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two z, Complex.mul_re]; ring
    rw [h, Complex.normSq_apply]; ring
  have hω4 : sicOmega ^ 4 = sicOmega := by
    rw [show (4 : ℕ) = 3 + 1 by rfl, pow_add, sicOmega_pow_three, one_mul, pow_one]
  have hsum2 : (c ^ 2).re + ((sicOmega * c) ^ 2).re + ((sicOmega ^ 2 * c) ^ 2).re = 0 := by
    rw [← Complex.add_re, ← Complex.add_re,
      show c ^ 2 + (sicOmega * c) ^ 2 + (sicOmega ^ 2 * c) ^ 2
        = (1 + sicOmega ^ 2 + sicOmega ^ 4) * c ^ 2 by ring, hω4,
      show (1 : ℂ) + sicOmega ^ 2 + sicOmega = 0 by linear_combination sicOmega_geom,
      zero_mul, Complex.zero_re]
  have hns : Complex.normSq c + Complex.normSq (sicOmega * c) + Complex.normSq (sicOmega ^ 2 * c)
      = 3 * Complex.normSq c := by
    rw [Complex.normSq_mul, Complex.normSq_mul, sicOmega_normSq,
      show Complex.normSq (sicOmega ^ 2) = 1 by rw [sq, Complex.normSq_mul, sicOmega_normSq]; ring]
    ring
  rw [hsq c, hsq (sicOmega * c), hsq (sicOmega ^ 2 * c)]; linarith [hsum2, hns]

/-- **The quadratic form `⟨v|E|v⟩` against a "cone" SIC amplitude vector**, in closed form. For a
Hermitian matrix `E` (`E₁₀ = conj E₀₁`) and a unit-modulus phase `W` (`W·conj W = 1`), the vector
`v = (1/√3, √(2/3)·W)` gives
`⟨v|E|v⟩ = E₀₀/3 + 2E₁₁/3 + (√2/3)(W E₀₁ + conj(W E₀₁))`.
The three cone states `|X₂⟩, |X₃⟩, |X₄⟩` are the cases `W = 1, ω, ω²`. -/
lemma sicKet_cone_quadForm (E : Matrix (Fin 2) (Fin 2) ℂ)
    (h10 : E 1 0 = (starRingEnd ℂ) (E 0 1)) (W : ℂ) (hW : W * (starRingEnd ℂ) W = 1) :
    (star ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * W] ⬝ᵥ
        E.mulVec ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * W])
      = E 0 0 / 3 + 2 * E 1 1 / 3
        + (Real.sqrt 2 : ℂ) / 3 * (W * E 0 1 + (starRingEnd ℂ) (W * E 0 1)) := by
  have h3 : ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = (3 : ℂ)⁻¹ := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hc3 : (starRingEnd ℂ) ((Real.sqrt 3 : ℂ)⁻¹) = (Real.sqrt 3 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hc2 : (starRingEnd ℂ) (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := Complex.conj_ofReal _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.star_apply, RCLike.star_def, map_mul, hc3, hc2, h10]
  linear_combination
    (E 0 0 + (Real.sqrt 2 : ℂ) * W * E 0 1
      + (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) W * (starRingEnd ℂ) (E 0 1)
      + E 1 1 * (Real.sqrt 2 : ℂ) ^ 2 * (W * (starRingEnd ℂ) W)) * h3
    + (E 1 1 * (W * (starRingEnd ℂ) W) / 3) * h2
    + (E 1 1 * 2 / 3) * hW

open scoped ComplexOrder in
/-- **The tetrahedral (SIC) tight-frame collision inequality.** For a positive-semidefinite `2×2`
matrix `E` (a qubit POVM element `E = M†M`), the four transition probabilities `⟨Xₓ|E|Xₓ⟩ =
star Xₓ ⬝ᵥ E.mulVec Xₓ` (real, as `E` is Hermitian) satisfy the collision bound

`∑ₓ ⟨Xₓ|E|Xₓ⟩² ≤ (4/3)·(tr E)²`.

This is the SIC/2-design second-moment property of the tetrahedral qubit ensemble: writing
`E = [[a, c], [c̄, b]]`, the sum equals `a² + (a+2b)²/3 + (4/3)|c|²`, and the bound reduces
**exactly** to the positive-semidefinite off-diagonal condition `|c|² ≤ a·b`. It is the
ensemble-specific input to Exercise 12.4's strict accessible-information cap: it forces every
outcome to have conditional collision probability `≤ 1/3` (`= 1/(d+1)`, `d = 2`), hence entropy
`≥ log 3`, hence mutual information `≤ log 4 − log 3 = log(4/3) < log 2`. Equality holds iff `E` is
rank one (`|c|² = a·b`), i.e. the achieving POVM is projective. -/
theorem sicKet_quadForm_re_sq_sum_le (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef) :
    ∑ x, (star (sicKet x) ⬝ᵥ E.mulVec (sicKet x)).re ^ 2 ≤ 4 / 3 * (E.trace).re ^ 2 := by
  -- Hermitian/positivity facts about the entries of `E`.
  have h10 : E 1 0 = (starRingEnd ℂ) (E 0 1) := by
    rw [← hE.1.apply 0 1]; exact (star_star _).symm
  have e00 : (E 0 0).im = 0 := by
    have := congrArg Complex.im (hE.1.apply 0 0); simp [Complex.conj_im] at this; linarith
  have e11 : (E 1 1).im = 0 := by
    have := congrArg Complex.im (hE.1.apply 1 1); simp [Complex.conj_im] at this; linarith
  -- Positive-semidefiniteness gives the off-diagonal Cauchy–Schwarz bound `|c|² ≤ a·b`.
  have hbound : Complex.normSq (E 0 1) ≤ (E 0 0).re * (E 1 1).re := by
    have hdet : (0 : ℂ) ≤ E.det := hE.det_nonneg
    rw [Matrix.det_fin_two, Complex.le_def] at hdet
    have hre := hdet.1
    simp only [Complex.zero_re, Complex.sub_re, Complex.mul_re, h10, Complex.conj_re,
      Complex.conj_im, e00, e11] at hre
    rw [Complex.normSq_apply]; nlinarith [hre]
  have htr : (E.trace).re = (E 0 0).re + (E 1 1).re := by
    rw [Matrix.trace_fin_two, Complex.add_re]
  -- `.re` of the closed-form cone quadratic form.
  have cone_re : ∀ W : ℂ, W * (starRingEnd ℂ) W = 1 →
      (star ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * W] ⬝ᵥ
          E.mulVec ![(Real.sqrt 3 : ℂ)⁻¹, (Real.sqrt 2 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ * W]).re
        = (E 0 0).re / 3 + 2 * (E 1 1).re / 3 + 2 * Real.sqrt 2 / 3 * (W * E 0 1).re := by
    intro W hW
    rw [sicKet_cone_quadForm E h10 W hW, Complex.add_conj]
    simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_im, Complex.mul_im, e00, e11, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat]
    ring
  -- Evaluate the four quadratic forms.
  have hz0 : (star (sicKet 0) ⬝ᵥ E.mulVec (sicKet 0)).re = (E 0 0).re := by
    simp [sicKet, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hz1 : (star (sicKet 1) ⬝ᵥ E.mulVec (sicKet 1)).re
      = (E 0 0).re / 3 + 2 * (E 1 1).re / 3 + 2 * Real.sqrt 2 / 3 * (E 0 1).re := by
    have := cone_re 1 (by simp); simpa [sicKet, one_mul] using this
  have hz2 : (star (sicKet 2) ⬝ᵥ E.mulVec (sicKet 2)).re
      = (E 0 0).re / 3 + 2 * (E 1 1).re / 3 + 2 * Real.sqrt 2 / 3 * (sicOmega * E 0 1).re :=
    cone_re sicOmega sicOmega_mul_conj
  have hz3 : (star (sicKet 3) ⬝ᵥ E.mulVec (sicKet 3)).re
      = (E 0 0).re / 3 + 2 * (E 1 1).re / 3 + 2 * Real.sqrt 2 / 3 * (sicOmega ^ 2 * E 0 1).re :=
    cone_re (sicOmega ^ 2) sicOmega_sq_mul_conj
  -- Assemble: the sum of squares plus the ω-frame identities give the tight-frame bound.
  rw [Fin.sum_univ_four, hz0, hz1, hz2, hz3, htr]
  have hr : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 := sicOmega_re_sum (E 0 1)
  have h2s := sicOmega_re_sq_sum (E 0 1)
  set a := (E 0 0).re
  set b := (E 1 1).re
  set r := Real.sqrt 2
  set s0 := (E 0 1).re
  set s1 := (sicOmega * E 0 1).re
  set s2 := (sicOmega ^ 2 * E 0 1).re
  have key : a ^ 2 + (a / 3 + 2 * b / 3 + 2 * r / 3 * s0) ^ 2
      + (a / 3 + 2 * b / 3 + 2 * r / 3 * s1) ^ 2 + (a / 3 + 2 * b / 3 + 2 * r / 3 * s2) ^ 2
      = a ^ 2 + (a + 2 * b) ^ 2 / 3 + 4 / 3 * Complex.normSq (E 0 1) := by
    linear_combination (4 * r * (a / 3 + 2 * b / 3) / 3) * h0 + (4 * r ^ 2 / 9) * h2s
      + (2 * Complex.normSq (E 0 1) / 3) * hr
  rw [key]; nlinarith [hbound]

/-! ### Born-probability bridge helpers

Two small `Matrix`-level lemmas that turn the Born probability of a `2×2` POVM element `E` on a SIC
state — which passes to the trace `Tr(E·|Xₓ⟩⟨Xₓ|)` — into the concrete quadratic form
`⟨Xₓ|E|Xₓ⟩ = star Xₓ ⬝ᵥ E.mulVec Xₓ` of `sicKet_quadForm_re_sq_sum_le`, and record that the four
quadratic forms sum to `2·Tr E` (the tetrahedral resolution `∑ₓ|Xₓ⟩⟨Xₓ| = 2·I`). -/

/-- Eta for the SIC amplitude vectors: `![Xₓ,₀, Xₓ,₁] = Xₓ` as functions `Fin 2 → ℂ`. Reconciles the
`![·, ·]` form produced by `qubitSuperposition_toState_op` with the `sicKet x` used throughout. -/
lemma sicKet_eta (x : Fin 4) : ![sicKet x 0, sicKet x 1] = sicKet x := by
  funext i; fin_cases i <;> rfl

/-- **Trace–quadratic-form bridge.** For a `2×2` matrix `A` and a vector `v : Fin 2 → ℂ`, the trace
of `A·|v⟩⟨v|` is the quadratic form `⟨v|A|v⟩ = star v ⬝ᵥ A.mulVec v`, i.e. `Tr(A·|v⟩⟨v|) = ⟨v|A|v⟩`.
The rank-one/outer-product identity `Tr(A P_v) = ⟨v|A|v⟩` at the matrix level. -/
lemma trace_mul_outerSelf (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    (A * outerSelf v).trace = star v ⬝ᵥ A.mulVec v := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, outerSelf_apply, Fin.sum_univ_two,
    dotProduct, Matrix.mulVec, Pi.star_apply]
  ring

/-- **The four SIC quadratic forms sum to `2·Tr E`.** For any `2×2` matrix `E`,
`∑ₓ ⟨Xₓ|E|Xₓ⟩ = 2·Tr E`, because the tetrahedral projectors resolve the identity as
`∑ₓ|Xₓ⟩⟨Xₓ| = 2·I` (`sicOuterSelf_sum`). This pins the `∑ₓ Tr(E ρₓ)` normalisation used to turn the
collision bound `∑ₓ⟨Xₓ|E|Xₓ⟩² ≤ 4/3·(Tr E)²` into a bound in terms of the total weight
`∑ₓ⟨Xₓ|E|Xₓ⟩`. -/
lemma sicKet_quadForm_sum_eq_trace (E : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ x, star (sicKet x) ⬝ᵥ E.mulVec (sicKet x) = 2 * E.trace := by
  have hO : ∑ x, outerSelf (sicKet x) = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h := sicOuterSelf_sum
    simp only [sicKet_eta] at h
    have h4 := congrArg (fun A => (4 : ℂ) • A) h
    simp only [Finset.smul_sum, smul_smul] at h4
    norm_num at h4
    exact h4
  calc ∑ x, star (sicKet x) ⬝ᵥ E.mulVec (sicKet x)
      = ∑ x, (E * outerSelf (sicKet x)).trace := by simp_rw [trace_mul_outerSelf]
    _ = (E * ∑ x, outerSelf (sicKet x)).trace := by rw [Finset.mul_sum, Matrix.trace_sum]
    _ = (E * ((2 : ℂ) • 1)).trace := by rw [hO]
    _ = 2 * E.trace := by rw [Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul]

end AxQM.Concrete
