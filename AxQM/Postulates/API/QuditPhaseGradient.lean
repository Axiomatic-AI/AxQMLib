/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.InverseQuantumFourierTransform
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.API.UniformSuperposition
import ToMathlib.Analysis.InnerProductSpace.InvolutionRotation
import ToMathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Algebra.Order.Round

/-!
# AxQM.Postulates.API — the qudit phase-gradient state

The **phase-gradient state** `|φ_θ⟩ = (1/√d) ∑ₖ e^{iθk} |k⟩` of the register `qudit d`: the equal
superposition of all computational-basis states, with the `k`-th amplitude carrying the linear phase
`e^{iθk}`. It is the state a phase-estimation register holds after the controlled-power stage has
loaded a per-value linear phase gradient with slope `θ`, and the object the final inverse QFT
then reads out (N&C §5.2, Figure 5.2).

This generalizes the Fourier image state `qftFourierImage d j = (1/√d) ∑ₖ e^{2πijk/d} |k⟩` from the
**dyadic/rational** slopes `θ = 2πj/d` (an integer `j`, so `θ` is a multiple of `2π/d`) to an
**arbitrary real** slope `θ`. That generality is exactly what Kitaev's QFT-over-`Z_p` circuit
(Problem 5.1) needs: phase estimation of the cyclic shift produces the gradient with slope
`θ = 2πℓ/p`, whose frequency `ℓ/p` is *not* of the form `m/d` for the `d = 2^{n+1}`-level control
register when `p` is prime — so the read-out is inherently a finite-precision *estimate*, and the
state at hand is a genuine `quditPhaseGrad θ d`, not any `qftFourierImage d m`.

## What is formalised

* `quditPhaseGrad θ d` — the state `(1/√d) ∑ₖ e^{iθk} |k⟩` as a `PureState (qudit d)`. It is
  normalized for **every** real `θ` (each amplitude has modulus `1/√d` and the `|k⟩` are
  orthonormal, so `‖φ_θ‖² = d·(1/√d)² = 1`), via `Orthonormal.norm_sum_smul_sq` — the same idiom as
  `qftInverseFourierImage` / `orderEigenstate`.
* `quditPhaseGrad_vec` — its underlying vector, the explicit superposition.
* `quditPhaseGrad_eq_qftFourierImage` — the **dyadic specialization** identifying the forward
  Fourier image as the phase gradient of slope `2πj/d`:
  `qftFourierImage d j = quditPhaseGrad (2πj/d) d`.
* `quditPhaseGrad_eq_qftInverseFourierImage` — the inverse-image counterpart at slope `−2πk/d`:
  `qftInverseFourierImage d k = quditPhaseGrad (−2πk/d) d`.
* `quditPhaseGrad_inner_quditPhaseGrad` — the **overlap** `⟨φ_α | φ_β⟩ = (1/d) ∑ₖ e^{i(β−α)k}` of
  two phase gradients: the normalized geometric sum of the slope difference.
* `quditPhaseGrad_qftInverse_inner_quditBasis` — the **phase-estimation read-out amplitude** (N&C
  §5.2.1, eqs. 5.23–5.24): the amplitude of computational-basis outcome `|m⟩` after the terminal
  inverse QFT of the gradient is `⟨m | F⁻¹ | φ_θ⟩ = (1/d) ∑ₖ e^{i(θ − 2πm/d)k}` (N&C's `αₗ`).
* `quditPhaseGrad_qftInverse_inner_quditBasis_geom` — its **closed form** (N&C eqs. 5.25–5.26):
  `(1/d)·(e^{iθd} − 1)/(e^{i(θ − 2πm/d)} − 1)` when the ratio `≠ 1`, numerator bin-independent.
  These two read-out amplitudes are the foundation of the finite-precision accuracy of the prime-`p`
  Kitaev circuit (Problem 5.1): since `ℓ/p` is non-dyadic the read-out never collapses to a single
  bin, and the modulus of `αₗ` — bounded via the closed form (eqs. 5.28–5.34) — is what quantifies
  how sharply the estimate concentrates.

## Design notes

* **Why a named definition (not an inline `qftFourierImage`).** The Kitaev-circuit
  read-out needs the *general-slope* state, and its phase modulus argument (unit for any real `θ`)
  is what makes it normalized without a background unitary — so it earns its own definition rather
  than being a special case of `qftFourierImage`, whose slope is pinned to a rational multiple of
  `2π`.
-/

noncomputable section

namespace AxQM

open scoped Matrix

/-- The linear phase `e^{iθk}` (real slope `θ`, `k : ℕ`) has unit modulus: it is `e^{iφ}` for the
real angle `φ = θk`. -/
private theorem norm_exp_phaseGrad (θ : ℝ) (k : ℕ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I * (k : ℕ))‖ = 1 := by
  simp [Complex.norm_exp]

/-- The **qudit phase-gradient state** `|φ_θ⟩ = (1/√d) ∑ₖ e^{iθk} |k⟩` of `qudit d`: the equal
superposition of the computational basis with the `k`-th amplitude carrying the linear phase
`e^{iθk}` (slope `θ : ℝ`). Normalized for every real `θ`, because each amplitude has modulus
`1/√d` and the basis states `|k⟩ = quditBasis k` are orthonormal, so `‖φ_θ‖² = d·(1/d) = 1`
(`Orthonormal.norm_sum_smul_sq`). The general-slope generalization of `qftFourierImage` (slope
`2πj/d`); the state a phase-estimation register carries into the terminal inverse-QFT read-out. -/
def quditPhaseGrad (θ : ℝ) (d : ℕ) [NeZero d] : PureState (qudit d) where
  vec := ∑ k : Fin d,
    ((Real.sqrt d : ℂ)⁻¹ * Complex.exp ((θ : ℂ) * Complex.I * (k : ℕ))) • (quditBasis k).vec
  normalized := by
    have horth : Orthonormal ℂ (fun k : Fin d => (quditBasis k).vec) := quditBasis_orthonormal d
    have hcoeff : ∀ k : Fin d,
        ‖(Real.sqrt d : ℂ)⁻¹ * Complex.exp ((θ : ℂ) * Complex.I * (k : ℕ))‖ ^ 2 = (d : ℝ)⁻¹ :=
      fun k => by
        rw [norm_mul, norm_exp_phaseGrad, mul_one, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
    have hsq : ‖(∑ k : Fin d,
        ((Real.sqrt d : ℂ)⁻¹ * Complex.exp ((θ : ℂ) * Complex.I * (k : ℕ)))
          • (quditBasis k).vec)‖ ^ 2 = 1 := by
      rw [horth.norm_sum_smul_sq, Finset.sum_congr rfl (fun k _ => hcoeff k)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_inv_cancel₀ (by exact_mod_cast (NeZero.ne d))]
    rw [← Real.sqrt_one, ← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- The underlying vector of `quditPhaseGrad θ d` is the explicit phase-gradient superposition
`(1/√d) ∑ₖ e^{iθk} |k⟩`. -/
@[simp]
theorem quditPhaseGrad_vec (θ : ℝ) (d : ℕ) [NeZero d] :
    (quditPhaseGrad θ d).vec
      = ∑ k : Fin d,
        ((Real.sqrt d : ℂ)⁻¹ * Complex.exp ((θ : ℂ) * Complex.I * (k : ℕ))) • (quditBasis k).vec :=
  rfl

/-- **Amplitude extraction:** the `j`-th coefficient of the phase gradient is `(1/√d)·e^{iθj}`,
`⟨j|φ_θ⟩ = (1/√d)·e^{iθj}` — the inner product of a computational-basis state with `quditPhaseGrad`
reads off its amplitude, since the `|k⟩` are orthonormal. The datum a phase-estimation read-out
(inverse QFT) processes wire by wire. -/
theorem quditPhaseGrad_inner_quditBasis (θ : ℝ) (d : ℕ) [NeZero d] (j : Fin d) :
    inner ℂ (quditBasis j).vec (quditPhaseGrad θ d).vec
      = (Real.sqrt d : ℂ)⁻¹ * Complex.exp ((θ : ℂ) * Complex.I * (j : ℕ)) := by
  simp only [quditPhaseGrad_vec, inner_sum, inner_smul_right, quditBasis_inner, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **At zero slope the phase gradient is the uniform superposition:**
`quditPhaseGrad 0 d = uniformSuperposition d`. With `θ = 0` every linear phase `e^{iθk}` is `1`, so
each amplitude collapses to `1/√d` — the equal superposition `(1/√d) ∑ₖ |k⟩`. -/
theorem quditPhaseGrad_zero (d : ℕ) [NeZero d] :
    quditPhaseGrad 0 d = uniformSuperposition d := by
  apply PureState.ext
  rw [quditPhaseGrad_vec, uniformSuperposition_vec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_zero, zero_mul, zero_mul, Complex.exp_zero, mul_one]

/-- **The forward Fourier image is the phase gradient of slope `2πj/d`.** The QFT image state
`qftFourierImage d j = (1/√d) ∑ₖ e^{2πijk/d} |k⟩` (N&C eq. 5.2/5.79) is exactly `quditPhaseGrad` at
the rational slope `θ = 2πj/d`: `qftFourierImage d j = quditPhaseGrad (2πj/d) d`. This is the sense
in which `quditPhaseGrad` generalizes the Fourier image — the linear phase `e^{2πijk/d}` is
`e^{iθk}` for `θ = 2πj/d`. -/
theorem quditPhaseGrad_eq_qftFourierImage (d : ℕ) [NeZero d] (j : Fin d) :
    qftFourierImage d j = quditPhaseGrad (2 * Real.pi * (j : ℕ) / d) d := by
  apply PureState.ext
  rw [qftFourierImage_vec, quditPhaseGrad_vec]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3; push_cast; ring

/-- **The inverse Fourier image is the phase gradient of slope `−2πk/d`.** The inverse-QFT image
`qftInverseFourierImage d k = (1/√d) ∑ⱼ e^{−2πijk/d} |j⟩` (N&C Exercise 5.5) is `quditPhaseGrad` at
the rational slope `θ = −2πk/d`: `qftInverseFourierImage d k = quditPhaseGrad (−2πk/d) d`. The
eigenstates of the cyclic shift `periodShift p y` are inverse Fourier images, so this reads them as
phase gradients of the register. -/
theorem quditPhaseGrad_eq_qftInverseFourierImage (d : ℕ) [NeZero d] (k : Fin d) :
    qftInverseFourierImage d k = quditPhaseGrad (-(2 * Real.pi * (k : ℕ)) / d) d := by
  apply PureState.ext
  rw [qftInverseFourierImage_vec, quditPhaseGrad_vec]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 3; push_cast; ring

/-- **Overlap of two phase gradients.** For real slopes `α, β`, the inner product of the
phase-gradient states is the normalized geometric sum of the slope difference:
`⟨φ_α | φ_β⟩ = (1/d) ∑ₖ e^{i(β−α)k}`. The two `1/√d` normalizations combine to `1/d`, and
orthonormality of the computational basis collapses the double sum to its diagonal, where the
conjugate phase `e^{−iαk}` (from the antilinear first slot) meets `e^{iβk}`. This is the algebraic
heart of the phase-estimation read-out amplitude below. -/
theorem quditPhaseGrad_inner_quditPhaseGrad (α β : ℝ) (d : ℕ) [NeZero d] :
    inner ℂ (quditPhaseGrad α d).vec (quditPhaseGrad β d).vec
      = (d : ℂ)⁻¹ * ∑ k : Fin d, Complex.exp (((β - α : ℝ) : ℂ) * Complex.I * (k : ℕ)) := by
  conv_lhs => rw [quditPhaseGrad_vec]
  rw [sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_left, quditPhaseGrad_inner_quditBasis]
  have hd : ((Real.sqrt d : ℂ))⁻¹ * (Real.sqrt d : ℂ)⁻¹ = (d : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity),
      Complex.ofReal_natCast]
  have hconj : (starRingEnd ℂ) ((Real.sqrt d : ℂ)⁻¹ * Complex.exp ((α : ℂ) * Complex.I * (k : ℕ)))
      = (Real.sqrt d : ℂ)⁻¹ * Complex.exp (-((α : ℂ) * Complex.I * (k : ℕ))) := by
    rw [map_mul, map_inv₀, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  rw [hconj, mul_mul_mul_comm, hd, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The phase-estimation read-out amplitude** (N&C §5.2.1, eqs. 5.23–5.24). When the terminal
inverse QFT of phase estimation acts on the phase gradient `|φ_θ⟩` of slope `θ`, the amplitude of
the computational-basis outcome `|m⟩` is the normalized geometric sum
`⟨m | F⁻¹ | φ_θ⟩ = (1/d) ∑ₖ e^{i(θ − 2πm/d)k}` — N&C's coefficient `αₗ` (eq. 5.24) with `θ = 2πϕ`,
`d = 2ᵗ` and `m = b + l`. The slope offset `2πm/d` is the phase of the bin `|m⟩`, so the summand is
the *residual* phase `e^{i(θ − 2πm/d)k}`: `|αₘ|²` peaks at the bin `m/d` closest to the frequency
`θ/(2π)`.

Proof: the inverse evolution is the adjoint of the QFT (`qftInverseEvolution = (qftEvolution d)†`),
so the adjoint moves across the inner product to give `⟨F|m⟩ | φ_θ⟩`; and `F|m⟩` is itself the phase
gradient of the dyadic slope `2πm/d` (`quditPhaseGrad_eq_qftFourierImage`), reducing the amplitude
to the phase-gradient overlap `quditPhaseGrad_inner_quditPhaseGrad` at `α = 2πm/d`, `β = θ`. -/
theorem quditPhaseGrad_qftInverse_inner_quditBasis (θ : ℝ) (d : ℕ) [NeZero d] (m : Fin d) :
    inner ℂ (quditBasis m).vec ((qftInverseEvolution d).evolvePure (quditPhaseGrad θ d)).vec
      = (d : ℂ)⁻¹ * ∑ k : Fin d,
          Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I * (k : ℕ)) := by
  rw [Evolution.evolvePure_vec, qftInverseEvolution, Evolution.adjoint_op,
    ContinuousLinearMap.adjoint_inner_right, ← Evolution.evolvePure_vec,
    qftEvolution_evolvePure_quditBasis, quditPhaseGrad_eq_qftFourierImage,
    quditPhaseGrad_inner_quditPhaseGrad]

/-- **The read-out amplitude in closed form** (N&C §5.2.1, eqs. 5.25–5.26). Summing the geometric
series of `quditPhaseGrad_qftInverse_inner_quditBasis`, the amplitude on bin `|m⟩` is
`⟨m | F⁻¹ | φ_θ⟩ = (1/d)·(e^{iθd} − 1)/(e^{i(θ − 2πm/d)} − 1)`, valid whenever the ratio
`e^{i(θ − 2πm/d)} ≠ 1` (i.e. `θ − 2πm/d` is not a multiple of `2π`, so the geometric series is not
constant). This is N&C's eq. (5.25)/(5.26): the numerator `e^{iθd} − 1` is **bin-independent** — the
`2πm` phase of the bin drops out because `m` is an integer (`e^{−2πim} = 1`) — which is exactly what
makes `|numerator| ≤ 2` uniformly, the first step of the accuracy bound (eqs. 5.28–5.34).

Proof: convert `∑ₖ e^{i(θ−2πm/d)k}` to `∑ₖ rᵏ` with `r = e^{i(θ−2πm/d)}`
(`Complex.exp_natCast_mul`), sum it with `geom_sum_eq` (`r ≠ 1`), then simplify `rᵈ = e^{iθd}` by
absorbing the integer multiple `e^{−2πim} = 1` (`Complex.exp_int_mul_two_pi_mul_I`). -/
theorem quditPhaseGrad_qftInverse_inner_quditBasis_geom (θ : ℝ) (d : ℕ) [NeZero d] (m : Fin d)
    (hne : Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) ≠ 1) :
    inner ℂ (quditBasis m).vec ((qftInverseEvolution d).evolvePure (quditPhaseGrad θ d)).vec
      = (d : ℂ)⁻¹ * (Complex.exp (((θ * d : ℝ) : ℂ) * Complex.I) - 1)
          / (Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) - 1) := by
  rw [quditPhaseGrad_qftInverse_inner_quditBasis]
  set φ : ℝ := θ - 2 * Real.pi * (m : ℕ) / d with hφ
  have hr : ∀ k : Fin d, Complex.exp ((φ : ℂ) * Complex.I * (k : ℕ))
      = Complex.exp ((φ : ℂ) * Complex.I) ^ (k : ℕ) := fun k => by
    rw [← Complex.exp_natCast_mul]; congr 1; ring
  have hsum : ∑ k : Fin d, Complex.exp ((φ : ℂ) * Complex.I * (k : ℕ))
      = (Complex.exp ((φ : ℂ) * Complex.I) ^ d - 1) / (Complex.exp ((φ : ℂ) * Complex.I) - 1) := by
    rw [Finset.sum_congr rfl (fun k _ => hr k),
      Fin.sum_univ_eq_sum_range (fun k => Complex.exp ((φ : ℂ) * Complex.I) ^ k) d,
      geom_sum_eq hne]
  have hpow : Complex.exp ((φ : ℂ) * Complex.I) ^ d
      = Complex.exp (((θ * d : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_natCast_mul]
    have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    have key : (d : ℂ) * ((φ : ℂ) * Complex.I)
        = ((θ * d : ℝ) : ℂ) * Complex.I + ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hφ]; push_cast; field_simp; ring
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hsum, hpow]
  ring

/-- **The modulus of the phase-estimation read-out amplitude, in closed form.** Taking the modulus
of the geometric closed form (`quditPhaseGrad_qftInverse_inner_quditBasis_geom`), the amplitude of
the computational outcome `|m⟩` after the terminal inverse QFT of the gradient `|φ_θ⟩` has modulus
`‖⟨m | F⁻¹ | φ_θ⟩‖ = (1/d)·‖e^{iθd} − 1‖ / ‖e^{iψ} − 1‖`, with `ψ = θ − 2πm/d` the residual phase of
the bin `|m⟩` (valid whenever `e^{iψ} ≠ 1`). The numerator `e^{iθd} − 1` is bin-independent; the
two chord lengths `‖e^{iθd} − 1‖` and `‖e^{iψ} − 1‖` are exactly the geometric quantities Nielsen &
Chuang bound in §5.2.1 (eqs. 5.28–5.29) to control how sharply `|αₘ|²` concentrates on the bin
nearest the frequency `θ/(2π)`. -/
theorem quditPhaseGrad_qftInverse_norm_inner_quditBasis (θ : ℝ) (d : ℕ) [NeZero d] (m : Fin d)
    (hne : Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) ≠ 1) :
    ‖inner ℂ (quditBasis m).vec ((qftInverseEvolution d).evolvePure (quditPhaseGrad θ d)).vec‖
      = (d : ℝ)⁻¹ * ‖Complex.exp (((θ * d : ℝ) : ℂ) * Complex.I) - 1‖
          / ‖Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) - 1‖ := by
  rw [quditPhaseGrad_qftInverse_inner_quditBasis_geom θ d m hne, norm_div, norm_mul, norm_inv,
    Complex.norm_natCast]

/-- **Nearest-bin concentration of phase estimation** — the read-out success amplitude. If the bin
`|m⟩` lies within half a bin-width of the frequency, i.e. its residual phase `ψ = θ − 2πm/d`
satisfies `|ψ| ≤ π/d`, then the read-out amplitude has modulus at least `2/π`:
`2/π ≤ ‖⟨m | F⁻¹ | φ_θ⟩‖`. Hence phase estimation places at least `(2/π)² = 4/π²` of the probability
on the bin nearest the frequency (`quditPhaseGrad_qftInverse_norm_inner_quditBasis_sq_ge`): the
sense in which the terminal inverse QFT reads out a good estimate even when `θ/(2π)` is not a dyadic
`m/d`.

Proof: when `ψ = 0` the amplitude is exactly `1 ≥ 2/π`. Otherwise, through the closed-form modulus,
the numerator `‖e^{iθd} − 1‖ = ‖e^{iψd} − 1‖ ≥ (2/π)|ψd|` (the reverse chord bound
`Complex.two_div_pi_mul_abs_le_norm_one_sub_exp_ofReal_mul_I`, applicable since `|ψd| ≤ π`; the bin
phase `2πm` drops out as an integer multiple of `2π`), while the denominator `‖e^{iψ} − 1‖ ≤ |ψ|`
(the chord bound `Complex.norm_one_sub_exp_ofReal_mul_I_le`); the register size `d` cancels, leaving
`2/π`. -/
theorem quditPhaseGrad_qftInverse_norm_inner_quditBasis_ge (θ : ℝ) (d : ℕ) [NeZero d] (m : Fin d)
    (hnear : |θ - 2 * Real.pi * (m : ℕ) / d| ≤ Real.pi / d) :
    2 / Real.pi
      ≤ ‖inner ℂ (quditBasis m).vec
          ((qftInverseEvolution d).evolvePure (quditPhaseGrad θ d)).vec‖ := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  rcases eq_or_ne (θ - 2 * Real.pi * (m : ℕ) / d) 0 with hz | hz
  · -- Residual `ψ = 0`: the bin phase matches exactly, so the amplitude is `1`.
    have hone : inner ℂ (quditBasis m).vec
        ((qftInverseEvolution d).evolvePure (quditPhaseGrad θ d)).vec = 1 := by
      rw [quditPhaseGrad_qftInverse_inner_quditBasis θ d m, hz]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne d : d ≠ 0))
    rw [hone, norm_one]
    exact (div_le_one Real.pi_pos).mpr Real.two_le_pi
  · -- Residual `ψ ≠ 0`: bound numerator below and denominator above through the closed form.
    have hψabs : 0 < |θ - 2 * Real.pi * (m : ℕ) / d| := abs_pos.mpr hz
    have hψπ : |θ - 2 * Real.pi * (m : ℕ) / d| ≤ Real.pi := by
      have hle : Real.pi / (d : ℝ) ≤ Real.pi := by
        rw [div_le_iff₀ hdpos]
        calc Real.pi = Real.pi * 1 := (mul_one _).symm
          _ ≤ Real.pi * d := mul_le_mul_of_nonneg_left hd1 Real.pi_pos.le
      linarith
    have hgeoψ := Complex.two_div_pi_mul_abs_le_norm_one_sub_exp_ofReal_mul_I hψπ
    have hdenpos : 0 <
        ‖Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [norm_sub_rev]
      have hpos : 0 < 2 / Real.pi * |θ - 2 * Real.pi * (m : ℕ) / d| := mul_pos (by positivity) hψabs
      linarith
    have hne : Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      intro h; rw [h, sub_self, norm_zero] at hdenpos; exact lt_irrefl 0 hdenpos
    -- Numerator: `e^{iθd} = e^{iψd}` after absorbing the integer bin phase `2πm`.
    have hnumeq : Complex.exp (((θ * d : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((((θ - 2 * Real.pi * (m : ℕ) / d) * d : ℝ) : ℂ) * Complex.I) := by
      have hdℂ : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
      have key : ((θ * d : ℝ) : ℂ) * Complex.I
          = (((θ - 2 * Real.pi * (m : ℕ) / d) * d : ℝ) : ℂ) * Complex.I
            + (((m : ℕ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        field_simp
        ring
      rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hnum_ge : 2 / Real.pi * (|θ - 2 * Real.pi * (m : ℕ) / d| * d)
        ≤ ‖Complex.exp (((θ * d : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [hnumeq, norm_sub_rev]
      have hψd_le : |(θ - 2 * Real.pi * (m : ℕ) / d) * d| ≤ Real.pi := by
        rw [abs_mul, abs_of_pos hdpos]
        have hmul : |θ - 2 * Real.pi * (m : ℕ) / d| * d ≤ Real.pi / d * d :=
          mul_le_mul_of_nonneg_right hnear hdpos.le
        rwa [div_mul_cancel₀ Real.pi hd0] at hmul
      have hg := Complex.two_div_pi_mul_abs_le_norm_one_sub_exp_ofReal_mul_I hψd_le
      rwa [abs_mul, abs_of_pos hdpos] at hg
    have hden_le : ‖Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ |θ - 2 * Real.pi * (m : ℕ) / d| := by
      rw [norm_sub_rev]
      exact Complex.norm_one_sub_exp_ofReal_mul_I_le _
    rw [quditPhaseGrad_qftInverse_norm_inner_quditBasis θ d m hne, le_div_iff₀ hdenpos]
    -- Goal: `2/π · ‖e^{iψ}−1‖ ≤ d⁻¹ · ‖e^{iθd}−1‖`.
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hcancel : (d : ℝ)⁻¹ * (2 / Real.pi * (|θ - 2 * Real.pi * (m : ℕ) / d| * d))
        = 2 / Real.pi * |θ - 2 * Real.pi * (m : ℕ) / d| := by
      field_simp
    calc 2 / Real.pi
          * ‖Complex.exp (((θ - 2 * Real.pi * (m : ℕ) / d : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ 2 / Real.pi * |θ - 2 * Real.pi * (m : ℕ) / d| :=
          mul_le_mul_of_nonneg_left hden_le (by positivity)
      _ = (d : ℝ)⁻¹ * (2 / Real.pi * (|θ - 2 * Real.pi * (m : ℕ) / d| * d)) := hcancel.symm
      _ ≤ (d : ℝ)⁻¹ * ‖Complex.exp (((θ * d : ℝ) : ℂ) * Complex.I) - 1‖ :=
          mul_le_mul_of_nonneg_left hnum_ge (by positivity)

/-- **Nearest-bin success probability `≥ 4/π²`.** The Born probability of the read-out landing on
the bin `|m⟩` nearest the frequency (residual phase `|ψ| ≤ π/d`) is at least `4/π² ≈ 0.405`, the
squared form of `quditPhaseGrad_qftInverse_norm_inner_quditBasis_ge`. This is the quantitative sense
in which Kitaev's phase-estimation read-out "performs the transform" to finite precision: a constant
fraction of the probability — bounded away from `0`, independent of the register size `d` —
concentrates on the best estimate. -/
theorem quditPhaseGrad_qftInverse_norm_inner_quditBasis_sq_ge (θ : ℝ) (d : ℕ) [NeZero d] (m : Fin d)
    (hnear : |θ - 2 * Real.pi * (m : ℕ) / d| ≤ Real.pi / d) :
    4 / Real.pi ^ 2
      ≤ ‖inner ℂ (quditBasis m).vec
          ((qftInverseEvolution d).evolvePure (quditPhaseGrad θ d)).vec‖ ^ 2 := by
  have h := quditPhaseGrad_qftInverse_norm_inner_quditBasis_ge θ d m hnear
  rw [show (4 : ℝ) / Real.pi ^ 2 = (2 / Real.pi) ^ 2 from by ring, pow_two, pow_two]
  exact mul_self_le_mul_self (by positivity) h

/-- **The phase-gradient state is `2π`-periodic in its slope** (up to integer multiples of `2π`).
Shifting `θ` by an integer multiple of `2π` leaves every amplitude `e^{iθk}` unchanged, since
`e^{−2πijk} = 1` for integers `j, k` (`Complex.exp_int_mul_two_pi_mul_I`), so the state itself is
invariant: `quditPhaseGrad (θ − 2π·j) d = quditPhaseGrad θ d` for every `j : ℤ`. This lets a slope
be replaced by any representative in the same `2π`-class — used to bring the residual phase
`θ − 2πm/d` of the *wrap-around* nearest bin into `[−π/d, π/d]`. -/
theorem quditPhaseGrad_sub_intMul_two_pi (θ : ℝ) (d : ℕ) [NeZero d] (j : ℤ) :
    quditPhaseGrad (θ - 2 * Real.pi * j) d = quditPhaseGrad θ d := by
  apply PureState.ext
  rw [quditPhaseGrad_vec, quditPhaseGrad_vec]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hexp : Complex.exp (((θ - 2 * Real.pi * j : ℝ) : ℂ) * Complex.I * (k : ℕ))
      = Complex.exp ((θ : ℂ) * Complex.I * (k : ℕ)) := by
    rw [show ((θ - 2 * Real.pi * j : ℝ) : ℂ) * Complex.I * (k : ℕ)
          = (θ : ℂ) * Complex.I * (k : ℕ)
            + ((-(j * (k : ℕ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        from by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]

/-- **The nearest computational bin to a phase-gradient slope.** For real slope `θ` and register
size `d`, `nearestBin θ d : Fin d` is the computational-basis index `round(θ·d/(2π)) mod d` — the
bin whose phase `2π·(nearestBin θ d)/d` best matches `θ`, i.e. the best `⌈log₂ d⌉`-bit estimate of
the frequency `θ/(2π)`. The `round` picks the closest integer (`abs_sub_round`), and `mod d` folds
it into `Fin d` (absorbing the `2π` wrap-around when `θ/(2π)` is near `1`). This is the outcome the
phase-estimation read-out lands on with probability `≥ 4/π²`
(`quditPhaseGrad_qftInverse_norm_inner_nearestBin_sq_ge`). -/
def nearestBin (θ : ℝ) (d : ℕ) [NeZero d] : Fin d :=
  ⟨(round (θ * (d : ℝ) / (2 * Real.pi)) % (d : ℤ)).toNat, by
    have hdℤpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have h1 : 0 ≤ round (θ * (d : ℝ) / (2 * Real.pi)) % (d : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d)
    have h2 : round (θ * (d : ℝ) / (2 * Real.pi)) % (d : ℤ) < d := Int.emod_lt_of_pos _ hdℤpos
    exact (Int.toNat_lt h1).mpr h2⟩

/-- **Nearest-bin concentration of phase estimation, unconditionally** (N&C §5.2.1, the read-out
success bound at the best estimate). For *every* real slope `θ`, the terminal inverse-QFT read-out
of the phase gradient `|φ_θ⟩` lands on the nearest computational bin `nearestBin θ d` with Born
probability at least `4/π²`:
`4/π² ≤ ‖⟨nearestBin θ d | F⁻¹ | φ_θ⟩‖²`.

This removes the `|θ − 2πm/d| ≤ π/d` hypothesis of
`quditPhaseGrad_qftInverse_norm_inner_quditBasis_sq_ge` by *choosing* the bin: `nearestBin θ d`
= `round(θd/2π) mod d`, whose phase is within half a bin-width of `θ` (up to the `2π` wrap). It is
the quantitative sense in which phase estimation reads out the frequency to finite precision for an
*arbitrary* — in particular non-dyadic — slope, the general form behind Kitaev's QFT-over-`Z_p`
read-out (Problem 5.1).

Proof: let `j = round(θd/2π) / d` (integer division). The gradient is `2π`-periodic in the slope
(`quditPhaseGrad_sub_intMul_two_pi`), so the read-out at `θ` equals the read-out at the
representative `θ' = θ − 2π·j`; and `θ' − 2π·(nearestBin θ d)/d = θ − 2π·round(θd/2π)/d`, of modulus
`(2π/d)·|θd/2π − round(θd/2π)| ≤ (2π/d)·(1/2) = π/d` (`abs_sub_round`). Apply the hypothesis form at
`θ'`. -/
theorem quditPhaseGrad_qftInverse_norm_inner_nearestBin_sq_ge (θ : ℝ) (d : ℕ) [NeZero d] :
    4 / Real.pi ^ 2
      ≤ ‖inner ℂ (quditBasis (nearestBin θ d)).vec
          ((qftInverseEvolution d).evolvePure (quditPhaseGrad θ d)).vec‖ ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have h2pi : (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  -- the bin's integer value is the nonnegative residue `round(θd/2π) mod d`
  have hval : (((nearestBin θ d : Fin d) : ℕ) : ℤ)
      = round (θ * (d : ℝ) / (2 * Real.pi)) % (d : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d))
  -- replace the read-out at `θ` by the read-out at the periodic representative `θ − 2π·j`
  rw [← quditPhaseGrad_sub_intMul_two_pi θ d (round (θ * (d : ℝ) / (2 * Real.pi)) / (d : ℤ))]
  apply quditPhaseGrad_qftInverse_norm_inner_quditBasis_sq_ge
  set r : ℤ := round (θ * (d : ℝ) / (2 * Real.pi)) with hr
  set j : ℤ := r / (d : ℤ) with hj
  -- integer split `r = d·j + (nearestBin θ d)`, so the residual telescopes
  have hrdj : (d : ℤ) * j + (((nearestBin θ d : Fin d) : ℕ) : ℤ) = r := by
    rw [hval, hj]; exact Int.mul_ediv_add_emod r (d : ℤ)
  have hrdjR : (d : ℝ) * (j : ℝ) + (((nearestBin θ d : Fin d) : ℕ) : ℝ) = (r : ℝ) := by
    exact_mod_cast hrdj
  have hkey : (θ - 2 * Real.pi * (j : ℝ))
        - 2 * Real.pi * (((nearestBin θ d : Fin d) : ℕ) : ℝ) / (d : ℝ)
      = (2 * Real.pi / d) * (θ * (d : ℝ) / (2 * Real.pi) - (r : ℝ)) := by
    have hm : (((nearestBin θ d : Fin d) : ℕ) : ℝ) = (r : ℝ) - (d : ℝ) * (j : ℝ) := by
      linarith [hrdjR]
    rw [hm]; field_simp; ring
  rw [hkey, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / d)]
  have habs : |θ * (d : ℝ) / (2 * Real.pi) - (r : ℝ)| ≤ 1 / 2 := by
    rw [hr]; exact_mod_cast abs_sub_round (θ * (d : ℝ) / (2 * Real.pi))
  calc (2 * Real.pi / d) * |θ * (d : ℝ) / (2 * Real.pi) - (r : ℝ)|
        ≤ (2 * Real.pi / d) * (1 / 2) := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = Real.pi / d := by field_simp

end AxQM
