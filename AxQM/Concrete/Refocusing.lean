/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationConjugation

/-!
# Concrete: refocusing a single spin's free precession (Nielsen & Chuang, Exercise 7.38)

Nielsen & Chuang, §7.7.3 ("Refocusing"), introduces the `180°` NMR pulse `R²ₓ₁` as the square of
the `90°` rotation `Rₓ₁ = exp(−iπX/4)` (eq. 7.149) and states the *refocusing identity* (eq. 7.150)

`R²ₓ₁ · e^{−iaZ₁t} · R²ₓ₁ = e^{+iaZ₁t}`,

"as can be easily verified". Exercise 7.38 asks to show this explicitly, using the
anti-commutativity of the Pauli matrices. Everything here is pure `2 × 2` complex-matrix
mathematics: the statements involve only the Pauli matrices `pauliX`/`pauliZ`,
the rotation operators `rotX`, and the matrix exponential `NormedSpace.exp`.

## What is formalized

* `zEvolution a t = exp(−i a Z t)` — the free-precession propagator of a single spin under the
  Hamiltonian `H = a Z` (N&C §7.7.3), as a genuine `2 × 2` matrix exponential, with closed form
  `zEvolution_eq : zEvolution a t = cos(at) • I − (sin(at) · i) • Z`. The bridge
  `zEvolution_eq_rotZ : zEvolution a t = rotZ (2 a t)` ties it to `Concrete/Rotation`'s `rotZ`, so
  the existing rotation lemmas (e.g. `pauliX_mul_rotZ_mul_pauliX`) apply to it directly.
* `pauliX_conj_smul_one_sub_smul_pauliZ` — the anti-commutativity core: conjugating `c • I − d • Z`
  by the Pauli `X` flips the sign of the `Z`-component, `X (c•I − d•Z) X = c•I + d•Z`, because
  `X X = I` (`pauliX_mul_self`) and `X Z X = −Z` (`pauliX_mul_pauliZ_mul_pauliX`, the
  anti-commutation `{X, Z} = 0` the exercise asks us to use).
* `pauliX_mul_zEvolution_mul_pauliX` — the **refocusing identity's physical content**,
  `X · e^{−iaZt} · X = e^{+iaZt}` (here `e^{+iaZt} = zEvolution a (−t)`, i.e. refocusing *reverses*
  the time evolution). This is exactly (7.150) once the `180°` pulse is identified with the Pauli
  `X` (a `180°` `x`-pulse is `X` up to a global phase), and it is where anti-commutativity is used.
* `refocusPulse = rotX π` — the `180°` `x`-pulse `R²ₓ₁`, with `refocusPulse_eq_sq` certifying it is
  the square `Rₓ₁²` of the `90°` pulse `Rₓ₁ = rotX (π/2)` (eq. 7.149), and
  `refocusPulse_eq : refocusPulse = −i • X` computing it via `cos(π/2) = 0`, `sin(π/2) = 1`.
* `refocusPulse_mul_zEvolution_mul_refocusPulse` — the **literal** identity (7.150) with the
  *exact* exponential pulse `R²ₓ₁ = −iX`: `R²ₓ₁ · e^{−iaZt} · R²ₓ₁ = −e^{+iaZt}`.

## The global phase in (7.150)

Read literally with the exact `90°` pulse `Rₓ₁ = exp(−iπX/4)`, one has `R²ₓ₁ = exp(−iπX/2) = −iX`,
so the two pulses contribute `(−i)(−i) = −1`: the honest computation gives
`R²ₓ₁ e^{−iaZt} R²ₓ₁ = −e^{+iaZt}` (`refocusPulse_mul_zEvolution_mul_refocusPulse`), **not**
`+e^{+iaZt}`. Thus (7.150) as printed holds only up to the global phase `−1`. This phase is
physically irrelevant (unobservable), which is why N&C — treating a `180°` pulse as the Pauli `X` up
to phase — write the identity without it; equivalently, reading the sandwich as the *conjugation*
`R²ₓ₁ e^{−iaZt} (R²ₓ₁)†` (a similarity transform of the generator) it is *exactly* `e^{+iaZt}`. The
full physical content — that the `180°` pulse reverses the `Z`-evolution — is captured exactly and
phase-free by `pauliX_mul_zEvolution_mul_pauliX`. Both facets are recorded so the formalization is
faithful to the physics and honest about the printed equation.

## Design notes

* `zEvolution` is defined literally as N&C's `exp(−iaZt)` (not as an explicit matrix), mirroring
  `Concrete/Rotation.lean`'s `rotAxis`, so the definition is manifestly faithful to N&C's
  propagator; its closed form `zEvolution_eq` is a *theorem*, obtained by writing `Z = ẑ · σ`
  (`pauliDot_axisZ`) and applying the Exercise 2.35 exponential `pauliDot_exp_of_unit`.
* The refocusing proofs are algebraic — distribute the conjugation over the closed form and apply
  `X X = I` and `X Z X = −Z` — rather than an entrywise `2 × 2` computation, keeping the exercise's
  "use anti-commutativity" reasoning visible in the proof term.
-/

namespace AxQM.Concrete

open Matrix Complex NormedSpace

/-- The **free-precession propagator** `e^{−iaZt}` of a single spin under the Hamiltonian `H = a Z`
(Nielsen & Chuang, §7.7.3), as the `2 × 2` matrix exponential `exp(−i (a t) Z)`. The accumulated
phase depends only on the product `a t`; `zEvolution a (−t) = e^{+iaZt}` is the time-reversed
propagator. It is the `z`-rotation `R_z(2 a t)` (`zEvolution_eq_rotZ`), the `H = a Z`
reparametrization of `Concrete/Rotation`'s `rotZ`, so it interoperates with the rotation API. -/
noncomputable def zEvolution (a t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  exp ((((-(a * t) : ℝ) : ℂ) * Complex.I) • pauliZ)

/-- **Bridge to the rotation API.** The free-precession propagator is the `z`-rotation by twice the
accumulated phase: `e^{−iaZt} = R_z(2 a t)`, since `R_z(θ) = exp(−iθZ/2)` (`rotZ`) and `Z = ẑ · σ`
(`pauliDot_axisZ`). This connects `zEvolution` to the coordinate-rotation lemmas of
`Concrete/Rotation`/`Concrete/RotationConjugation` (e.g. `pauliX_mul_rotZ_mul_pauliX`), shared with
the neighbouring refocusing items (7.39/7.40). -/
theorem zEvolution_eq_rotZ (a t : ℝ) : zEvolution a t = rotZ (2 * a * t) := by
  rw [zEvolution, rotZ, rotAxis, pauliDot_axisZ]
  ring_nf

/-- The **closed form** of the free-precession propagator:
`e^{−iaZt} = cos(at) • I − (sin(at) · i) • Z`.
Writing `Z = ẑ · σ` (`pauliDot_axisZ`), this is the Exercise 2.35 exponential `pauliDot_exp_of_unit`
at the real angle `−(a t)`, simplified with `cos(−x) = cos x` and `sin(−x) = −sin x`. -/
theorem zEvolution_eq (a t : ℝ) :
    zEvolution a t = (Real.cos (a * t) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - ((Real.sin (a * t) : ℂ) * Complex.I) • pauliZ := by
  rw [zEvolution, ← pauliDot_axisZ, pauliDot_exp_of_unit (by simp) (-(a * t))]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul]
  module

/-- **Anti-commutativity core of refocusing.** Conjugating the Pauli-diagonal combination
`c • I − d • Z` by the Pauli `X` flips the sign of the `Z`-component:
`X (c • I − d • Z) X = c • I + d • Z`.
The `I`-term is fixed (`X X = I`, `pauliX_mul_self`) and the `Z`-term is negated
(`X Z X = −Z`, `pauliX_mul_pauliZ_mul_pauliX`, i.e. `{X, Z} = 0`). -/
theorem pauliX_conj_smul_one_sub_smul_pauliZ (c d : ℂ) :
    pauliX * (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) - d • pauliZ) * pauliX
      = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + d • pauliZ := by
  rw [mul_sub, mul_smul_comm, mul_smul_comm, mul_one, sub_mul, smul_mul_assoc, smul_mul_assoc,
    pauliX_mul_self, pauliX_mul_pauliZ_mul_pauliX, smul_neg, sub_neg_eq_add]

/-- **Refocusing identity (physical content), Nielsen & Chuang eq. 7.150.**
Conjugating the free-precession propagator by the Pauli `X` reverses the evolution:
`X · e^{−iaZt} · X = e^{+iaZt}` (`= zEvolution a (−t)`).
This is (7.150) with the `180°` pulse identified with `X` (up to global phase); the sign reversal is
the anti-commutativity `X Z X = −Z` (`pauliX_conj_smul_one_sub_smul_pauliZ`). -/
theorem pauliX_mul_zEvolution_mul_pauliX (a t : ℝ) :
    pauliX * zEvolution a t * pauliX = zEvolution a (-t) := by
  rw [zEvolution_eq, pauliX_conj_smul_one_sub_smul_pauliZ, zEvolution_eq]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul, neg_smul,
    sub_neg_eq_add]

/-- The **`180°` `x`-pulse** `R²ₓ₁ = exp(−iπX/2)`, the square of the `90°` rotation
`Rₓ₁ = exp(−iπX/4)` (Nielsen & Chuang, eq. 7.149), realized as `rotX π`. -/
noncomputable def refocusPulse : Matrix (Fin 2) (Fin 2) ℂ := rotX Real.pi

/-- The refocusing pulse **is the square of the `90°` pulse**: `R²ₓ₁ = Rₓ₁ · Rₓ₁` with
`Rₓ₁ = rotX (π/2)` (Nielsen & Chuang, eq. 7.149), via the one-parameter group law
`rotAxis_mul_same` and `π/2 + π/2 = π`. -/
theorem refocusPulse_eq_sq : refocusPulse = rotX (Real.pi / 2) * rotX (Real.pi / 2) := by
  rw [refocusPulse, rotX, rotX, rotAxis_mul_same, add_halves]

/-- The **`180°` pulse as a Pauli matrix**: `R²ₓ₁ = −i • X`. From `rotX_eq` with `cos(π/2) = 0`,
`sin(π/2) = 1`: `rotX π = !![0, −i; −i, 0] = −i • X`. -/
theorem refocusPulse_eq : refocusPulse = -Complex.I • pauliX := by
  rw [refocusPulse, rotX_eq, pauliX, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Refocusing identity, literal form (Nielsen & Chuang eq. 7.150), exact exponential pulse.**
With `R²ₓ₁ = exp(−iπX/2) = −iX`, the two `−i` factors multiply to `−1`, so
`R²ₓ₁ · e^{−iaZt} · R²ₓ₁ = −e^{+iaZt}` (`= −zEvolution a (−t)`).
Thus (7.150) as printed holds up to the physically-irrelevant global phase `−1`; the exact,
phase-free content is `pauliX_mul_zEvolution_mul_pauliX`. -/
theorem refocusPulse_mul_zEvolution_mul_refocusPulse (a t : ℝ) :
    refocusPulse * zEvolution a t * refocusPulse = -zEvolution a (-t) := by
  rw [refocusPulse_eq, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    pauliX_mul_zEvolution_mul_pauliX, neg_mul_neg, Complex.I_mul_I, neg_one_smul]

end AxQM.Concrete
