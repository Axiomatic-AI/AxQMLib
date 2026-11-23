/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliEigenstateBloch

/-!
# Numeric bridges for the NMR `π/2`-pulse and `π/4`-coupling phases

Pure `ℂ`-arithmetic facts reused across the NMR §7.7.3 exercises (7.47/7.48/7.50): the `cos`/`sin`
values at the *un-normalised* `↑π/2/2` and `-↑π/2/2` arguments produced by the concrete rotation
matrices `Concrete.rotX`/`Concrete.rotY (±π/2)` (`R_θ` carries the half-angle `θ/2`), and the closed
forms of the coupled free-evolution phases `e^{∓iπ/4}` on the two-spin computational branches.

They build on the shared `Concrete.ofReal_{cos,sin}_pi_div_four` bridges (in
`AxQM/Concrete/PauliEigenstateBloch.lean`) rather than re-deriving `cos/sin(π/4) = 1/√2` from
scratch.  The lemma names encode the actual `↑π/2/2` argument (not the reduced `π/4`), to
distinguish them from those canonical bridges.
-/

namespace AxQM.Concrete

open Complex (I)

/-- `cos(π/2/2) = 1/√2`, at the un-normalised `↑π/2/2` argument that `Concrete.rotX/rotY (π/2)`
produces (the half-angle of a `90°` pulse). -/
theorem cos_pi_div_two_div_two : Complex.cos ((Real.pi : ℂ) / 2 / 2) = invSqrt2 := by
  rw [show ((Real.pi : ℂ) / 2 / 2) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cos, ofReal_cos_pi_div_four]

/-- `sin(π/2/2) = 1/√2`, at the `↑π/2/2` argument of a `90°` pulse. -/
theorem sin_pi_div_two_div_two : Complex.sin ((Real.pi : ℂ) / 2 / 2) = invSqrt2 := by
  rw [show ((Real.pi : ℂ) / 2 / 2) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sin, ofReal_sin_pi_div_four]

/-- `cos(-(π/2)/2) = 1/√2`, at the argument `Concrete.rotY (-(π/2))` produces (the barred pulse). -/
theorem cos_neg_pi_div_two_div_two : Complex.cos (-((Real.pi : ℂ) / 2) / 2) = invSqrt2 := by
  rw [show (-((Real.pi : ℂ) / 2) / 2) = ((-(Real.pi / 4) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cos, Real.cos_neg, ofReal_cos_pi_div_four]

/-- `sin(-(π/2)/2) = -1/√2`, at the argument `Concrete.rotY (-(π/2))` produces. -/
theorem sin_neg_pi_div_two_div_two : Complex.sin (-((Real.pi : ℂ) / 2) / 2) = -invSqrt2 := by
  rw [show (-((Real.pi : ℂ) / 2) / 2) = ((-(Real.pi / 4) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sin, Real.sin_neg, Complex.ofReal_neg, ofReal_sin_pi_div_four]

/-- `e^{-iπ/4} = (1 - i)/√2`, the coupled-evolution phase on the `|00⟩`/`|11⟩` branches. -/
theorem exp_neg_pi_div_four_mul_I :
    Complex.exp (-(I * ((Real.pi : ℂ) / 4))) = invSqrt2 - invSqrt2 * I := by
  rw [show -(I * ((Real.pi : ℂ) / 4)) = ((-(Real.pi / 4) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    ofReal_cos_pi_div_four, Complex.ofReal_neg, ofReal_sin_pi_div_four]
  ring

/-- `e^{iπ/4} = (1 + i)/√2`, the coupled-evolution phase on the `|01⟩`/`|10⟩` branches. -/
theorem exp_pi_div_four_mul_I :
    Complex.exp (I * ((Real.pi : ℂ) / 4)) = invSqrt2 + invSqrt2 * I := by
  rw [show (I * ((Real.pi : ℂ) / 4)) = ((Real.pi / 4 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ofReal_cos_pi_div_four,
    ofReal_sin_pi_div_four]

end AxQM.Concrete
