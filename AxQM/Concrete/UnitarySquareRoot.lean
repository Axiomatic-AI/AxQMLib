/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AxisAngleDecomposition

/-!
# AxQM.Concrete — the unitary square root of a single-qubit unitary

Every `2 × 2` unitary matrix has a unitary square root: for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
there is a `V` in the same unitary group with `V * V = U`. This is the matrix core behind the
gate square root `Evolution.exists_comp_self_eq` (`Postulates/API/UnitarySquareRoot.lean`), which
Nielsen & Chuang's Figure 4.8 construction of `C²(U)` needs: that circuit is built from a `V` with
`V² = U`, and the square root's existence is what makes the *"for any single-qubit unitary `U`"*
statement of Exercise 4.22 honest.

## What is formalised

* `AxQM.Concrete.exists_unitary_sq` — for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`,
  `∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ, V * V = U`.

## Design notes

**Construction (half-angle rotation).** Via the axis-angle decomposition (Exercise 4.8,
`Concrete.exists_axis_angle_decomposition`): write `U = e^{iα} R_n̂(θ)` for a real phase `α`, angle
`θ`, and unit axis `n̂`. The half-angle rotation `V := e^{iα/2} R_n̂(θ/2)` squares to `U`: the
one-parameter group law `rotAxis_mul_same` gives `R_n̂(θ/2) R_n̂(θ/2) = R_n̂(θ)`, and
`e^{iα/2} · e^{iα/2} = e^{iα}` (`Complex.exp_add`). Unitarity holds because `V` is a unit-modulus
scalar (`‖e^{iα/2}‖ = 1`) times the unitary rotation `R_n̂(θ/2)`
(`rotAxis_mul_conjTranspose_self`).
-/

open Matrix Complex

namespace AxQM.Concrete

/-- **Every `2 × 2` unitary has a unitary square root.** For `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
there is a unitary `V` with `V * V = U`. Taking the axis-angle form `U = e^{iα} R_n̂(θ)`
(`exists_axis_angle_decomposition`), the witness is the half-angle rotation
`V = e^{iα/2} R_n̂(θ/2)`, whose square is `U` by the rotation group law `rotAxis_mul_same`
(with `θ/2 + θ/2 = θ`) and `e^{iα/2} · e^{iα/2} = e^{iα}`. -/
theorem exists_unitary_sq {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ, V * V = U := by
  obtain ⟨α, θ, n, hn, hUeq⟩ := exists_axis_angle_decomposition U hU
  -- `star (e^{iα/2}) = e^{-iα/2}` (conjugating a real-times-`i` exponent flips the sign).
  have hstar : star (Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((-(α / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- `e^{iα/2} · star (e^{iα/2}) = 1`, i.e. the scalar has unit modulus.
  have hcc : Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I)
      * star (Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [hstar, ← Complex.exp_add,
      show ((α / 2 : ℝ) : ℂ) * Complex.I + ((-(α / 2) : ℝ) : ℂ) * Complex.I = 0 by
        push_cast; ring, Complex.exp_zero]
  refine ⟨Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I) • rotAxis n (θ / 2), ?_, ?_⟩
  · -- Unitarity: `(c • R) (c • R)ᴴ = (c · star c) • (R Rᴴ) = 1 • 1 = 1`.
    rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm,
      Matrix.star_eq_conjTranspose, rotAxis_mul_conjTranspose_self, hcc, one_smul]
  · -- Square: `(c • R(θ/2)) (c • R(θ/2)) = (c·c) • R(θ/2 + θ/2) = e^{iα} • R(θ) = U`.
    rw [smul_mul_smul_comm, rotAxis_mul_same, ← Complex.exp_add,
      show (θ / 2 + θ / 2) = θ by ring,
      show (((α / 2 : ℝ) : ℂ) * Complex.I + ((α / 2 : ℝ) : ℂ) * Complex.I)
          = ((α : ℝ) : ℂ) * Complex.I by push_cast; ring, ← hUeq]

end AxQM.Concrete
