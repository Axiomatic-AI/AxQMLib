/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecomposition
import AxQM.Concrete.Hadamard

/-!
# Concrete: the X–Y decomposition of a single-qubit unitary (Nielsen & Chuang, Exercise 4.10)

Nielsen & Chuang, Exercise 4.10
(*X–Y decomposition of rotations*) asks for a decomposition analogous to Theorem 4.1 (the Z–Y
decomposition) but using `R_x` instead of `R_z`: every single-qubit unitary `U` factors as

`U = e^{iα} R_x(β) R_y(γ) R_x(δ)`

for some real `α, β, γ, δ`. The statement of Exercise 4.10 is `exists_xy_decomposition`, in
`AxQM/NC/Ch4/Exercise4_10.lean`.

## What is formalised

* `hadamardC_mul_rotZ_mul_hadamardC` — `H R_z(θ) H = R_x(θ)`: conjugating a `z`-rotation by the
  Hadamard gate turns it into the `x`-rotation of the same angle (`H` exchanges the `x̂`/`ẑ` axes).
* `hadamardC_mul_rotY_mul_hadamardC` — `H R_y(θ) H = R_y(-θ)`: conjugating a `y`-rotation by `H`
  negates its angle (`H` flips the `ŷ` axis, `H Y H = -Y`).
* `exists_xy_decomposition` — **Exercise 4.10 itself**: for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
  there exist real `α, β, γ, δ` with `U = e^{iα} • (R_x(β) R_y(γ) R_x(δ))`.

## Design notes

* **Reduction to Theorem 4.1 by Hadamard conjugation, not a second entrywise derivation.** The
  Hadamard gate is an involution (`H² = I`, `hadamardC_mul_self`) that exchanges the `x̂` and `ẑ`
  axes and flips `ŷ`; hence `H R_z(θ) H = R_x(θ)` and `H R_y(θ) H = R_y(-θ)`. For a unitary `U`,
  `H U H` is again unitary, so the Z–Y decomposition (`exists_zy_decomposition`, Theorem 4.1) gives
  `H U H = e^{iα} R_z(β) R_y(γ) R_z(δ)`. Conjugating back by `H` (using `H (H U H) H = U`, since
  `H² = I`) and pushing the two `H`s through each factor turns every `R_z` into `R_x` and the middle
  `R_y(γ)` into `R_y(-γ)`, giving `U = e^{iα} R_x(β) R_y(-γ) R_x(δ)`. The middle angle `-γ` is just
  a real number, so this is the X–Y decomposition with `γ' := -γ`. Reusing Theorem 4.1 avoids
  redoing
  the entry-by-entry angle extraction from `U`.
* **"Unitary" as `Matrix.unitaryGroup`.** Exactly as in Theorem 4.1: a single-qubit unitary is a
  `2 × 2` complex matrix with `Uᴴ U = I`, so the statement is Exercise 4.10 in full generality (all
  of `U(2)`).
* **The conjugation lemmas are proved from the explicit closed forms** `rotZ_eq`/`rotX_eq`/`rotY_eq`
  (eqs. 4.4–4.6) by the entrywise `2 × 2` computation, the same idiom as
  `Concrete/HadamardRotation.lean` and `Concrete/RotationConjugation.lean`; the scalar `(√2)⁻¹² = ½`
  collapses the Hadamard normalisation. They are named theorems because Hadamard conjugation of the
  coordinate rotations is reusable Chapter-4 infrastructure.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- Conjugating the `z`-rotation by the Hadamard gate gives the `x`-rotation of the same angle:
`H R_z(θ) H = R_x(θ)`. The Hadamard reflection exchanges the `x̂` and `ẑ` axes (`H Z H = X`), so it
carries `R_z(θ) = exp(-iθZ/2)` to `R_x(θ) = exp(-iθX/2)`. Proved from the closed forms `rotZ_eq`,
`rotX_eq`: the diagonal phases `e^{∓iθ/2}` combine, via `H = (√2)⁻¹ !![1,1;1,-1]`, into the
`cos(θ/2)` / `-i sin(θ/2)` entries of `R_x`. -/
theorem hadamardC_mul_rotZ_mul_hadamardC (θ : ℝ) :
    hadamardC * rotZ θ * hadamardC = rotX θ := by
  have e1 : Complex.exp (-(θ / 2) * Complex.I)
      = (Real.cos (θ / 2) : ℂ) - (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show (-(θ / 2) : ℂ) * Complex.I = ((-(θ / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have e2 : Complex.exp ((θ / 2) * Complex.I)
      = (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show ((θ / 2) : ℂ) * Complex.I = ((θ / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hadamardC, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_two_mul_self, rotZ_eq, rotX_eq, e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one, smul_eq_mul, mul_zero,
      add_zero, zero_add] <;>
    ring

/-- Conjugating the `y`-rotation by the Hadamard gate negates its angle: `H R_y(θ) H = R_y(-θ)`.
The Hadamard reflection flips the `ŷ` axis (`H Y H = -Y`), so it sends `R_y(θ) = exp(-iθY/2)` to
`exp(iθY/2) = R_y(-θ)`. Proved from the closed form `rotY_eq` by the entrywise `2 × 2` computation,
with the sign flip supplied by `Real.cos_neg` / `Real.sin_neg`. -/
theorem hadamardC_mul_rotY_mul_hadamardC (θ : ℝ) :
    hadamardC * rotY θ * hadamardC = rotY (-θ) := by
  rw [hadamardC, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_two_mul_self, rotY_eq, rotY_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one, smul_eq_mul, neg_div,
      Real.cos_neg, Real.sin_neg, Complex.ofReal_neg] <;>
    ring

/-- **Nielsen & Chuang, Exercise 4.10 (X–Y decomposition of a single-qubit unitary).** Every
`2 × 2` unitary `U` (a single-qubit gate, `Uᴴ U = I`) factors as `U = e^{iα} R_x(β) R_y(γ) R_x(δ)`
for some real numbers `α, β, γ, δ` — Theorem 4.1 with `R_z` replaced by `R_x`. Since the Hadamard
gate `H` is an involution exchanging the `x̂`/`ẑ` axes and flipping `ŷ`, the conjugate `H U H` is
unitary, so the Z–Y decomposition (`exists_zy_decomposition`) yields
`H U H = e^{iα} R_z(β) R_y(γ) R_z(δ)`; conjugating back and pushing the `H`s through each factor
(`hadamardC_mul_rotZ_mul_hadamardC`, `hadamardC_mul_rotY_mul_hadamardC`) gives
`U = e^{iα} R_x(β) R_y(-γ) R_x(δ)`, i.e. the claim with middle angle `-γ`. -/
theorem exists_xy_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = Complex.exp ((α : ℂ) * Complex.I) • (rotX β * rotY γ * rotX δ) := by
  -- `H U H` is unitary (product of unitaries).
  have hHUH : hadamardC * U * hadamardC ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem hadamardC_mem_unitaryGroup hU) hadamardC_mem_unitaryGroup
  obtain ⟨α, β, γ, δ, hV⟩ := exists_zy_decomposition (hadamardC * U * hadamardC) hHUH
  refine ⟨α, β, -γ, δ, ?_⟩
  -- Push the two `H`s through the phased Z–Y product (`hadamardC_conj_mul` is `H²=I`
  -- multiplicativity of conjugation), turning each `R_z` into `R_x` and `R_y(γ)` into `R_y(-γ)`.
  have key : hadamardC * (rotZ β * rotY γ * rotZ δ) * hadamardC
      = rotX β * rotY (-γ) * rotX δ := by
    rw [hadamardC_conj_mul, hadamardC_conj_mul, hadamardC_mul_rotZ_mul_hadamardC,
      hadamardC_mul_rotY_mul_hadamardC, hadamardC_mul_rotZ_mul_hadamardC]
  -- `U = H (H U H) H` (`hadamardC_conj_conj` is `H²=I` double-conjugation); substitute the Z–Y
  -- decomposition of `H U H`, pull the phase out, and apply `key`.
  rw [← hadamardC_conj_conj U, hV, Matrix.mul_smul, Matrix.smul_mul, key]

end AxQM.Concrete
