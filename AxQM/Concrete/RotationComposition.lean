/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Concrete: composition of two Bloch-sphere rotations (Nielsen & Chuang, Exercise 4.15)

Nielsen & Chuang, Exercise 4.15 ("Composition of single qubit operations") asks: if a rotation
through `β₁` about `n̂₁` is followed by one through `β₂` about `n̂₂`, the overall operation is
again a rotation, through some angle `β₁₂` about some axis `n̂₁₂`; find `β₁₂, n̂₁₂` (eq. 4.19–4.20)
and specialise to `β₁ = β₂`, `n̂₁ = ẑ` (eq. 4.21–4.22).

The composite operator is the matrix product `R_n̂₂(β₂) · R_n̂₁(β₁)` ("`n̂₁` first, then `n̂₂`").
Writing `cᵢ = cos(βᵢ/2)`, `sᵢ = sin(βᵢ/2)` and reducing each factor to its closed form
`R_n̂(β) = cᵢ I − i sᵢ (n̂·σ)` (`rotAxis_eq_of_unit`), the product is the **quaternion
multiplication law**: with the Pauli rule `(a·σ)(b·σ) = (a·b) I + i (a×b)·σ` (`pauliDot_mul`),

`R_n̂₂(β₂) R_n̂₁(β₁) = [c₁c₂ − s₁s₂ (n̂₁·n̂₂)] I − i [s₁c₂ n̂₁ + c₁s₂ n̂₂ + s₁s₂ (n̂₂×n̂₁)]·σ`,

which is exactly `R_n̂₁₂(β₁₂) = c₁₂ I − i (s₁₂ n̂₁₂)·σ` for
`c₁₂ = rotComposeCos` (eq. 4.19) and `s₁₂ n̂₁₂ = rotComposeVec` (eq. 4.20).

## A sign erratum in the printed exercise

The printed eq. (4.20) has the cross-product term `− s₁s₂ n̂₂×n̂₁`; the correct term for the "`n̂₁`
then `n̂₂`" order stated in the text is `+ s₁s₂ n̂₂×n̂₁` (equivalently `− s₁s₂ n̂₁×n̂₂`), as the
derivation above and the witness `n̂₁ = ẑ, n̂₂ = x̂, β₁ = β₂ = π` both confirm (the composite
is `R_x(π)R_z(π) = −XZ`, whose axis is `−ŷ`, while the printed formula gives `+ŷ`). The printed sign
is precisely the composition law for the **opposite** operator order `R_n̂₁(β₁) R_n̂₂(β₂)` ("`n̂₂`
first"), recorded here as `rotAxis_mul_rotAxis_reversed`. We therefore formalise the *corrected*
statement as the headline law (`rotAxis_mul_rotAxis`) — a faithful reformulation of the exercise —
and expose the printed formula's true meaning as the reversed-order law, so the discrepancy is
documented, not silently repaired. Equation (4.19) for `c₁₂` is symmetric in the two rotations and
is correct as printed.

## What is formalized

* `rotComposeCos` / `rotComposeVec` — the composed half-angle cosine `c₁₂` (eq. 4.19) and the
  composed axis-vector `s₁₂ n̂₁₂` (eq. 4.20, corrected sign) for the order "`n̂₁` then `n̂₂`".
* `rotAxis_mul_rotAxis` — **part (1)**: `R_n̂₂(β₂) R_n̂₁(β₁) = c₁₂ I − i (s₁₂ n̂₁₂)·σ`, the
  composition law, for arbitrary unit axes and angles.
* `rotComposeCos_self_axisZ` / `rotComposeVec_self_axisZ` — **part (2)**: the `β₁ = β₂`, `n̂₁ = ẑ`
  simplifications (eq. 4.21 and eq. 4.22, corrected sign).
* `rotAxis_mul_rotAxis_reversed` — the printed eq. (4.20) formula, proved as the composition law for
  the reversed order `R_n̂₁(β₁) R_n̂₂(β₂)`; it pins down the printed cross-term sign as an
  order-transposition erratum.
* `rotAxis_mul_rotAxis_stated_order_printed_false` — a formal refutation: at the witness
  `n̂₁ = ẑ, n̂₂ = x̂, β₁ = β₂ = π` the composite `R_x(π) R_z(π)` differs from the operator built
  from N&C's printed axis-vector, so the printed eq. (4.20) is genuinely false for the stated order.

These are the statements of N&C Exercise 4.15; see also `AxQM/NC/Ch4/Exercise4_15.lean`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **composed half-angle cosine** `c₁₂ = c₁c₂ − s₁s₂ (n̂₁·n̂₂)` of a rotation by `β₁` about
`n₁` followed by a rotation by `β₂` about `n₂` (Nielsen & Chuang, eq. 4.19), with `cᵢ = cos(βᵢ/2)`,
`sᵢ = sin(βᵢ/2)`. Symmetric in the two rotations. -/
noncomputable def rotComposeCos (β₁ : ℝ) (n₁ : Fin 3 → ℝ) (β₂ : ℝ) (n₂ : Fin 3 → ℝ) : ℝ :=
  Real.cos (β₁ / 2) * Real.cos (β₂ / 2)
    - Real.sin (β₁ / 2) * Real.sin (β₂ / 2) * (n₁ ⬝ᵥ n₂)

/-- The **composed axis-vector** `s₁₂ n̂₁₂ = s₁c₂ n̂₁ + c₁s₂ n̂₂ + s₁s₂ (n̂₂×n̂₁)` of a rotation by
`β₁` about `n₁` followed by a rotation by `β₂` about `n₂` (Nielsen & Chuang, eq. 4.20), with
`cᵢ = cos(βᵢ/2)`, `sᵢ = sin(βᵢ/2)`. The cross-product sign is `+ s₁s₂ n̂₂×n̂₁`, correcting the
printed `− s₁s₂ n̂₂×n̂₁` (see the module docstring). -/
noncomputable def rotComposeVec (β₁ : ℝ) (n₁ : Fin 3 → ℝ) (β₂ : ℝ) (n₂ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (Real.sin (β₁ / 2) * Real.cos (β₂ / 2)) • n₁ + (Real.cos (β₁ / 2) * Real.sin (β₂ / 2)) • n₂
    + (Real.sin (β₁ / 2) * Real.sin (β₂ / 2)) • crossProduct n₂ n₁

/-- **Composition of two Bloch-sphere rotations — Nielsen & Chuang, Exercise 4.15 (1).** A rotation
by `β₁` about the unit axis `n₁` followed by a rotation by `β₂` about the unit axis `n₂` — the
operator product `R_n̂₂(β₂) R_n̂₁(β₁)` — is again a rotation operator
`R_n̂₁₂(β₁₂) = c₁₂ I − i (s₁₂ n̂₁₂)·σ`, whose composed cosine `c₁₂` and axis-vector `s₁₂ n̂₁₂` are
`rotComposeCos` (eq. 4.19) and `rotComposeVec` (eq. 4.20). Proof: reduce each factor to its closed
form `cᵢ I − i sᵢ (nᵢ·σ)` (`rotAxis_eq_of_unit`), expand the product, and collapse the
`(n₂·σ)(n₁·σ)` term with the Pauli product rule `pauliDot_mul` — the quaternion multiplication law.
Both axes are fully general unit vectors and both angles are arbitrary. -/
theorem rotAxis_mul_rotAxis {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1)
    (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1) (β₁ β₂ : ℝ) :
    rotAxis n₂ β₂ * rotAxis n₁ β₁
      = (rotComposeCos β₁ n₁ β₂ n₂ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - Complex.I • pauliDot (rotComposeVec β₁ n₁ β₂ n₂) := by
  rw [rotAxis_eq_of_unit h₂, rotAxis_eq_of_unit h₁, rotComposeVec, rotComposeCos,
    pauliDot_add, pauliDot_add, pauliDot_smul, pauliDot_smul, pauliDot_smul]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [pauliDot_mul n₂ n₁, dotProduct_comm n₂ n₁]
  push_cast
  simp only [smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq, Complex.I_pow_three] <;> ring

/-- **Special case of the composed cosine — Nielsen & Chuang, Exercise 4.15 (2), eq. 4.21.** When
the two rotations share the angle (`β₁ = β₂ = β`) and the first axis is `ẑ`, the composed half-angle
cosine `c₁₂` becomes `c² − s² (ẑ·n̂₂)` with `c = cos(β/2)`, `s = sin(β/2)`. -/
theorem rotComposeCos_self_axisZ (β : ℝ) (n₂ : Fin 3 → ℝ) :
    rotComposeCos β ![0, 0, 1] β n₂
      = Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2 * ((![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ n₂) := by
  rw [rotComposeCos]; ring

/-- **Special case of the composed axis-vector — Nielsen & Chuang, Exercise 4.15 (2), eq. 4.22.**
When the two rotations share the angle (`β₁ = β₂ = β`) and the first axis is `ẑ`, the composed
axis-vector `s₁₂ n̂₁₂` becomes `sc (ẑ + n̂₂) + s² (n̂₂ × ẑ)` with `c = cos(β/2)`, `s = sin(β/2)`.
The cross-product sign is `+ s² n̂₂×ẑ`, correcting the printed `− s² n̂₂×ẑ` (the same
order-transposition erratum as in eq. 4.20; see the module docstring). -/
theorem rotComposeVec_self_axisZ (β : ℝ) (n₂ : Fin 3 → ℝ) :
    rotComposeVec β ![0, 0, 1] β n₂
      = (Real.sin (β / 2) * Real.cos (β / 2)) • ((![0, 0, 1] : Fin 3 → ℝ) + n₂)
        + Real.sin (β / 2) ^ 2 • crossProduct n₂ ![0, 0, 1] := by
  rw [rotComposeVec]; module

/-- **The printed eq. (4.20) is the composition law for the reversed operator order.** N&C's printed
axis-vector `s₁c₂ n̂₁ + c₁s₂ n̂₂ − s₁s₂ n̂₂×n̂₁` (with the cross-product sign opposite to
`rotComposeVec`) is exactly the composed axis-vector of the *reversed* order `R_n̂₁(β₁) R_n̂₂(β₂)`
("`n̂₂` first, then `n̂₁`"), while `rotComposeCos` is unchanged (it is symmetric). This pins the
printed formula's sign as an order-transposition erratum: it holds, but for the operator product
opposite to the "`n̂₁` then `n̂₂`" order of the text. Proved from `rotAxis_mul_rotAxis` with the two
axes swapped, using `dotProduct_comm` and `cross_anticomm`. -/
theorem rotAxis_mul_rotAxis_reversed {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1)
    (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1) (β₁ β₂ : ℝ) :
    rotAxis n₁ β₁ * rotAxis n₂ β₂
      = (rotComposeCos β₁ n₁ β₂ n₂ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - Complex.I • pauliDot ((Real.sin (β₁ / 2) * Real.cos (β₂ / 2)) • n₁
            + (Real.cos (β₁ / 2) * Real.sin (β₂ / 2)) • n₂
            - (Real.sin (β₁ / 2) * Real.sin (β₂ / 2)) • crossProduct n₂ n₁) := by
  rw [rotAxis_mul_rotAxis h₂ h₁ β₂ β₁]
  have hcos : rotComposeCos β₂ n₂ β₁ n₁ = rotComposeCos β₁ n₁ β₂ n₂ := by
    rw [rotComposeCos, rotComposeCos, dotProduct_comm n₂ n₁]; ring
  have hvec : rotComposeVec β₂ n₂ β₁ n₁
      = (Real.sin (β₁ / 2) * Real.cos (β₂ / 2)) • n₁ + (Real.cos (β₁ / 2) * Real.sin (β₂ / 2)) • n₂
        - (Real.sin (β₁ / 2) * Real.sin (β₂ / 2)) • crossProduct n₂ n₁ := by
    have hcr : crossProduct n₁ n₂ = -crossProduct n₂ n₁ := (cross_anticomm n₂ n₁).symm
    rw [rotComposeVec, hcr]
    module
  rw [hcos, hvec]

/-- **The `SU(2)` unit-norm identity for the composed axis-vector.** For unit axes `n₁`, `n₂` the
composed half-angle cosine `c₁₂ = rotComposeCos` and axis-vector `s₁₂ n̂₁₂ = rotComposeVec` satisfy
`‖s₁₂ n̂₁₂‖² = 1 − c₁₂²` (equivalently `c₁₂² + ‖rotComposeVec‖² = 1`): the composed operator
`c₁₂ • I − i (rotComposeVec)·σ` (`rotAxis_mul_rotAxis`) is a genuine `SU(2)` element. Proof: expand
`‖·‖²` bilinearly, using Lagrange's identity `cross_dot_cross` (`‖n₂×n₁‖² = 1 − (n₁·n₂)²`) and the
orthogonality of `n₂×n₁` to `n₁` and `n₂` (`dot_cross_self`/`dot_self_cross`); the remaining
trigonometric identity is `sin² + cos² = 1` for both half-angles. -/
theorem rotComposeVec_normSq {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1) (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1)
    (β₁ β₂ : ℝ) :
    (rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
        + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2
      = 1 - (rotComposeCos β₁ n₁ β₂ n₂) ^ 2 := by
  have hnn1 : n₁ ⬝ᵥ n₁ = 1 := by
    simp only [dotProduct, Fin.sum_univ_three, ← pow_two]; exact h₁
  have hnn2 : n₂ ⬝ᵥ n₂ = 1 := by
    simp only [dotProduct, Fin.sum_univ_three, ← pow_two]; exact h₂
  have hp1 : Real.sin (β₁ / 2) ^ 2 + Real.cos (β₁ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hp2 : Real.sin (β₂ / 2) ^ 2 + Real.cos (β₂ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hd : n₂ ⬝ᵥ n₁ = n₁ ⬝ᵥ n₂ := dotProduct_comm n₂ n₁
  have hW1 : n₁ ⬝ᵥ crossProduct n₂ n₁ = 0 := dot_cross_self n₂ n₁
  have hW2 : n₂ ⬝ᵥ crossProduct n₂ n₁ = 0 := dot_self_cross n₂ n₁
  have hW1' : crossProduct n₂ n₁ ⬝ᵥ n₁ = 0 := by rw [dotProduct_comm]; exact hW1
  have hW2' : crossProduct n₂ n₁ ⬝ᵥ n₂ = 0 := by rw [dotProduct_comm]; exact hW2
  have hWW : crossProduct n₂ n₁ ⬝ᵥ crossProduct n₂ n₁ = 1 - (n₁ ⬝ᵥ n₂) ^ 2 := by
    rw [cross_dot_cross, hnn1, hnn2, hd]; ring
  rw [show (rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
        + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2
      = (rotComposeVec β₁ n₁ β₂ n₂) ⬝ᵥ (rotComposeVec β₁ n₁ β₂ n₂) from by
        simp only [dotProduct, Fin.sum_univ_three, ← pow_two], rotComposeVec, rotComposeCos]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    hnn1, hnn2, hd, hW1, hW2, hW1', hW2', hWW]
  nlinarith [hp1, hp2]

/-- The **unit axis of the composed rotation** `n̂₁₂`: the composed axis-vector `rotComposeVec`
(`= s₁₂ n̂₁₂`) rescaled to unit length (junk value `0` when `rotComposeVec = 0`, i.e. when the
composite is `± I`). Together with `rotComposeAngle` it presents the product of two Bloch rotations
as a single `rotAxis` (`rotAxis_mul_rotAxis_eq_rotAxis`). -/
noncomputable def rotComposeUnitAxis (β₁ : ℝ) (n₁ : Fin 3 → ℝ) (β₂ : ℝ) (n₂ : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  (Real.sqrt ((rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
      + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2))⁻¹ • rotComposeVec β₁ n₁ β₂ n₂

/-- The **angle of the composed rotation** `β₁₂ = 2 arccos c₁₂` (Nielsen & Chuang, eq. 4.19: its
half-angle cosine `cos(β₁₂/2) = c₁₂ = rotComposeCos`). -/
noncomputable def rotComposeAngle (β₁ : ℝ) (n₁ : Fin 3 → ℝ) (β₂ : ℝ) (n₂ : Fin 3 → ℝ) : ℝ :=
  2 * Real.arccos (rotComposeCos β₁ n₁ β₂ n₂)

/-- **The half-angle of the composed rotation**: `β₁₂ / 2 = arccos c₁₂`, unfolding
`rotComposeAngle = 2 arccos c₁₂`. The shared half-angle step of `rotComposeAngle_cos_half` /
`rotComposeAngle_sin_half`. -/
theorem rotComposeAngle_div_two (β₁ : ℝ) (n₁ : Fin 3 → ℝ) (β₂ : ℝ) (n₂ : Fin 3 → ℝ) :
    rotComposeAngle β₁ n₁ β₂ n₂ / 2 = Real.arccos (rotComposeCos β₁ n₁ β₂ n₂) := by
  rw [rotComposeAngle]; ring

/-- **The composed axis `n̂₁₂` is a unit vector** whenever the composite is not `± I`
(`rotComposeVec ≠ 0`): `‖rotComposeUnitAxis‖² = 1`. Immediate from the normalisation
`n̂₁₂ = ‖rotComposeVec‖⁻¹ • rotComposeVec` (`(‖v‖⁻¹)² ‖v‖² = 1`). The characterising fact for
`rotComposeUnitAxis`, consumed by `rotAxis_mul_rotAxis_eq_rotAxis` and by the Rodrigues landing on
`n̂₁₂` (Nielsen & Chuang, Exercise 6.10). -/
theorem rotComposeUnitAxis_normSq {n₁ n₂ : Fin 3 → ℝ} (β₁ β₂ : ℝ)
    (hne : (rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
        + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2 ≠ 0) :
    (rotComposeUnitAxis β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeUnitAxis β₁ n₁ β₂ n₂) 1 ^ 2
        + (rotComposeUnitAxis β₁ n₁ β₂ n₂) 2 ^ 2 = 1 := by
  have hSpos : 0 < (rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
      + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
  simp only [rotComposeUnitAxis, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← mul_add, ← mul_add, inv_pow, Real.sq_sqrt hSpos.le, inv_mul_cancel₀ hSpos.ne']

/-- **The composed half-angle cosine lies in `[-1, 1]`** for unit axes `n₁`, `n₂`:
`|c₁₂| ≤ 1` (`c₁₂ = rotComposeCos`), so `arccos c₁₂` — and hence `rotComposeAngle` — is well
defined. From `c₁₂² = 1 − ‖rotComposeVec‖² ≤ 1` (`rotComposeVec_normSq`). -/
theorem abs_rotComposeCos_le_one {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1) (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1)
    (β₁ β₂ : ℝ) : |rotComposeCos β₁ n₁ β₂ n₂| ≤ 1 := by
  have hS0 : (0 : ℝ) ≤ (rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
      + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2 := by positivity
  rw [rotComposeVec_normSq h₁ h₂ β₁ β₂] at hS0
  rw [abs_le]
  exact ⟨by nlinarith [hS0, sq_nonneg (rotComposeCos β₁ n₁ β₂ n₂ + 1)],
    by nlinarith [hS0, sq_nonneg (rotComposeCos β₁ n₁ β₂ n₂ - 1)]⟩

/-- **The half-angle cosine of the composed angle** (Nielsen & Chuang, eq. 4.19):
`cos(β₁₂/2) = c₁₂ = rotComposeCos`, for unit axes `n₁`, `n₂`. From `Real.cos_arccos`
(`|c₁₂| ≤ 1`, `abs_rotComposeCos_le_one`). The characterising tie of `rotComposeAngle` to N&C's
composed cosine `c₁₂`; used to hit a prescribed composed rotation angle (Exercise 6.10). -/
theorem rotComposeAngle_cos_half {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1) (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1)
    (β₁ β₂ : ℝ) : Real.cos (rotComposeAngle β₁ n₁ β₂ n₂ / 2) = rotComposeCos β₁ n₁ β₂ n₂ := by
  have h := abs_le.mp (abs_rotComposeCos_le_one h₁ h₂ β₁ β₂)
  rw [rotComposeAngle_div_two]
  exact Real.cos_arccos h.1 h.2

/-- **The half-angle sine of the composed angle**: `sin(β₁₂/2) = ‖rotComposeVec‖`, for unit axes
`n₁`, `n₂`. From `Real.sin_arccos` and the `SU(2)` identity `rotComposeVec_normSq`
(`‖rotComposeVec‖² = 1 − c₁₂²`). Paired with `rotComposeUnitAxis` it gives
`sin(β₁₂/2) • n̂₁₂ = rotComposeVec`. -/
theorem rotComposeAngle_sin_half {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1) (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1)
    (β₁ β₂ : ℝ) :
    Real.sin (rotComposeAngle β₁ n₁ β₂ n₂ / 2)
      = Real.sqrt ((rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
          + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2) := by
  rw [rotComposeAngle_div_two, Real.sin_arccos, ← rotComposeVec_normSq h₁ h₂ β₁ β₂]

/-- **A product of two Bloch rotations is itself a Bloch rotation.** For unit axes `n₁`, `n₂`, and
angles `β₁`, `β₂` whose composite is not `± I` (`rotComposeVec ≠ 0`), the operator product
`R_n̂₂(β₂) R_n̂₁(β₁)` is the single rotation `R_n̂₁₂(β₁₂)` about the unit axis
`n̂₁₂ = rotComposeUnitAxis` through the angle `β₁₂ = rotComposeAngle`. This upgrades the
`SU(2)`-coefficient form `rotAxis_mul_rotAxis` (`c₁₂ • I − i (rotComposeVec)·σ`) to a genuine
`rotAxis`, so the one-parameter group/power laws (`rotAxis_mul_same`, `rotAxis_pow`) apply to the
composite — the enabling step for iterating a two-reflection search/Grover step `U(Δt)^j`. Proof:
`rotAxis_eq_of_unit` on the unit composed axis (`rotComposeUnitAxis_normSq`) gives
`R_n̂₁₂(β₁₂) = cos(β₁₂/2) • I − i sin(β₁₂/2) (n̂₁₂·σ)`; the shared API lemmas
`rotComposeAngle_cos_half` (`cos(β₁₂/2) = c₁₂`) and `rotComposeAngle_sin_half`
(`sin(β₁₂/2) = ‖rotComposeVec‖`) with
`sin(β₁₂/2) • n̂₁₂ = rotComposeVec` match `rotAxis_mul_rotAxis`. -/
theorem rotAxis_mul_rotAxis_eq_rotAxis {n₁ n₂ : Fin 3 → ℝ}
    (h₁ : n₁ 0 ^ 2 + n₁ 1 ^ 2 + n₁ 2 ^ 2 = 1) (h₂ : n₂ 0 ^ 2 + n₂ 1 ^ 2 + n₂ 2 ^ 2 = 1)
    (β₁ β₂ : ℝ)
    (hne : (rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
        + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2 ≠ 0) :
    rotAxis n₂ β₂ * rotAxis n₁ β₁
      = rotAxis (rotComposeUnitAxis β₁ n₁ β₂ n₂) (rotComposeAngle β₁ n₁ β₂ n₂) := by
  have hSpos : 0 < (rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
      + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
  have hsqrtS : Real.sqrt ((rotComposeVec β₁ n₁ β₂ n₂) 0 ^ 2 + (rotComposeVec β₁ n₁ β₂ n₂) 1 ^ 2
      + (rotComposeVec β₁ n₁ β₂ n₂) 2 ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hSpos
  rw [rotAxis_mul_rotAxis h₁ h₂ β₁ β₂, rotAxis_eq_of_unit (rotComposeUnitAxis_normSq β₁ β₂ hne),
    rotComposeAngle_cos_half h₁ h₂, rotComposeAngle_sin_half h₁ h₂, rotComposeUnitAxis,
    pauliDot_smul]
  refine sub_right_inj.mpr ?_
  rw [smul_smul]
  congr 1
  rw [mul_right_comm, ← Complex.ofReal_mul, mul_inv_cancel₀ hsqrtS, Complex.ofReal_one, one_mul]

/-- **The exercise as printed is false for the stated order: a formal refutation of eq. (4.20).**
For the unit axes `n̂₁ = ẑ`, `n̂₂ = x̂` and `β₁ = β₂ = π`, the composite `R_x(π) R_z(π)` (the "`ẑ`
then `x̂`" order of the text) does *not* equal the rotation operator built from N&C's printed
axis-vector `s₁c₂ n̂₁ + c₁s₂ n̂₂ − s₁s₂ n̂₂×n̂₁` (cross sign opposite to `rotComposeVec`): the true
composed axis is `−ŷ` (`rotAxis_mul_rotAxis`), while the printed axis is `+ŷ`. So the printed sign
cannot be repaired by any choice of `β₁₂, n̂₁₂` — it is genuinely wrong for the "`n̂₁` then `n̂₂`"
order, confirming the erratum (the correct law is `rotAxis_mul_rotAxis`; the printed formula is
the reversed-order law `rotAxis_mul_rotAxis_reversed`). Proof: rewrite the composite by
`rotAxis_mul_rotAxis`, cancel the shared `c₁₂ I` and the injective `−i •` factor, and evaluate the
`(0,1)` entry of the two Pauli combinations at the witness (`i ≠ −i`). -/
theorem rotAxis_mul_rotAxis_stated_order_printed_false :
    rotAxis ![1, 0, 0] Real.pi * rotAxis ![0, 0, 1] Real.pi
      ≠ (rotComposeCos Real.pi ![0, 0, 1] Real.pi ![1, 0, 0] : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - Complex.I • pauliDot
            ((Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2)) • (![0, 0, 1] : Fin 3 → ℝ)
              + (Real.cos (Real.pi / 2) * Real.sin (Real.pi / 2)) • (![1, 0, 0] : Fin 3 → ℝ)
              - (Real.sin (Real.pi / 2) * Real.sin (Real.pi / 2))
                  • crossProduct ![1, 0, 0] ![0, 0, 1]) := by
  rw [rotAxis_mul_rotAxis (by simp) (by simp)]
  intro h
  rw [sub_right_inj] at h
  have h2 := smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) Complex.I_ne_zero h
  have h3 := congrFun (congrFun h2 0) 1
  simp only [rotComposeVec, pauliDot_eq, Real.cos_pi_div_two, Real.sin_pi_div_two, cross_apply,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply,
    Matrix.cons_val'] at h3
  norm_num [Complex.ext_iff] at h3

end AxQM.Concrete
