/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation
import AxQM.Concrete.RotationDecomposition
import AxQM.Concrete.SpecialOrthogonalAxisAngle

/-!
# Concrete: the *corrected* generalized Euler decomposition, for perpendicular axes (N&C Ex 4.11)

Nielsen & Chuang, Exercise 4.11 claims that for **non-parallel** unit vectors `m̂, n̂` every
single-qubit unitary `U` factors as `U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` (eq. 4.13). As shown in
`Concrete/EulerDecompositionCounterexample.lean`, that is **false**: mere non-parallelism does not
suffice. This file proves the **corrected** statement — the decomposition holds whenever the middle
axis is *perpendicular* to the (repeated) outer axis, `m̂ ⊥ n̂` (Davenport's theorem; the classical
Euler `ZYZ` decomposition, Theorem 4.1, is the special case `n̂ = ẑ`, `m̂ = ŷ`).

Everything is stated for matrices and scalars (`rotAxis`, `pauliDot`, `rot3D`, `Matrix`).

## What is formalized

* `rotAxis_conj_rotAxis` — **conjugating a rotation by a rotation rotates its axis**: for unit axes
  `p, v`, `R_p(φ) · R_v(θ) · R_p(φ)ᴴ = R_{R(φ)v}(θ)`, where `R(φ)v = rot3D p φ v`. Proved from the
  closed form of `R_v(θ)` and Exercise 4.6's `pauliDot_conj_rotAxis`.
* `orthoFrame` / `orthoFrame_mem_specialOrthogonalGroup` / `orthoFrame_mulVec_axisZ` /
  `orthoFrame_mulVec_axisY` — the **frame rotation** `O = [m̂×n̂ | m̂ | n̂] ∈ SO(3)` built from an
  orthonormal pair `(m̂, n̂)`, sending `ẑ ↦ n̂` and `ŷ ↦ m̂`.
* `exists_smul_rotAxis_triple_of_perp` — **the corrected Exercise 4.11**: for orthonormal `m̂ ⊥ n̂`
  and any unitary `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`, there exist `α, β, γ, δ` with
  `U = e^{iα} • (R_n̂(β) R_m̂(γ) R_n̂(δ))`.

## Design notes

* **Reduction to Theorem 4.1 by a frame rotation, exactly as N&C's "use Theorem 4.1" intends.**
  Euler's theorem (`exists_rot3D_eq_mulVec_of_mem_specialOrthogonalGroup`) realizes the frame
  `O = [m̂×n̂ | m̂ | n̂]` as a single spatial rotation `rot3D p φ`, hence as conjugation by the
  qubit rotation `W := R_p(φ)`. Because `W` sends `ẑ ↦ n̂` and `ŷ ↦ m̂` on the Bloch sphere,
  `W R_z(θ) Wᴴ = R_n̂(θ)` and `W R_y(θ) Wᴴ = R_m̂(θ)` (`rotAxis_conj_rotAxis`). Applying the Z–Y
  decomposition (`exists_zy_decomposition`) to the conjugate `Wᴴ U W` and conjugating back therefore
  turns each `R_z` into `R_n̂` and the middle `R_y` into `R_m̂`, giving (4.13) for `U`. No phase
  bookkeeping is needed: conjugation commutes with `exp`, so the identity `W R_v(θ) Wᴴ = R_{Wv}(θ)`
  is exact, not merely up to sign.
* **Why perpendicularity is exactly the right hypothesis.** The frame `O` needs `ŷ ↦ m̂` and
  `ẑ ↦ n̂` simultaneously as an *orthonormal* frame map, which forces `m̂ ⊥ n̂`; the counterexample
  file shows this is not a proof artefact but the genuine boundary of validity.
* **The frame matrix is proved orthogonal via its columns.** `Oᵀ O = I` is the clean statement:
  the columns `m̂×n̂, m̂, n̂` are orthonormal by the Lagrange identity. Then `O Oᵀ = I`, the form
  `Matrix.mem_orthogonalGroup_iff` wants, follows by `mul_eq_one_comm`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Conjugating a rotation by a rotation rotates its axis.** For unit axes `p, v` and angles
`φ, θ`, `R_p(φ) · R_v(θ) · R_p(φ)ᴴ = R_{R(φ)v}(θ)`, where `R(φ)v = rot3D p φ v` is the spatial
rotation of `v` about `p`. In the closed form `R_v(θ) = cos(θ/2) I − i sin(θ/2)(v·σ)`, the identity
part is fixed by unitarity (`R_p(φ) R_p(φ)ᴴ = I`) and the `v·σ` part is carried to `(R(φ)v)·σ` by
Exercise 4.6's `pauliDot_conj_rotAxis`; `rot3D_sq_sum` keeps `R(φ)v` a unit vector so the target is
again a rotation. -/
theorem rotAxis_conj_rotAxis {p v : Fin 3 → ℝ}
    (hp : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1) (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1)
    (φ θ : ℝ) :
    rotAxis p φ * rotAxis v θ * (rotAxis p φ)ᴴ = rotAxis (rot3D p φ v) θ := by
  have hrv : (rot3D p φ v) 0 ^ 2 + (rot3D p φ v) 1 ^ 2 + (rot3D p φ v) 2 ^ 2 = 1 := by
    rw [rot3D_sq_sum hp]; exact hv
  rw [rotAxis_eq_of_unit hv, rotAxis_eq_of_unit hrv, Matrix.mul_sub, Matrix.sub_mul,
    mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_one,
    rotAxis_mul_conjTranspose_self, pauliDot_conj_rotAxis hp]

/-- The **frame rotation** `O = [m̂×n̂ | m̂ | n̂]`: the `3 × 3` real matrix whose columns are the
cross product `m̂×n̂`, then `m̂`, then `n̂`. For an orthonormal pair `(m̂, n̂)` it is a proper
rotation (`orthoFrame_mem_specialOrthogonalGroup`) sending `ẑ ↦ n̂` and `ŷ ↦ m̂`. -/
def orthoFrame (m n : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![m 1 * n 2 - m 2 * n 1, m 0, n 0;
     m 2 * n 0 - m 0 * n 2, m 1, n 1;
     m 0 * n 1 - m 1 * n 0, m 2, n 2]

/-- The frame rotation sends `ẑ = (0,0,1)` to its third column `n̂`: `O · ẑ = n̂`. -/
theorem orthoFrame_mulVec_axisZ (m n : Fin 3 → ℝ) :
    (orthoFrame m n).mulVec ![0, 0, 1] = n := by
  funext i
  fin_cases i <;>
    simp [orthoFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The frame rotation sends `ŷ = (0,1,0)` to its second column `m̂`: `O · ŷ = m̂`. -/
theorem orthoFrame_mulVec_axisY (m n : Fin 3 → ℝ) :
    (orthoFrame m n).mulVec ![0, 1, 0] = m := by
  funext i
  fin_cases i <;>
    simp [orthoFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The frame rotation of an **orthonormal pair** is a proper rotation, `O ∈ SO(3)`. The columns
`m̂×n̂, m̂, n̂` are orthonormal (Lagrange gives `|m̂×n̂|² = 1`, and `(m̂×n̂)·m̂ = (m̂×n̂)·n̂ = 0`,
`m̂·n̂ = 0`), so `Oᵀ O = I`; the determinant is `det O = (m̂×n̂)·(m̂×n̂) = 1`. -/
theorem orthoFrame_mem_specialOrthogonalGroup {m n : Fin 3 → ℝ}
    (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hmn : m 0 * n 0 + m 1 * n 1 + m 2 * n 2 = 0) :
    orthoFrame m n ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  -- `|m̂×n̂|² = |m̂|²|n̂|² − (m̂·n̂)² = 1`, the Lagrange identity — reused for `Oᵀ O` and `det O`.
  have hcross : (m 1 * n 2 - m 2 * n 1) ^ 2 + (m 2 * n 0 - m 0 * n 2) ^ 2
      + (m 0 * n 1 - m 1 * n 0) ^ 2 = 1 := by
    linear_combination (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) * hm + hn
      - (m 0 * n 0 + m 1 * n 1 + m 2 * n 2) * hmn
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    -- The columns `m̂×n̂, m̂, n̂` are orthonormal, so `Oᵀ O = I`; then `O Oᵀ = I` by commutation.
    have hcol : (orthoFrame m n)ᵀ * orthoFrame m n = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.reduceFinMk, orthoFrame, Matrix.transpose_apply, Matrix.mul_apply,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Matrix.one_apply_eq,
          Matrix.one_apply_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
      · linear_combination hcross
      · ring
      · ring
      · ring
      · linear_combination hm
      · linear_combination hmn
      · ring
      · linear_combination hmn
      · linear_combination hn
    exact mul_eq_one_comm.mpr hcol
  · rw [Matrix.det_fin_three]
    simp only [orthoFrame, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination hcross

/-- **The corrected Nielsen & Chuang, Exercise 4.11.** For an orthonormal pair of axes — unit
vectors `m̂ ⊥ n̂` — every single-qubit unitary `U` factors as `U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)`
for some real `α, β, γ, δ`. This is the true statement N&C's Exercise 4.11 intends: perpendicularity
of `m̂` and `n̂` (not mere non-parallelism) is the correct hypothesis, and Theorem 4.1 (the Z–Y
decomposition, `n̂ = ẑ`, `m̂ = ŷ`) is the special case.

Realize the frame `O = [m̂×n̂ | m̂ | n̂] ∈ SO(3)` as a qubit rotation `W = R_p(φ)` (Euler's
theorem), so `W R_z(θ) Wᴴ = R_n̂(θ)` and `W R_y(θ) Wᴴ = R_m̂(θ)` (`rotAxis_conj_rotAxis`). Apply
Theorem 4.1 to `Wᴴ U W` and conjugate back by `W`. -/
theorem exists_smul_rotAxis_triple_of_perp {m n : Fin 3 → ℝ}
    (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hmn : m 0 * n 0 + m 1 * n 1 + m 2 * n 2 = 0)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ,
      U = Complex.exp ((α : ℂ) * Complex.I) • (rotAxis n β * rotAxis m γ * rotAxis n δ) := by
  -- The frame rotation, realized as a qubit rotation `W = R_p(φ)`.
  obtain ⟨p, φ, hp, heuler⟩ := exists_rot3D_eq_mulVec_of_mem_specialOrthogonalGroup
    (orthoFrame_mem_specialOrthogonalGroup hm hn hmn)
  set W : Matrix (Fin 2) (Fin 2) ℂ := rotAxis p φ with hW
  -- `W` sends `ẑ ↦ n̂` and `ŷ ↦ m̂` on the Bloch sphere.
  have haxZ : rot3D p φ ![0, 0, 1] = n :=
    (heuler ![0, 0, 1]).symm.trans (orthoFrame_mulVec_axisZ m n)
  have haxY : rot3D p φ ![0, 1, 0] = m :=
    (heuler ![0, 1, 0]).symm.trans (orthoFrame_mulVec_axisY m n)
  have hvz : (![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have hvy : (![0, 1, 0] : Fin 3 → ℝ) 0 ^ 2 + (![0, 1, 0] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 1, 0] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  -- Conjugation of the coordinate rotations by `W`.
  have hcZ : ∀ θ, W * rotZ θ * Wᴴ = rotAxis n θ := by
    intro θ
    rw [hW, rotZ, rotAxis_conj_rotAxis hp hvz, haxZ]
  have hcY : ∀ θ, W * rotY θ * Wᴴ = rotAxis m θ := by
    intro θ
    rw [hW, rotY, rotAxis_conj_rotAxis hp hvy, haxY]
  -- `W` is unitary, hence so is `Wᴴ U W`.
  have hWu : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := by rw [hW]; exact rotAxis_mem_unitaryGroup p φ
  have hWH : Wᴴ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mem hWu
  obtain ⟨α, β, γ, δ, hzy⟩ :=
    exists_zy_decomposition (Wᴴ * U * W) (mul_mem (mul_mem hWH hU) hWu)
  refine ⟨α, β, γ, δ, ?_⟩
  -- `U = W (Wᴴ U W) Wᴴ`.
  have hWWH : W * Wᴴ = 1 := by rw [hW]; exact rotAxis_mul_conjTranspose_self p φ
  have hWHW : Wᴴ * W = 1 := by rw [hW]; exact rotAxis_conjTranspose_mul_self p φ
  have hUconj : W * (Wᴴ * U * W) * Wᴴ = U := by
    calc W * (Wᴴ * U * W) * Wᴴ = (W * Wᴴ) * U * (W * Wᴴ) := by noncomm_ring
      _ = U := by rw [hWWH, one_mul, mul_one]
  conv_lhs => rw [← hUconj, hzy]
  rw [mul_smul_comm, smul_mul_assoc]
  refine congrArg (Complex.exp ((α : ℂ) * Complex.I) • ·) ?_
  -- Push the two `W`s through the phased `R_z R_y R_z` product, turning it into `R_n̂ R_m̂ R_n̂`.
  -- Reassociate the conjugated factors to expose the two `Wᴴ W` pairs, which collapse to `1`.
  have hreassoc : W * rotZ β * Wᴴ * (W * rotY γ * Wᴴ) * (W * rotZ δ * Wᴴ)
      = W * rotZ β * (Wᴴ * W) * rotY γ * (Wᴴ * W) * rotZ δ * Wᴴ := by noncomm_ring
  rw [← hcZ β, ← hcY γ, ← hcZ δ, hreassoc, hWHW]
  noncomm_ring

end AxQM.Concrete
