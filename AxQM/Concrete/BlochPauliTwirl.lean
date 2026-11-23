/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation

/-!
# AxQM.Concrete — the Bloch action of the Pauli conjugations and the Pauli twirl

The single-qubit **Pauli channel** `E(ρ) = ∑ₖ pₖ σₖ ρ σₖ` (`σ₀ = I`, `σ₁ = X`, `σ₂ = Y`,
`σ₃ = Z`) acts on the Bloch vector by a **diagonal contraction**: it multiplies the three Bloch
coordinates by `mₓ, m_y, m_z` where each `mⱼ` is a signed average of the four probabilities. This
file provides the matrix-algebra core of that fact — everything phrased purely on real
three-vectors `Fin 3 → ℝ` and the concrete Bloch matrix — for use
by the statement in `AxQM/NC/Ch8/Problem8_3.lean`.

* `rot3D_angle_zero`, `rot3D_axisX_pi`, `rot3D_axisY_pi`, `rot3D_axisZ_pi` — the Rodrigues rotation
  `rot3D` at angle `0` (the identity) and at angle `π` about each coordinate axis (a reflection that
  keeps that axis and negates the other two). The `π`-rotation about `x̂` is `R_x̂(π) = −iX`, whose
  *conjugation* action equals that of the Pauli `X`; likewise `ŷ ↔ Y`, `ẑ ↔ Z`. These are the Bloch
  actions of the four Pauli conjugations.
* `pauliBlochFlip k` — the induced sign-flip on the Bloch vector for the `k`-th Pauli (`k : Fin 4`),
  and `pauliBlochFlip_sq_sum`: it preserves the squared length (so it fixes the Bloch ball).
* `pauliTwirlVec p v` — the diagonal image `(mₓ v₀, m_y v₁, m_z v₂)` of `v` under a Pauli channel
  with weights `p`, `pauliTwirlVec_sq_sum_le`: it is a contraction of the Bloch ball (`|mⱼ| ≤ 1`),
  and `blochMatrix_pauliTwirl`: the probability-weighted average of the flipped Bloch matrices is
  the Bloch matrix of the twirled vector — the matrix identity behind the channel's action.
* `pauliTwirlInvProb d` — the **inverse** transform: the four Pauli weights realising a *prescribed*
  diagonal contraction `v ↦ (d₀ v₀, d₁ v₁, d₂ v₂)`. `pauliTwirlInvProb_sum` (they sum to `1`),
  `pauliTwirlVec_pauliTwirlInvProb` (their twirl *is* that contraction), and
  `pauliTwirlInvProb_nonneg_iff` (they are nonnegative — a genuine probability distribution — iff
  `d` lies in the Fujiwara–Algoet tetrahedron): the linear-algebra core of Problem 8.3's qubit
  converse for diagonal channels.
-/

open scoped Matrix

namespace AxQM.Concrete

/-- The Rodrigues rotation `rot3D n θ` at angle `θ = 0` is the identity on every vector: it is the
constant-map term `cos 0 • v + sin 0 • (n × v) + (1 − cos 0)(n·v) • n = v`. -/
theorem rot3D_angle_zero (n v : Fin 3 → ℝ) : rot3D n 0 v = v := by
  funext i
  simp only [rot3D, Real.cos_zero, Real.sin_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    one_mul, zero_smul, add_zero, sub_self, zero_mul, Pi.zero_apply]

/-- The `π`-rotation about the `x̂` axis negates the `y` and `z` Bloch coordinates and fixes `x`:
`rot3D x̂ π v = (v₀, −v₁, −v₂)`. This is the Bloch action of conjugation by the Pauli `X`
(`R_x̂(π) = −iX`, and the global phase cancels in `X ρ X†`). -/
theorem rot3D_axisX_pi (v : Fin 3 → ℝ) :
    rot3D ![1, 0, 0] Real.pi v = ![v 0, -v 1, -v 2] := by
  funext i
  fin_cases i <;>
    simp [rot3D, Real.cos_pi, Real.sin_pi, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The `π`-rotation about the `ŷ` axis negates the `x` and `z` Bloch coordinates and fixes `y`:
`rot3D ŷ π v = (−v₀, v₁, −v₂)`. This is the Bloch action of conjugation by the Pauli `Y`. -/
theorem rot3D_axisY_pi (v : Fin 3 → ℝ) :
    rot3D ![0, 1, 0] Real.pi v = ![-v 0, v 1, -v 2] := by
  funext i
  fin_cases i <;>
    simp [rot3D, Real.cos_pi, Real.sin_pi, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The `π`-rotation about the `ẑ` axis negates the `x` and `y` Bloch coordinates and fixes `z`:
`rot3D ẑ π v = (−v₀, −v₁, v₂)`. This is the Bloch action of conjugation by the Pauli `Z`. -/
theorem rot3D_axisZ_pi (v : Fin 3 → ℝ) :
    rot3D ![0, 0, 1] Real.pi v = ![-v 0, -v 1, v 2] := by
  funext i
  fin_cases i <;>
    simp [rot3D, Real.cos_pi, Real.sin_pi, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- **The Bloch-vector action of the `k`-th Pauli conjugation.** For `k : Fin 4` selecting one of
`I, X, Y, Z`, conjugation `σₖ ρ σₖ` sends a state with Bloch vector `v` to the state with Bloch
vector `pauliBlochFlip k v`: the identity fixes `v`, and `X`/`Y`/`Z` each negate the two Bloch
coordinates orthogonal to their axis (matching `rot3D_axisX_pi` etc.). -/
def pauliBlochFlip : Fin 4 → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  | 0, v => v
  | 1, v => ![v 0, -v 1, -v 2]
  | 2, v => ![-v 0, v 1, -v 2]
  | 3, v => ![-v 0, -v 1, v 2]

/-- Each Pauli conjugation **preserves the squared length** of the Bloch vector (it only flips
signs), so it maps the Bloch ball into itself. -/
theorem pauliBlochFlip_sq_sum (i : Fin 4) (v : Fin 3 → ℝ) :
    (pauliBlochFlip i v) 0 ^ 2 + (pauliBlochFlip i v) 1 ^ 2 + (pauliBlochFlip i v) 2 ^ 2
      = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  fin_cases i <;>
    simp only [pauliBlochFlip, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- **The Bloch image of a Pauli channel** with weights `p : Fin 4 → ℝ`: the diagonal contraction
`v ↦ (mₓ v₀, m_y v₁, m_z v₂)` with the *Pauli-transfer coefficients*
`mₓ = p₀ + p₁ − p₂ − p₃`, `m_y = p₀ − p₁ + p₂ − p₃`, `m_z = p₀ − p₁ − p₂ + p₃`
(each `mⱼ` is `∑ₖ ±pₖ`, the sign being `+` iff `σₖ` commutes with the `j`-th Pauli). -/
def pauliTwirlVec (p : Fin 4 → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(p 0 + p 1 - p 2 - p 3) * v 0, (p 0 - p 1 + p 2 - p 3) * v 1, (p 0 - p 1 - p 2 + p 3) * v 2]

/-- The Pauli-twirled vector stays in the **Bloch ball**: each transfer coefficient satisfies
`|mⱼ| ≤ 1` (it is `∑ ±pₖ` with `pₖ ≥ 0`, `∑ pₖ = 1`), so `‖pauliTwirlVec p v‖² ≤ ‖v‖²`. Concretely
`1 − mⱼ²` factors as a product of two nonnegative sums of the `pₖ` (e.g.
`1 − mₓ² = 4(p₀+p₁)(p₂+p₃)`). -/
theorem pauliTwirlVec_sq_sum_le (p : Fin 4 → ℝ) (v : Fin 3 → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) :
    (pauliTwirlVec p v) 0 ^ 2 + (pauliTwirlVec p v) 1 ^ 2 + (pauliTwirlVec p v) 2 ^ 2
      ≤ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [Fin.sum_univ_four] at hp
  simp only [pauliTwirlVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  have hx : (p 0 + p 1 - p 2 - p 3) ^ 2 ≤ 1 := by
    nlinarith [hp, mul_nonneg (add_nonneg (hp0 0) (hp0 1)) (add_nonneg (hp0 2) (hp0 3))]
  have hy : (p 0 - p 1 + p 2 - p 3) ^ 2 ≤ 1 := by
    nlinarith [hp, mul_nonneg (add_nonneg (hp0 0) (hp0 2)) (add_nonneg (hp0 1) (hp0 3))]
  have hz : (p 0 - p 1 - p 2 + p 3) ^ 2 ≤ 1 := by
    nlinarith [hp, mul_nonneg (add_nonneg (hp0 0) (hp0 3)) (add_nonneg (hp0 1) (hp0 2))]
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sq_nonneg (v 0)),
    mul_nonneg (sub_nonneg.2 hy) (sq_nonneg (v 1)),
    mul_nonneg (sub_nonneg.2 hz) (sq_nonneg (v 2))]

/-- **The matrix identity behind the Pauli channel's action.** The probability-weighted average of
the Pauli-flipped Bloch matrices is the Bloch matrix of the twirled vector:
`∑ₖ pₖ · ½(I + (σₖ·flip) v · σ) = ½(I + (pauliTwirlVec p v)·σ)`. The identity part contributes
`(∑ pₖ) I = I` (using `∑ pₖ = 1`); the Pauli part is linear in the vector, so the weighted average
of the flipped vectors is exactly `pauliTwirlVec p v`. -/
theorem blochMatrix_pauliTwirl (p : Fin 4 → ℝ) (v : Fin 3 → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, (p i : ℂ) • blochMatrix (pauliBlochFlip i v) = blochMatrix (pauliTwirlVec p v) := by
  have hpc : (p 0 : ℂ) + p 1 + p 2 + p 3 = 1 := by
    rw [Fin.sum_univ_four] at hp; exact_mod_cast hp
  rw [Fin.sum_univ_four]
  simp only [pauliBlochFlip, pauliTwirlVec, blochMatrix, pauliDot_eq]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val', smul_eq_mul, Fin.zero_eta, Fin.mk_one, ite_true, Matrix.cons_val] <;>
    push_cast <;>
    (first | (linear_combination (2⁻¹ : ℂ) * hpc) | ring)

/-- **The inverse Pauli-transfer transform.** Given a target diagonal Bloch action with transfer
coefficients `(d₀, d₁, d₂)` — the desired contraction `v ↦ (d₀ v₀, d₁ v₁, d₂ v₂)` — the four Pauli
weights `pₖ` that realise it as a Pauli channel `∑ₖ pₖ σₖ ρ σₖ`. Inverting the Walsh–Hadamard system
`mⱼ = ∑ₖ ±pₖ` together with `∑ₖ pₖ = 1` (the four coefficient rows form a Hadamard matrix, its own
inverse up to the factor `¼`):
`p₀ = ¼(1 + d₀ + d₁ + d₂)`, `p₁ = ¼(1 + d₀ − d₁ − d₂)`,
`p₂ = ¼(1 − d₀ + d₁ − d₂)`, `p₃ = ¼(1 − d₀ − d₁ + d₂)`.
These weights are a genuine probability distribution (nonnegative, summing to `1`) exactly when
`(d₀, d₁, d₂)` lies in the Fujiwara–Algoet tetrahedron (`pauliTwirlInvProb_nonneg_iff`). -/
noncomputable def pauliTwirlInvProb (d : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![(1 + d 0 + d 1 + d 2) / 4, (1 + d 0 - d 1 - d 2) / 4,
    (1 - d 0 + d 1 - d 2) / 4, (1 - d 0 - d 1 + d 2) / 4]

/-- The inverse Pauli-transfer weights always **sum to one**: whatever the target diagonal `d`, the
four `pauliTwirlInvProb d k` add up to `1` (the constant Hadamard row), so trace preservation of the
realising Pauli channel is automatic. -/
theorem pauliTwirlInvProb_sum (d : Fin 3 → ℝ) : ∑ i, pauliTwirlInvProb d i = 1 := by
  simp only [pauliTwirlInvProb, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  ring

/-- **The inverse transform is a right inverse of the Pauli twirl.** The Pauli channel with weights
`pauliTwirlInvProb d` has Bloch action exactly the diagonal contraction `v ↦ (d₀ v₀, d₁ v₁, d₂ v₂)`:
`pauliTwirlVec (pauliTwirlInvProb d) v = ![d₀ v₀, d₁ v₁, d₂ v₂]`. Thus every real diagonal `d` is
*algebraically* realised by these weights; realising it *physically* (as a genuine random-unitary
channel) additionally requires `pauliTwirlInvProb d ≥ 0` (`pauliTwirlInvProb_nonneg_iff`). -/
theorem pauliTwirlVec_pauliTwirlInvProb (d v : Fin 3 → ℝ) :
    pauliTwirlVec (pauliTwirlInvProb d) v = ![d 0 * v 0, d 1 * v 1, d 2 * v 2] := by
  funext i
  fin_cases i <;>
    simp only [pauliTwirlVec, pauliTwirlInvProb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] <;>
    ring_nf

/-- **The realisability criterion (Fujiwara–Algoet).** The inverse Pauli-transfer weights
`pauliTwirlInvProb d` are all nonnegative — i.e. `d` is realised by a genuine *random-unitary* Pauli
channel — exactly when the four Fujiwara–Algoet inequalities hold:
`1 + d₀ + d₁ + d₂ ≥ 0`, `1 + d₀ − d₁ − d₂ ≥ 0`, `1 − d₀ + d₁ − d₂ ≥ 0`, `1 − d₀ − d₁ + d₂ ≥ 0`,
i.e. `(d₀, d₁, d₂)` lies in the tetrahedron with vertices `(1,1,1), (1,−1,−1), (−1,1,−1),
(−1,−1,1)`. This is the complete-positivity condition on a diagonal-Bloch qubit channel; the
outstanding step of Problem 8.3's qubit converse is that a unital qubit *channel*'s singular-value
diagonal satisfies it. -/
theorem pauliTwirlInvProb_nonneg_iff (d : Fin 3 → ℝ) :
    (∀ i, 0 ≤ pauliTwirlInvProb d i) ↔
      (0 ≤ 1 + d 0 + d 1 + d 2 ∧ 0 ≤ 1 + d 0 - d 1 - d 2 ∧
       0 ≤ 1 - d 0 + d 1 - d 2 ∧ 0 ≤ 1 - d 0 - d 1 + d 2) := by
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [pauliTwirlInvProb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> norm_num [pauliTwirlInvProb] <;> linarith

end AxQM.Concrete
