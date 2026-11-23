/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DualRail
import AxQM.Postulates.API.Swap

/-!
# AxQM.Postulates.API — the dual-rail beamsplitter

The **beamsplitter** acting on a dual-rail single-photon qubit (Nielsen & Chuang §7.4.2). A
beamsplitter couples two optical modes; on the single-photon dual-rail manifold
`{|0_L⟩ = |01⟩, |1_L⟩ = |10⟩}` it performs the real rotation

`B(θ) : |01⟩ ↦ cos θ |01⟩ + sin θ |10⟩,   |10⟩ ↦ -sin θ |01⟩ + cos θ |10⟩`

(N&C eq. 7.35, `B = [[cos θ, -sin θ]; [sin θ, cos θ]]`). Because the two modes each sit in the
`qubit ⊗ qubit` space of `DualRail.lean` (so the beamsplitter can compose with the phase shifter
`phaseShiftGate.onRight` of Exercise 7.7), we model `B(θ)` as the **number-conserving** unitary that
rotates the plane `span{|01⟩, |10⟩}` and fixes its orthogonal complement (the vacuum `|00⟩` and the
two-photon `|11⟩`). This is the faithful realisation on `qubit ⊗ qubit` of N&C's logical `2 × 2`
action — a *planar rotation*

`B(θ) = 1 + (cos θ - 1)·(|01⟩⟨01| + |10⟩⟨10|) + sin θ·(|10⟩⟨01| - |01⟩⟨10|)`.

* `dualRailPlaneProj` — the projector `|01⟩⟨01| + |10⟩⟨10|` onto the dual-rail plane.
* `dualRailRotGen` — the anti-self-adjoint generator `|10⟩⟨01| - |01⟩⟨10|` (the `y`-rotation
  generator of the plane, `G² = -P`).
* `beamSplitterDualRailOp θ` — the beamsplitter operator, `1 + (cos θ - 1)·P + sin θ·G`.
* `beamSplitterDualRailOp_comp` — the group law `B(α) B(β) = B(α + β)` (angle addition), from which
  unitarity (`beamSplitterDualRailOp_mem_unitary`, via `star B(θ) = B(-θ) = B(θ)⁻¹`) follows.
* `beamSplitterDualRail θ` — the beamsplitter as an `Evolution (qubit ⊗ qubit)`.
* `beamSplitterDualRail_evolvePure_dualRail` — its action on a dual-rail state:
  `c₀|01⟩ + c₁|10⟩ ↦ (cos θ·c₀ - sin θ·c₁)|01⟩ + (sin θ·c₀ + cos θ·c₁)|10⟩` (N&C 7.35).
* `beamSplitterDualRail_comp` / `beamSplitterDualRail_zero` — the composition law and
  `B(0) = 1` lifted to `Evolution`s (used by the Mach-Zehnder identity circuit, Exercise 7.10.1).

The exercises of `AxQM/NC/` use `beamSplitterDualRail` and `evolvePure`. The unitarity of the
planar rotation is proved through the rank-one algebra (`InnerProductSpace.rankOne_comp_rankOne`
and the four codeword inner products) and the angle-addition group law, mirroring
`Concrete.qubitRotY`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The four dual-rail codeword inner products -/

/-- `⟨01|01⟩ = 1`: the logical-zero codeword is a unit vector. (Not `@[simp]`: simp already
reduces `inner ℂ dualRailZero.vec dualRailZero.vec` via the `.vec` unfolds, so this is used by name
in the rank-one algebra below.) -/
theorem dualRailZero_inner_self :
    (inner ℂ dualRailZero.vec dualRailZero.vec : ℂ) = 1 := by
  rw [dualRailZero_vec, qubitBasis_tmul_inner]; simp

/-- `⟨10|10⟩ = 1`: the logical-one codeword is a unit vector. (Not `@[simp]`; used by name.) -/
theorem dualRailOne_inner_self :
    (inner ℂ dualRailOne.vec dualRailOne.vec : ℂ) = 1 := by
  rw [dualRailOne_vec, qubitBasis_tmul_inner]; simp

/-- `⟨10|01⟩ = 0`: the dual-rail codewords are orthogonal (the reverse of
`dualRailZero_inner_dualRailOne`). (Not `@[simp]`; used by name.) -/
theorem dualRailOne_inner_dualRailZero :
    (inner ℂ dualRailOne.vec dualRailZero.vec : ℂ) = 0 := by
  rw [dualRailOne_vec, dualRailZero_vec, qubitBasis_tmul_inner]; simp

/-- The squared norm of a dual-rail superposition, unconditionally: `‖c₀|01⟩ + c₁|10⟩‖² =
‖c₀‖² + ‖c₁‖²` (the codewords are orthonormal). The amplitude form `norm_dualRailVec` is the special
case with the amplitude constraint. -/
theorem norm_dualRailVec_sq (c0 c1 : ℂ) :
    ‖dualRailVec c0 c1‖ ^ 2 = ‖c0‖ ^ 2 + ‖c1‖ ^ 2 := by
  rw [dualRailVec, norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, dualRailZero.normalized,
    dualRailOne.normalized, inner_smul_left, inner_smul_right, dualRailZero_inner_dualRailOne]
  simp only [mul_one, mul_zero, map_zero, add_zero]

/-! ### The dual-rail plane projector and rotation generator -/

/-- The **projector onto the dual-rail plane** `span{|01⟩, |10⟩}`:
`P = |01⟩⟨01| + |10⟩⟨10|`. -/
def dualRailPlaneProj : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  InnerProductSpace.rankOne ℂ dualRailZero.vec dualRailZero.vec
    + InnerProductSpace.rankOne ℂ dualRailOne.vec dualRailOne.vec

/-- The **rotation generator** of the dual-rail plane: `G = |10⟩⟨01| - |01⟩⟨10|`, the anti-self-
adjoint operator with `G² = -P` (`σ₊ - σ₋` in the logical basis). -/
def dualRailRotGen : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  InnerProductSpace.rankOne ℂ dualRailOne.vec dualRailZero.vec
    - InnerProductSpace.rankOne ℂ dualRailZero.vec dualRailOne.vec

/-- `P² = P`: the dual-rail plane projector is idempotent (the cross terms vanish by codeword
orthogonality). -/
theorem dualRailPlaneProj_mul_self : dualRailPlaneProj * dualRailPlaneProj = dualRailPlaneProj := by
  simp only [dualRailPlaneProj, add_mul, mul_add, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    add_zero, zero_add]

/-- `P G = G`: the projector fixes the in-plane generator. -/
theorem dualRailPlaneProj_mul_rotGen : dualRailPlaneProj * dualRailRotGen = dualRailRotGen := by
  simp only [dualRailPlaneProj, dualRailRotGen, add_mul, mul_sub, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    add_zero, zero_add]

/-- `G P = G`: the projector fixes the in-plane generator (on the right). -/
theorem dualRailRotGen_mul_planeProj : dualRailRotGen * dualRailPlaneProj = dualRailRotGen := by
  simp only [dualRailPlaneProj, dualRailRotGen, mul_add, sub_mul, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    sub_zero, zero_sub]
  abel

/-- `G² = -P`: squaring the generator gives minus the plane projector (the `σ₊σ₋ = P₁`,
`σ₋σ₊ = P₀` cross terms combine to `-(P₀ + P₁) = -P`; the diagonal squares vanish). -/
theorem dualRailRotGen_mul_self : dualRailRotGen * dualRailRotGen = -dualRailPlaneProj := by
  simp only [dualRailPlaneProj, dualRailRotGen, mul_sub, sub_mul, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne, dualRailZero_inner_self, dualRailOne_inner_self,
    dualRailZero_inner_dualRailOne, dualRailOne_inner_dualRailZero, one_smul, zero_smul,
    sub_zero, zero_sub, neg_add]
  abel

/-- `star P = P`: the plane projector is self-adjoint (`adjoint_rankOne` fixes each diagonal
rank-one term). -/
theorem star_dualRailPlaneProj : star dualRailPlaneProj = dualRailPlaneProj := by
  simp only [dualRailPlaneProj, star_add, ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne]

/-- `star G = -G`: the generator is anti-self-adjoint (`adjoint_rankOne` swaps the two off-diagonal
rank-ones). -/
theorem star_dualRailRotGen : star dualRailRotGen = -dualRailRotGen := by
  simp only [dualRailRotGen, star_sub, ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne]
  abel

/-! ### The beamsplitter operator -/

/-- The **beamsplitter operator** on the dual-rail space, mixing angle `θ`:
`B(θ) = 1 + (cos θ - 1)·P + sin θ·G`, the planar rotation of `span{|01⟩, |10⟩}` by `θ` (and identity
on the orthogonal complement `span{|00⟩, |11⟩}`). On the logical manifold it is the real rotation
`[[cos θ, -sin θ]; [sin θ, cos θ]]` of Nielsen & Chuang eq. 7.35. -/
def beamSplitterDualRailOp (θ : ℝ) : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  1 + ((Real.cos θ : ℂ) - 1) • dualRailPlaneProj + (Real.sin θ : ℂ) • dualRailRotGen

/-- **Angle addition (group law):** `B(α) B(β) = B(α + β)`. The plane rotates by the sum of the
angles; the identity part off the plane is untouched. Proved from the plane algebra `P² = P`,
`PG = GP = G`, `G² = -P` and the addition formulas for `cos`/`sin`. -/
theorem beamSplitterDualRailOp_comp (α β : ℝ) :
    beamSplitterDualRailOp α * beamSplitterDualRailOp β = beamSplitterDualRailOp (α + β) := by
  simp only [beamSplitterDualRailOp, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, dualRailPlaneProj_mul_self, dualRailPlaneProj_mul_rotGen,
    dualRailRotGen_mul_planeProj, dualRailRotGen_mul_self, smul_neg]
  match_scalars <;>
    simp only [Complex.cos_add, Complex.sin_add] <;> ring

/-- `B(0) = 1`: the zero-angle beamsplitter is the identity (`cos 0 = 1`, `sin 0 = 0`). -/
theorem beamSplitterDualRailOp_zero : beamSplitterDualRailOp 0 = 1 := by
  simp [beamSplitterDualRailOp]

/-- `star B(θ) = B(-θ)`: the beamsplitter's adjoint is the reverse rotation (`cos` even, `sin` odd,
`star P = P`, `star G = -G`). -/
theorem star_beamSplitterDualRailOp (θ : ℝ) :
    star (beamSplitterDualRailOp θ) = beamSplitterDualRailOp (-θ) := by
  have hcos : star ((Real.cos θ : ℂ)) = (Real.cos θ : ℂ) := Complex.conj_ofReal _
  have hsin : star ((Real.sin θ : ℂ)) = (Real.sin θ : ℂ) := Complex.conj_ofReal _
  have hc : star ((Real.cos θ : ℂ) - 1) = (Real.cos θ : ℂ) - 1 := by
    rw [star_sub, star_one, hcos]
  rw [beamSplitterDualRailOp, beamSplitterDualRailOp, star_add, star_add, star_smul, star_smul,
    star_one, star_dualRailPlaneProj, star_dualRailRotGen, hc, hsin, Real.cos_neg, Real.sin_neg]
  push_cast
  module

/-- **The beamsplitter operator is unitary.** From `star B(θ) = B(-θ)` and the group law:
`star B(θ) · B(θ) = B(-θ) B(θ) = B(0) = 1`, and symmetrically on the other side. -/
theorem beamSplitterDualRailOp_mem_unitary (θ : ℝ) :
    beamSplitterDualRailOp θ ∈ unitary ((qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space) := by
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [star_beamSplitterDualRailOp, beamSplitterDualRailOp_comp, neg_add_cancel,
      beamSplitterDualRailOp_zero]
  · rw [star_beamSplitterDualRailOp, beamSplitterDualRailOp_comp, add_neg_cancel,
      beamSplitterDualRailOp_zero]

/-- The **beamsplitter** on a dual-rail single-photon qubit, as a closed-system `Evolution` of
`qubit ⊗ qubit` (Nielsen & Chuang §7.4.2). Its operator is the planar rotation
`beamSplitterDualRailOp θ`; unitarity is `beamSplitterDualRailOp_mem_unitary`. -/
def beamSplitterDualRail (θ : ℝ) : Evolution (qubit ⊗ qubit) where
  op := beamSplitterDualRailOp θ
  unitary := beamSplitterDualRailOp_mem_unitary θ

@[simp]
theorem beamSplitterDualRail_op (θ : ℝ) :
    (beamSplitterDualRail θ).op = beamSplitterDualRailOp θ := rfl

/-! ### Action of the beamsplitter -/

/-- **The beamsplitter's action on `|01⟩`:** `B(θ)|01⟩ = cos θ|01⟩ + sin θ|10⟩` (N&C 7.35). -/
theorem beamSplitterDualRailOp_apply_dualRailZero (θ : ℝ) :
    beamSplitterDualRailOp θ dualRailZero.vec
      = (Real.cos θ : ℂ) • dualRailZero.vec + (Real.sin θ : ℂ) • dualRailOne.vec := by
  rw [beamSplitterDualRailOp, dualRailPlaneProj, dualRailRotGen]
  simp only [add_apply, smul_apply,
    one_apply_eq_self, sub_apply, InnerProductSpace.rankOne_apply,
    dualRailZero_inner_self, dualRailOne_inner_dualRailZero, one_smul, zero_smul, add_zero,
    sub_zero]
  module

/-- **The beamsplitter's action on `|10⟩`:** `B(θ)|10⟩ = -sin θ|01⟩ + cos θ|10⟩` (N&C 7.35). -/
theorem beamSplitterDualRailOp_apply_dualRailOne (θ : ℝ) :
    beamSplitterDualRailOp θ dualRailOne.vec
      = -(Real.sin θ : ℂ) • dualRailZero.vec + (Real.cos θ : ℂ) • dualRailOne.vec := by
  rw [beamSplitterDualRailOp, dualRailPlaneProj, dualRailRotGen]
  simp only [add_apply, smul_apply,
    one_apply_eq_self, sub_apply, InnerProductSpace.rankOne_apply,
    dualRailOne_inner_self, dualRailZero_inner_dualRailOne, one_smul, zero_smul, zero_sub]
  module

/-- **The beamsplitter's action on a dual-rail superposition** (vector level):
`B(θ)(c₀|01⟩ + c₁|10⟩) = (cos θ·c₀ - sin θ·c₁)|01⟩ + (sin θ·c₀ + cos θ·c₁)|10⟩`. -/
theorem beamSplitterDualRailOp_apply_dualRailVec (θ : ℝ) (c0 c1 : ℂ) :
    beamSplitterDualRailOp θ (dualRailVec c0 c1)
      = dualRailVec ((Real.cos θ : ℂ) * c0 - (Real.sin θ : ℂ) * c1)
          ((Real.sin θ : ℂ) * c0 + (Real.cos θ : ℂ) * c1) := by
  rw [dualRailVec, dualRailVec, map_add, map_smul, map_smul,
    beamSplitterDualRailOp_apply_dualRailZero, beamSplitterDualRailOp_apply_dualRailOne]
  module

/-- **Norm preservation of the beamsplitter's amplitude rotation:** if `‖c₀‖² + ‖c₁‖² = 1` then the
rotated amplitudes `(cos θ·c₀ - sin θ·c₁, sin θ·c₀ + cos θ·c₁)` also satisfy the normalisation, as
the beamsplitter operator is unitary and the codewords are orthonormal. -/
theorem beamSplitterDualRail_rotation_normalized (θ : ℝ) (c0 c1 : ℂ)
    (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖(Real.cos θ : ℂ) * c0 - (Real.sin θ : ℂ) * c1‖ ^ 2
        + ‖(Real.sin θ : ℂ) * c0 + (Real.cos θ : ℂ) * c1‖ ^ 2 = 1 := by
  have hnorm : ‖dualRailVec ((Real.cos θ : ℂ) * c0 - (Real.sin θ : ℂ) * c1)
      ((Real.sin θ : ℂ) * c0 + (Real.cos θ : ℂ) * c1)‖ = 1 := by
    rw [← beamSplitterDualRailOp_apply_dualRailVec, ← beamSplitterDualRail_op,
      (beamSplitterDualRail θ).norm_op_apply]
    exact norm_dualRailVec c0 c1 h
  rw [← norm_dualRailVec_sq, hnorm, one_pow]

/-- **The beamsplitter's action on a dual-rail state** (Nielsen & Chuang eq. 7.35): it sends
`c₀|01⟩ + c₁|10⟩` to `(cos θ·c₀ - sin θ·c₁)|01⟩ + (sin θ·c₀ + cos θ·c₁)|10⟩`, the real rotation
`[[cos θ, -sin θ]; [sin θ, cos θ]]` of the logical amplitude vector `(c₀, c₁)`. -/
theorem beamSplitterDualRail_evolvePure_dualRail (θ : ℝ) (c0 c1 : ℂ)
    (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    (beamSplitterDualRail θ).evolvePure (dualRail c0 c1 h)
      = dualRail ((Real.cos θ : ℂ) * c0 - (Real.sin θ : ℂ) * c1)
          ((Real.sin θ : ℂ) * c0 + (Real.cos θ : ℂ) * c1)
          (beamSplitterDualRail_rotation_normalized θ c0 c1 h) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, dualRail_vec, dualRail_vec, beamSplitterDualRail_op]
  exact beamSplitterDualRailOp_apply_dualRailVec θ c0 c1

/-! ### Composition of beamsplitters -/

/-- **Composition of beamsplitters is angle addition** (as `Evolution`s):
`B(α) ∘ B(β) = B(α + β)`. -/
theorem beamSplitterDualRail_comp (α β : ℝ) :
    (beamSplitterDualRail α).comp (beamSplitterDualRail β) = beamSplitterDualRail (α + β) := by
  apply Evolution.ext
  rw [Evolution.comp_op, beamSplitterDualRail_op, beamSplitterDualRail_op, beamSplitterDualRail_op,
    ← ContinuousLinearMap.mul_def, beamSplitterDualRailOp_comp]

/-- **The zero-angle beamsplitter is the identity evolution.** -/
theorem beamSplitterDualRail_zero : beamSplitterDualRail 0 = Evolution.id := by
  apply Evolution.ext
  rw [beamSplitterDualRail_op, Evolution.id_op, beamSplitterDualRailOp_zero]

/-! ### The balanced Mach–Zehnder operator action -/

/-- **Congruence for `dualRailVec` in both amplitudes:** equal amplitudes give equal dual-rail
vectors. Used to reduce an equality of two dual-rail superpositions to the two scalar amplitude
equalities. -/
theorem dualRailVec_congr {a a' b b' : ℂ} (ha : a = a') (hb : b = b') :
    dualRailVec a b = dualRailVec a' b' := by rw [ha, hb]

/-- **The operator action of the balanced Mach–Zehnder composition** `B(-π/4) · P(φ) · B(π/4)` on a
dual-rail vector: it sends `c₀·|01⟩ + c₁·|10⟩` to the vector with amplitudes
`½((e^{iφ}+1)c₀ + (1-e^{iφ})c₁)` on `|01⟩` and `½((1-e^{iφ})c₀ + (e^{iφ}+1)c₁)` on `|10⟩`. Obtained
by applying the two beamsplitter rotations (`beamSplitterDualRailOp_apply_dualRailVec` at `±π/4`)
around the phase shifter (`phaseShiftGate_onRight_op_dualRailVec`) and collapsing
`cos(π/4) = sin(π/4) = √2/2`. The shared computational core of Nielsen & Chuang Exercise 7.10 part 2
(the circuit's `Evolution` is `machZehnder` in `AxQM/NC/Ch7/Exercise7_10.lean`), reused by both
the output normalisation and the `evolvePure` action there, mirroring how
`beamSplitterDualRailOp_apply_dualRailVec` is reused across this file. -/
theorem machZehnderDualRail_op_apply_dualRailVec (φ : ℝ) (c0 c1 : ℂ) :
    (beamSplitterDualRail (-(Real.pi / 4))).op
        (((phaseShiftGate φ).onRight qubit).op
          ((beamSplitterDualRail (Real.pi / 4)).op (dualRailVec c0 c1)))
      = dualRailVec
          (2⁻¹ * ((Complex.exp ((φ : ℂ) * Complex.I) + 1) * c0
            + (1 - Complex.exp ((φ : ℂ) * Complex.I)) * c1))
          (2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * Complex.I)) * c0
            + (Complex.exp ((φ : ℂ) * Complex.I) + 1) * c1)) := by
  simp only [beamSplitterDualRail_op]
  rw [beamSplitterDualRailOp_apply_dualRailVec, phaseShiftGate_onRight_op_dualRailVec,
    beamSplitterDualRailOp_apply_dualRailVec]
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt] <;> norm_num
  apply dualRailVec_congr
  · rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring_nf
    linear_combination
      (c0 * Complex.exp ((φ : ℂ) * Complex.I) / 4 + c0 / 4
        - c1 * Complex.exp ((φ : ℂ) * Complex.I) / 4 + c1 / 4) * h2
  · rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring_nf
    linear_combination
      (c0 / 4 - c0 * Complex.exp ((φ : ℂ) * Complex.I) / 4
        + c1 * Complex.exp ((φ : ℂ) * Complex.I) / 4 + c1 / 4) * h2

/-! ### The optical Hadamard on a dual-rail qubit -/

/-- **The logical zero `|0_L⟩ = |01⟩` as a `dualRail` state:** `dualRailZero = dualRail 1 0`. A
bridge from the named codeword to the amplitude-parametrised `dualRail 1 0`, so the beamsplitter /
phase-shifter action lemmas (stated for `dualRail c₀ c₁`) apply to the basis states. -/
theorem dualRailZero_eq_dualRail : dualRailZero = dualRail 1 0 (by norm_num) := by
  apply PureState.ext
  rw [dualRail_vec, dualRailVec]
  simp only [one_smul, zero_smul, add_zero]

/-- **The logical one `|1_L⟩ = |10⟩` as a `dualRail` state:** `dualRailOne = dualRail 0 1`. -/
theorem dualRailOne_eq_dualRail : dualRailOne = dualRail 0 1 (by norm_num) := by
  apply PureState.ext
  rw [dualRail_vec, dualRailVec]
  simp only [one_smul, zero_smul, zero_add]

/-- **The optical Hadamard gate** on a dual-rail single-photon qubit (Nielsen & Chuang p. 292,
Exercise 7.9): a `π` phase shifter on the second mode followed by a balanced `50/50` beamsplitter,
`H_opt = B(π/4) ∘ (1 ⊗ P(π))`, as an `Evolution` on `qubit ⊗ qubit`. This is the
optical realisation of the single-qubit Hadamard used throughout §7.4.2 — e.g. the `I ⊗ H` factors
flanking the Kerr medium in the `CNOT` construction (N&C eq. 7.46) — built entirely from a
beamsplitter and a phase shifter, with *no* Kerr nonlinearity. It is the `Evolution`-level companion
to the matrix identity `Concrete.opticalHadamardCircuit` (Exercise 7.9); its action on the logical
states is the Hadamard up to the overall phase `e^{iπ} = -1`
(`opticalHadamardDualRail_evolvePure_dualRail`). -/
def opticalHadamardDualRail : Evolution (qubit ⊗ qubit) :=
  (beamSplitterDualRail (Real.pi / 4)).comp ((phaseShiftGate Real.pi).onRight qubit)

/-- **Operator action of the optical Hadamard on a dual-rail superposition:** it sends
`c₀|01⟩ + c₁|10⟩` to `-(√2/2)(c₀ + c₁)|01⟩ - (√2/2)(c₀ - c₁)|10⟩` — the Hadamard amplitude map
`(c₀, c₁) ↦ ((c₀+c₁)/√2, (c₀-c₁)/√2)` times the global phase `e^{iπ} = -1`. (The `π` phase shifter
flips the `|01⟩` amplitude, `c₀ ↦ -c₀`; the balanced beamsplitter then mixes with
`cos(π/4) = sin(π/4) = √2/2`.) -/
theorem opticalHadamardDualRail_op_apply_dualRailVec (c0 c1 : ℂ) :
    opticalHadamardDualRail.op (dualRailVec c0 c1)
      = dualRailVec (-((Real.sqrt 2 : ℂ) / 2) * (c0 + c1))
          (-((Real.sqrt 2 : ℂ) / 2) * (c0 - c1)) := by
  rw [opticalHadamardDualRail, Evolution.comp_op, ContinuousLinearMap.comp_apply,
    phaseShiftGate_onRight_op_dualRailVec, beamSplitterDualRail_op,
    beamSplitterDualRailOp_apply_dualRailVec]
  apply dualRailVec_congr
  · rw [Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.exp_pi_mul_I]; push_cast; ring
  · rw [Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.exp_pi_mul_I]; push_cast; ring

/-- **The optical Hadamard preserves normalisation:** the transformed amplitudes
`(-(√2/2)(c₀+c₁), -(√2/2)(c₀-c₁))` again satisfy `‖·‖² + ‖·‖² = 1`, since `opticalHadamardDualRail`
is a unitary `Evolution` and the codewords are orthonormal (as for
`beamSplitterDualRail_rotation_normalized`). -/
theorem opticalHadamardDualRail_amplitudes_normalized (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖-((Real.sqrt 2 : ℂ) / 2) * (c0 + c1)‖ ^ 2 + ‖-((Real.sqrt 2 : ℂ) / 2) * (c0 - c1)‖ ^ 2
      = 1 := by
  have hnorm : ‖dualRailVec (-((Real.sqrt 2 : ℂ) / 2) * (c0 + c1))
      (-((Real.sqrt 2 : ℂ) / 2) * (c0 - c1))‖ = 1 := by
    rw [← opticalHadamardDualRail_op_apply_dualRailVec, opticalHadamardDualRail.norm_op_apply]
    exact norm_dualRailVec c0 c1 h
  rw [← norm_dualRailVec_sq, hnorm, one_pow]

/-- **The optical Hadamard realises the Hadamard on dual-rail states, up to global phase**
(Nielsen & Chuang Exercise 7.9): `H_opt(c₀|01⟩ + c₁|10⟩) = -(√2/2)(c₀+c₁)|01⟩ - (√2/2)(c₀-c₁)|10⟩`,
the Hadamard-transformed logical amplitudes `((c₀+c₁)/√2, (c₀-c₁)/√2)` times the overall phase
`e^{iπ} = -1`. The `Evolution` upgrade of the matrix identity `Concrete.opticalHadamardCircuit`
(Exercise 7.9): where the beamsplitter of Ex. 7.9 leaves the codespace at the matrix level, the
number-conserving `beamSplitterDualRail` keeps everything a genuine unitary on `qubit ⊗ qubit`, so
the optical Hadamard is a bona-fide `Evolution`. -/
theorem opticalHadamardDualRail_evolvePure_dualRail (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    opticalHadamardDualRail.evolvePure (dualRail c0 c1 h)
      = dualRail (-((Real.sqrt 2 : ℂ) / 2) * (c0 + c1)) (-((Real.sqrt 2 : ℂ) / 2) * (c0 - c1))
          (opticalHadamardDualRail_amplitudes_normalized c0 c1 h) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, dualRail_vec, dualRail_vec]
  exact opticalHadamardDualRail_op_apply_dualRailVec c0 c1

/-! ### The phase-shifter-free optical Hadamard: a beamsplitter and a mirror (Exercise 7.13, part 2)

Nielsen & Chuang Exercise 7.13 part (2) asks *why no phase shifters are necessary* in the optical
Deutsch–Jozsa construction. The answer is that the single-qubit Hadamard — the only element of the
construction that might seem to need one (Exercise 7.9 realises it as a beamsplitter after a `π`
phase shifter) — can equally be built from a beamsplitter and a **mirror**: the mode `SWAP`
(`Evolution.swap`) that a dual-rail qubit already needs for its `X` gate. Trading the `π` phase
shifter of `opticalHadamardDualRail` for that mirror gives `opticalHadamardMirror = SWAP ∘ B(π/4)`,
which realises the Hadamard **exactly** (no residual global phase), so the whole construction uses
only beamsplitters, mirrors, and Kerr media. -/

/-- **The mirror (mode `SWAP`) exchanges the amplitudes of a dual-rail superposition:**
`SWAP(c₀|01⟩ + c₁|10⟩) = c₁|01⟩ + c₀|10⟩`. A *mirror* swaps the two optical modes of a dual-rail
qubit (`Evolution.swap` on `qubit ⊗ qubit`), interchanging the codewords `|01⟩ ↔ |10⟩` and hence
their amplitudes. This is the dual-rail `X` gate — the same mirror the oracles use — recorded here
at the level of `dualRailVec` for the mirror-Hadamard below. -/
theorem swap_op_dualRailVec (c0 c1 : ℂ) :
    (Evolution.swap (S := qubit)).op (dualRailVec c0 c1) = dualRailVec c1 c0 := by
  simp only [dualRailVec, dualRailZero_vec, dualRailOne_vec, PureState.tmul_vec, map_add,
    ]
  rw [add_comm]
  erw [map_smul, map_smul]
  rw [Evolution.swap_op_tmul, Evolution.swap_op_tmul]

/-- **The phase-shifter-free optical Hadamard** on a dual-rail single-photon qubit (Nielsen & Chuang
Exercise 7.13, part 2): a balanced `50/50` beamsplitter followed by a **mirror** (the mode `SWAP`),
`H_mirror = SWAP ∘ B(π/4)`, as an `Evolution` on `qubit ⊗ qubit`. Unlike the
phase-shifter realisation `opticalHadamardDualRail = B(π/4) ∘ (1 ⊗ P(π))` (Exercise 7.9), this uses
**no phase shifter** — only a beamsplitter and a mirror, and that mirror (`Evolution.swap`) is
already the dual-rail `X` gate the oracle construction relies on. It realises the Hadamard *exactly*
(`opticalHadamardMirror_evolvePure_dualRail`), with no residual global phase, which is precisely why
no phase shifters are necessary (Exercise 7.13, part 2). -/
def opticalHadamardMirror : Evolution (qubit ⊗ qubit) :=
  (Evolution.swap (S := qubit)).comp (beamSplitterDualRail (Real.pi / 4))

/-- **Operator action of the mirror-Hadamard on a dual-rail superposition:** it sends
`c₀|01⟩ + c₁|10⟩` to `(√2/2)(c₀ + c₁)|01⟩ + (√2/2)(c₀ - c₁)|10⟩` — *exactly* the Hadamard amplitude
map `(c₀, c₁) ↦ ((c₀+c₁)/√2, (c₀-c₁)/√2)`, with no global phase. The beamsplitter rotates
`(c₀, c₁)` to `(√2/2)(c₀-c₁, c₀+c₁)` (`cos(π/4) = sin(π/4) = √2/2`) and the mirror then swaps the
two amplitudes. Contrast `opticalHadamardDualRail_op_apply_dualRailVec`, whose output carries the
extra `-1 = e^{iπ}` of the `π` phase shifter. -/
theorem opticalHadamardMirror_op_apply_dualRailVec (c0 c1 : ℂ) :
    opticalHadamardMirror.op (dualRailVec c0 c1)
      = dualRailVec ((Real.sqrt 2 : ℂ) / 2 * (c0 + c1)) ((Real.sqrt 2 : ℂ) / 2 * (c0 - c1)) := by
  rw [opticalHadamardMirror, Evolution.comp_op, ContinuousLinearMap.comp_apply,
    beamSplitterDualRail_op, beamSplitterDualRailOp_apply_dualRailVec, swap_op_dualRailVec]
  apply dualRailVec_congr
  · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
  · rw [Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring

/-- **The mirror-Hadamard preserves normalisation:** the transformed amplitudes
`((√2/2)(c₀+c₁), (√2/2)(c₀-c₁))` again satisfy `‖·‖² + ‖·‖² = 1`, since `opticalHadamardMirror` is a
unitary `Evolution` (a beamsplitter composed with the `SWAP`) and the codewords are orthonormal. -/
theorem opticalHadamardMirror_amplitudes_normalized (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖(Real.sqrt 2 : ℂ) / 2 * (c0 + c1)‖ ^ 2 + ‖(Real.sqrt 2 : ℂ) / 2 * (c0 - c1)‖ ^ 2 = 1 := by
  have hnorm : ‖dualRailVec ((Real.sqrt 2 : ℂ) / 2 * (c0 + c1))
      ((Real.sqrt 2 : ℂ) / 2 * (c0 - c1))‖ = 1 := by
    rw [← opticalHadamardMirror_op_apply_dualRailVec, opticalHadamardMirror.norm_op_apply]
    exact norm_dualRailVec c0 c1 h
  rw [← norm_dualRailVec_sq, hnorm, one_pow]

/-- **The mirror-Hadamard realises the Hadamard on dual-rail states, exactly** (Nielsen & Chuang
Exercise 7.13, part 2): `H_mirror(c₀|01⟩ + c₁|10⟩) = (√2/2)(c₀+c₁)|01⟩ + (√2/2)(c₀-c₁)|10⟩`, the
Hadamard-transformed amplitudes `((c₀+c₁)/√2, (c₀-c₁)/√2)` with *no* global phase — a strictly
cleaner realisation than the phase-shifter version `opticalHadamardDualRail` (whose action carries
the phase `e^{iπ} = -1`), obtained by trading the `π` phase shifter for a mirror. -/
theorem opticalHadamardMirror_evolvePure_dualRail (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    opticalHadamardMirror.evolvePure (dualRail c0 c1 h)
      = dualRail ((Real.sqrt 2 : ℂ) / 2 * (c0 + c1)) ((Real.sqrt 2 : ℂ) / 2 * (c0 - c1))
          (opticalHadamardMirror_amplitudes_normalized c0 c1 h) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, dualRail_vec, dualRail_vec]
  exact opticalHadamardMirror_op_apply_dualRailVec c0 c1

end AxQM
