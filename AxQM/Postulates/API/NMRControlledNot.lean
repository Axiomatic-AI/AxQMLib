/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRControlledZ
import AxQM.Postulates.API.HadamardRotation
import AxQM.Postulates.API.HadamardABC
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Postulates.API — the NMR controlled-`NOT` (N&C Ex 7.47)

The **controlled-`NOT` circuit of Figure 7.19** (top left): a
`90°` `y`-pulse on the target spin, one period of `Z₁Z₂`-coupled evolution `exp(-i c Z₁Z₂ t)`, then
a `90°` `x`-pulse on the target. The statement of Exercise 7.47 is in
`AxQM/NC/Ch7/Exercise7_47.lean`.

## What is here

* `couplingZZ_propagator_op_tmul` — the **controlled-`R_z` reduction**: on the control block `|a⟩`,
  the `Z₁Z₂` coupling `exp(-i c Z₁Z₂ t)` acts on the target as the single-qubit `z`-rotation
  `R_z((-1)ᵃ·2ct)`. This is what collapses the whole two-qubit computation to single-qubit `2×2`
  matrices.  (`couplingZZ_key` is its computational-basis special case.)
* `nmrCnotCircuit c t` — the **Fig 7.19 circuit** `R_x(π/2)₂ ∘ exp(-i c Z₁Z₂ t) ∘ R_y(π/2)₂` and
  its factorisation `nmrCnotCircuit_op_apply_qubitBasis` on `|a⟩⊗|b⟩` into a control `|a⟩`
  untouched, tensored with the target single-qubit sandwich `R_x(π/2)·R_z((-1)ᵃ·2ct)·R_y(π/2)`.
* `nmrCnotPhase`, `nmr_target_op_apply` — the target sandwich at `c·t = π/4` is `(phase)·Xᵃ`
  (diagonal for `a = 0`, an `X`-flip for `a = 1`), with the unit-modulus scalar `nmrCnotPhase a b`.
* `nmrCnotCircuit_op_apply_phase` — the main result: at `c·t = π/4`, `nmrCnotCircuit c t` sends
  `|a⟩⊗|b⟩` to `(nmrCnotPhase a b)·|a⟩⊗|a⊕b⟩`, i.e. it is a controlled-`NOT` up to single-qubit
  phases on classical inputs.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Computational-basis form of the controlled-`R_z` reduction.** On `|a⟩⊗|b⟩` the `Z₁Z₂` coupling
propagator acts by the same scalar as the target `z`-rotation `R_z((-1)ᵃ·2ct)` acting on `|b⟩`: both
are the phase `e^{-i c (-1)ᵃ(-1)ᵇ t}`. The eigenvector input to the `∀ ψ` lemma
`couplingZZ_propagator_op_tmul`. -/
theorem couplingZZ_key (c t : ℝ) (a b : Fin 2) :
    ((couplingZZHamiltonian c).propagator 1 0 t).op
        ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (qubitBasis a).vec ⊗ₜ[ℂ]
          ((rotZGate ((-1) ^ (a : ℕ) * (2 * c * t))).op (qubitBasis b).vec) := by
  have hev := Observable.propagator_op_apply_of_apply_eq_smul (couplingZZHamiltonian c) t
    (couplingZZHamiltonian_op_apply_qubitBasis c a b)
  rw [PureState.tmul_vec] at hev
  rw [hev, rotZGate_op_apply_qubitBasis, TensorProduct.tmul_smul]
  congr 1
  fin_cases b
  · simp only [Fin.mk_zero, Fin.isValue]
    rw [Concrete.rotZ_apply_zero_zero]
    congr 1
    push_cast
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [Concrete.rotZ_apply_one_one]
    congr 1
    push_cast
    ring

/-- **Controlled-`R_z` reduction.** The `Z₁Z₂` coupling propagator, restricted to the control block
`|a⟩`, acts on the target as the single-qubit `z`-rotation `R_z((-1)ᵃ·2ct)`: for every target vector
`ψ`, `exp(-i c Z₁Z₂ t)(|a⟩⊗ψ) = |a⟩⊗(R_z((-1)ᵃ·2ct) ψ)`. Proved by extending the computational-basis
identity `couplingZZ_key` linearly in `ψ` (`Module.Basis.ext` on the qubit basis). -/
theorem couplingZZ_propagator_op_tmul (c t : ℝ) (a : Fin 2) (ψ : (qubit).space) :
    ((couplingZZHamiltonian c).propagator 1 0 t).op ((qubitBasis a).vec ⊗ₜ[ℂ] ψ)
      = (qubitBasis a).vec ⊗ₜ[ℂ] ((rotZGate ((-1) ^ (a : ℕ) * (2 * c * t))).op ψ) := by
  have hlin :
      (((couplingZZHamiltonian c).propagator 1 0 t).op.toLinearMap ∘ₗ
          TensorProduct.mk ℂ (qubit).space (qubit).space ((qubitBasis a).vec))
        = ((TensorProduct.mk ℂ (qubit).space (qubit).space ((qubitBasis a).vec)) ∘ₗ
          (rotZGate ((-1) ^ (a : ℕ) * (2 * c * t))).op.toLinearMap) := by
    apply Module.Basis.ext (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
    intro b
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, ← qubitBasis_vec]
    exact couplingZZ_key c t a b
  exact LinearMap.congr_fun hlin ψ

/-- **The Fig 7.19 (top left) NMR controlled-`NOT` circuit.** On the target (right) spin: a `90°`
`y`-rotation `R_y(π/2)`, then one period of `Z₁Z₂`-coupled evolution
`(couplingZZHamiltonian c).propagator 1 0 t`, then a `90°` `x`-rotation `R_x(π/2)`. When `c·t = π/4`
this performs a controlled-`NOT` up to single-qubit phases (see `AxQM/NC/Ch7/Exercise7_47.lean`). -/
def nmrCnotCircuit (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotXGate (Real.pi / 2)).onRight qubit).comp
    (((couplingZZHamiltonian c).propagator 1 0 t).comp
      ((rotYGate (Real.pi / 2)).onRight qubit))

/-- **Action of the Fig 7.19 circuit as a target-qubit sandwich.** Because the coupling reduces to a
target `R_z` on each control block (`couplingZZ_propagator_op_tmul`), the whole circuit factors on a
computational-basis input `|a⟩⊗|b⟩` as the control `|a⟩` unchanged, tensored with the single-qubit
sandwich `R_x(π/2)·R_z((-1)ᵃ·2ct)·R_y(π/2)` applied to the target `|b⟩`. -/
theorem nmrCnotCircuit_op_apply_qubitBasis (c t : ℝ) (a b : Fin 2) :
    (nmrCnotCircuit c t).op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (qubitBasis a).vec ⊗ₜ[ℂ]
          ((rotXGate (Real.pi / 2)).op
            ((rotZGate ((-1) ^ (a : ℕ) * (2 * c * t))).op
              ((rotYGate (Real.pi / 2)).op (qubitBasis b).vec))) := by
  change ((rotXGate (Real.pi / 2)).onRight qubit).op
      (((couplingZZHamiltonian c).propagator 1 0 t).op
        (((rotYGate (Real.pi / 2)).onRight qubit).op
          ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)))
      = (qubitBasis a).vec ⊗ₜ[ℂ]
          ((rotXGate (Real.pi / 2)).op
            ((rotZGate ((-1) ^ (a : ℕ) * (2 * c * t))).op
              ((rotYGate (Real.pi / 2)).op (qubitBasis b).vec)))
  rw [Evolution.onRight_op_tmul, couplingZZ_propagator_op_tmul, Evolution.onRight_op_tmul]

/-- The single-qubit phase picked up by the target in the Fig 7.19 circuit at `c·t = π/4`, one of
the four unit-modulus scalars `e^{-iπ/4}, e^{iπ/4}, e^{-iπ/4}, e^{-3iπ/4}` (given in rectangular
form `(√2/2)(±1 ± i)`). These are exactly the phases that a subsequent single-qubit `R_z` correction
removes to turn the circuit into a proper controlled-`NOT`. -/
def nmrCnotPhase (a b : Fin 2) : ℂ :=
  !![(↑(Real.sqrt 2) / 2 : ℂ) - (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I,
        (↑(Real.sqrt 2) / 2 : ℂ) + (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I;
      (↑(Real.sqrt 2) / 2 : ℂ) - (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I,
        -(↑(Real.sqrt 2) / 2 : ℂ) - (↑(Real.sqrt 2) / 2 : ℂ) * Complex.I] a b

-- The unused-tactic linter misreports the `try nlinarith` below: without it `nlinarith` runs on
-- goals `simp` already closed.
set_option linter.unusedTactic false in
/-- **The target single-qubit sandwich is `(phase)·Xᵃ`.** At the coupling period `c·t = π/4` (so
the `R_z` angle is `(-1)ᵃ·π/2`), the composite `R_x(π/2)·R_z((-1)ᵃ·π/2)·R_y(π/2)` sends the target
`|b⟩` to `nmrCnotPhase a b · |a⊕b⟩`: for control `a = 0` a diagonal phase (`a + b = b`), for `a = 1`
a target flip (`a + b = b ⊕ 1`). Proved by reducing the three gate operators to one concrete `2×2`
matrix product via `Matrix.toEuclideanCLM` and evaluating each of the eight entries at `π/4`. -/
theorem nmr_target_op_apply (a b : Fin 2) :
    (rotXGate (Real.pi / 2)).op
        ((rotZGate ((-1 : ℝ) ^ (a : ℕ) * (Real.pi / 2))).op
          ((rotYGate (Real.pi / 2)).op (qubitBasis b).vec))
      = nmrCnotPhase a b • (qubitBasis (a + b)).vec := by
  rw [rotXGate_op, rotZGate_op, rotYGate_op, qubitBasis_vec]
  have hcc : Complex.cos ((↑Real.pi / 2 / 2 : ℂ)) = ↑(Real.sqrt 2) / 2 := by
    rw [show (↑Real.pi / 2 / 2 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_pi_div_four]; push_cast; ring
  have hsc : Complex.sin ((↑Real.pi / 2 / 2 : ℂ)) = ↑(Real.sqrt 2) / 2 := by
    rw [show (↑Real.pi / 2 / 2 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin, Real.sin_pi_div_four]; push_cast; ring
  have he0m : Complex.exp (-((↑Real.pi / 2 / 2 : ℂ) * Complex.I))
      = ↑(Real.sqrt 2) / 2 - ↑(Real.sqrt 2) / 2 * Complex.I := by
    rw [show (-((↑Real.pi / 2 / 2 : ℂ) * Complex.I)) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
  have he0p : Complex.exp ((↑Real.pi / 2 / 2 : ℂ) * Complex.I)
      = ↑(Real.sqrt 2) / 2 + ↑(Real.sqrt 2) / 2 * Complex.I := by
    rw [show ((↑Real.pi / 2 / 2 : ℂ) * Complex.I) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
  have he1m : Complex.exp (-(↑Real.pi / 2 : ℂ) / 2 * Complex.I)
      = ↑(Real.sqrt 2) / 2 - ↑(Real.sqrt 2) / 2 * Complex.I := by
    rw [show (-(↑Real.pi / 2 : ℂ) / 2 * Complex.I) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
  have he1p : Complex.exp (-(-(↑Real.pi / 2 : ℂ) / 2 * Complex.I))
      = ↑(Real.sqrt 2) / 2 + ↑(Real.sqrt 2) / 2 * Complex.I := by
    rw [show (-(-(↑Real.pi / 2 : ℂ) / 2 * Complex.I)) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
  have hof :
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotX (Real.pi / 2)))
          ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
              (Concrete.rotZ ((-1 : ℝ) ^ (a : ℕ) * (Real.pi / 2))))
            ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY (Real.pi / 2)))
              (EuclideanSpace.single b 1)))).ofLp
        = (nmrCnotPhase a b •
            (EuclideanSpace.single (a + b) 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases a <;> fin_cases b <;> fin_cases j <;>
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one,
          Fin.isValue, Fin.reduceAdd, Concrete.rotX_eq, Concrete.rotY_eq, Concrete.rotZ_eq,
          Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_ofNat,
          Complex.ofReal_neg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, EuclideanSpace.single, PiLp.single_apply,
          PiLp.smul_apply, Finset.sum_ite_eq', Finset.mem_univ, nmrCnotPhase, pow_zero, pow_one,
          neg_mul, mul_neg, neg_neg, neg_zero, one_mul, mul_one, mul_zero, zero_mul, add_zero,
          zero_add, mul_ite, one_ne_zero, zero_ne_one, smul_eq_mul, ↓reduceIte,
          hcc, hsc, he0m, he0p, he1m, he1p]
        rw [Complex.ext_iff]
        refine ⟨?_, ?_⟩ <;>
          (simp; try nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2])
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The Fig 7.19 circuit acts as a controlled-`NOT` up to single-qubit phases on the computational
basis.** For one coupling period `c·t = π/4`, `nmrCnotCircuit c t` sends `|a⟩⊗|b⟩` to
`(phase)·|a⟩⊗|a⊕b⟩`: the target is flipped exactly when the control is `|1⟩` (as `a + b` is `b` for
`a = 0` and `b ⊕ 1` for `a = 1`), each computational-basis input acquiring the unit-modulus scalar
`nmrCnotPhase a b`. This is the precise sense in which the circuit "acts properly on classical input
states" (N&C Exercise 7.47). -/
theorem nmrCnotCircuit_op_apply_phase (c t : ℝ) (h : c * t = Real.pi / 4) (a b : Fin 2) :
    (nmrCnotCircuit c t).op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = nmrCnotPhase a b • ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis (a + b)).vec) := by
  have h2 : (2 : ℝ) * c * t = Real.pi / 2 := by rw [mul_assoc, h]; ring
  rw [nmrCnotCircuit_op_apply_qubitBasis, h2, nmr_target_op_apply, TensorProduct.tmul_smul]

/-- **Computational-basis action of the CNOT gate.** `cnotGate` sends `|a⟩⊗|b⟩` to `|a⟩⊗|a⊕b⟩`,
i.e. it flips the target iff the control is `|1⟩` (`a + b = b` for `a = 0`, `b ⊕ 1` for `a = 1`).
The target of `nmrCnotCircuit_op_apply_phase`. The operator-level form of the CNOT truth table
`cnotGate_evolvePure_qubitBasis` (`t ⊕ c` reindexed to `a ⊕ b` via `add_comm`). -/
theorem cnotGate_op_apply_qubitBasis (a b : Fin 2) :
    cnotGate.op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis (a + b)).vec := by
  rw [← PureState.tmul_vec, ← Evolution.evolvePure_vec, cnotGate_evolvePure_qubitBasis,
    PureState.tmul_vec, add_comm]

end AxQM
