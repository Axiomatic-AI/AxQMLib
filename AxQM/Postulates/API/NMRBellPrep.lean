/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRControlledZ
import AxQM.Postulates.API.HadamardABC
import AxQM.Concrete.NMRPulsePhases

/-!
# AxQM.Postulates.API — the NMR Bell-preparation circuit (N&C Ex 7.48)

The construction of the **bottom-left circuit of Nielsen & Chuang Figure 7.19**
(§7.7.3, p. 338): the NMR pulse sequence that creates the Bell state `(|00⟩ − |11⟩)/√2` from the
computational `|00⟩` input, built from the same pieces as the controlled-`Z`/CNOT circuit of
Exercise 7.41 (`AxQM/Postulates/API/NMRControlledZ.lean`).

## The circuit (Figure 7.19, bottom-left)

Reading left to right, the two-qubit circuit is

* an `R_x(π/2)` (`90°` `x̂`-rotation) on **each** spin,
* one period of the `Z₁Z₂`-coupled free evolution
  `e^{-iH/2ℏJ} = (couplingZZHamiltonian c).propagator 1 0 t` (the identical physical box of
  Exercise 7.41, with `c·t = π/4`, i.e. `exp(-i(π/4) Z₁Z₂)`),
* an `R_y(-π/2)` (`90°` `ŷ`-rotation, the "barred" `R̄_y` pulse) on the **second** spin only.

That is `nmrBellCircuit c t = (1 ⊗ R_y(-π/2)) · exp(-i(π/4) Z₁Z₂) · (R_x(π/2) ⊗ R_x(π/2))`.

## The sign convention (fidelity note)

The joint sign convention of the `90°` pulses and the coupling box is *not* pinned by the figure
(the RF-pulse phase sets the rotation handedness). We fix the coupling box to the physically
standard `exp(-i(π/4) Z₁Z₂)` — positive free evolution under `H = +c Z₁Z₂`, and the *identical* box
already used for the controlled-`Z`/CNOT circuit in Exercise 7.41 — and then the final `y`-pulse
handedness that yields *exactly* the advertised `(|00⟩ − |11⟩)/√2` is `R_y(-π/2)`. (The opposite
box-sign convention would instead pair with `R_y(+π/2)`; either is faithful, differing only by the
unobservable global phase.) With this choice the circuit produces the target up to `e^{-iπ/4}`.

## What is here

* `nmrBellCircuit c t` — the circuit as an `Evolution (qubit ⊗ qubit)`.
* The **verified action of each stage** on the computational basis — the pulses
  `rotXGate_piDivTwo_op_qubitBasisZero`, `rotYGate_negPiDivTwo_op_qubitBasis{Zero,One}`, and the
  diagonal coupled free-evolution box `couplingBox_op_qubitBasis` (the `(1∓i)/√2` phase table). The
  reusable `ℂ`-arithmetic bridges these consume — `cos/sin(±π/2/2)` and the `e^{∓iπ/4}` closed forms
  — live in the shared `AxQM/Concrete/NMRPulsePhases.lean`.

* The **assembled result** `nmrBellCircuit_op_qubitBasisZeroZero`:
  `nmrBellCircuit c t |00⟩ = e^{-iπ/4} • (bellState 1 0).vec` (for `c·t = π/4`) — the four stages
  composed by linearity, verifying `|00⟩ ↦ e^{-iπ/4}(|00⟩ − |11⟩)/√2 = e^{-iπ/4}|β₁₀⟩` exactly
  (`R_x` gives `(|0⟩−i|1⟩)/√2` on each spin, the box multiplies the four branches by `(1∓i)/√2`, and
  `R_y(-π/2)` on the second spin interferes them, cancelling `|01⟩`/`|10⟩`).

The assembly threads every stage through the computational product basis
`((qubitBasis a).tmul (qubitBasis b)).vec` — whose `•`/`+`/`-` live at the composite-system head,
so each `Evolution.op` distributes by a plain `map_smul`/`map_sub` — and reduces `bellBasisVec`'s
bit-flip index `qubitBasis (0+1)` to `qubitBasis 1` before `match_scalars`, so the `|11⟩` atoms
unify syntactically; the residual scalar identity then closes on `invSqrt2 ^ 2 = 2⁻¹` and
`I ^ 2 = -1`. The physical statement — the output density operator equals `|β₁₀⟩⟨β₁₀|`,
the global phase `e^{-iπ/4}` washing out — is the statement of Exercise 7.48 in
`AxQM/NC/Ch7/Exercise7_48.lean`.
-/

open scoped InnerProductSpace TensorProduct

open Complex (I)

noncomputable section

namespace AxQM

/-! ### Single-qubit pulse actions on the computational basis -/

/-- **`R_x(π/2)|0⟩ = (|0⟩ − i|1⟩)/√2`.** The `90°` `x̂`-pulse on `|0⟩`, column `0` of the concrete
matrix `R_x(π/2) = !![cos(π/4), -i sin(π/4); …]` via `Matrix.ofLp_toEuclideanCLM`. -/
theorem rotXGate_piDivTwo_op_qubitBasisZero :
    (rotXGate (Real.pi / 2)).op (qubitBasis 0).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec - Complex.I • (qubitBasis 1).vec) := by
  rw [rotXGate_op]
  simp only [qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotX (Real.pi / 2)))
        (EuclideanSpace.single 0 1)).ofLp
      = (Concrete.invSqrt2 • (EuclideanSpace.single 0 1
          - Complex.I • EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.rotX_eq, Matrix.mulVec, dotProduct, EuclideanSpace.single,
        Concrete.cos_pi_div_two_div_two, Concrete.sin_pi_div_two_div_two]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **`R_y(-π/2)|0⟩ = (|0⟩ − |1⟩)/√2`.** The barred `90°` `ŷ`-pulse on `|0⟩`, column `0` of
`R_y(-π/2)`. -/
theorem rotYGate_negPiDivTwo_op_qubitBasisZero :
    (rotYGate (-(Real.pi / 2))).op (qubitBasis 0).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec - (qubitBasis 1).vec) := by
  rw [rotYGate_op]
  simp only [qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY (-(Real.pi / 2))))
        (EuclideanSpace.single 0 1)).ofLp
      = (Concrete.invSqrt2 • (EuclideanSpace.single 0 1
          - EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.rotY_eq, Matrix.mulVec, dotProduct, EuclideanSpace.single,
        Concrete.cos_neg_pi_div_two_div_two,
        Concrete.sin_neg_pi_div_two_div_two]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **`R_y(-π/2)|1⟩ = (|0⟩ + |1⟩)/√2`.** The barred `90°` `ŷ`-pulse on `|1⟩`, column `1` of
`R_y(-π/2)`. -/
theorem rotYGate_negPiDivTwo_op_qubitBasisOne :
    (rotYGate (-(Real.pi / 2))).op (qubitBasis 1).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec + (qubitBasis 1).vec) := by
  rw [rotYGate_op]
  simp only [qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY (-(Real.pi / 2))))
        (EuclideanSpace.single 1 1)).ofLp
      = (Concrete.invSqrt2 • (EuclideanSpace.single 0 1
          + EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.rotY_eq, Matrix.mulVec, dotProduct, EuclideanSpace.single,
        Concrete.cos_neg_pi_div_two_div_two,
        Concrete.sin_neg_pi_div_two_div_two]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-! ### The coupled free-evolution box on the computational basis -/

/-- **Diagonal action of the coupling box on `|a⟩⊗|b⟩`.** For `c·t = π/4` the free evolution
`exp(-i(π/4) Z₁Z₂)` sends `|a⟩⊗|b⟩` to `e^{-i(π/4)(-1)^{a+b}} |a⟩⊗|b⟩`, in closed form
`(invSqrt2 · (1 − (-1)^{a+b} i)) |a⟩⊗|b⟩`: `(1−i)/√2` on the diagonal `|00⟩,|11⟩`, `(1+i)/√2` on the
antidiagonal `|01⟩,|10⟩`. -/
theorem couplingBox_op_qubitBasis (c t : ℝ) (h : c * t = Real.pi / 4) (a b : Fin 2) :
    ((couplingZZHamiltonian c).propagator 1 0 t).op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (Concrete.invSqrt2 - (-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * Concrete.invSqrt2 * Complex.I)
        • ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec) := by
  have key := Observable.propagator_op_apply_of_apply_eq_smul (couplingZZHamiltonian c) t
    (couplingZZHamiltonian_op_apply_qubitBasis c a b)
  rw [PureState.tmul_vec] at key
  rw [key]
  congr 1
  have hct : ((c : ℂ) * (t : ℂ)) = (Real.pi : ℂ) / 4 := by
    rw [← Complex.ofReal_mul, h]; push_cast; ring
  rw [show ((c : ℂ) * (-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ (b : ℕ)) * (t : ℂ)
        = (-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * ((c : ℂ) * (t : ℂ)) by rw [pow_add]; ring, hct]
  rcases Nat.even_or_odd ((a : ℕ) + (b : ℕ)) with he | ho
  · simp only [Even.neg_one_pow he, one_mul]
    exact Concrete.exp_neg_pi_div_four_mul_I
  · simp only [Odd.neg_one_pow ho]
    rw [show -(Complex.I * ((-1 : ℂ) * ((Real.pi : ℂ) / 4))) = Complex.I * ((Real.pi : ℂ) / 4) by
          ring, Concrete.exp_pi_div_four_mul_I]
    ring

/-! ### The circuit and its action -/

/-- **The NMR Bell-preparation circuit** (Nielsen & Chuang Figure 7.19, bottom-left; Exercise 7.48):
`(1 ⊗ R_y(-π/2)) · exp(-i(π/4) Z₁Z₂) · (R_x(π/2) ⊗ R_x(π/2))` — an `R_x(π/2)` on each spin, one
period of the `Z₁Z₂`-coupled free evolution, then an `R_y(-π/2)` on the second spin. Applied to
`|00⟩` it creates the Bell state `(|00⟩ − |11⟩)/√2` up to the global phase `e^{-iπ/4}` (see the
module docstring). -/
def nmrBellCircuit (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotYGate (-(Real.pi / 2))).onRight qubit).comp
    (((couplingZZHamiltonian c).propagator 1 0 t).comp
      (((rotXGate (Real.pi / 2)).onLeft qubit).comp
        ((rotXGate (Real.pi / 2)).onRight qubit)))

/-- **Exercise 7.48: the NMR circuit creates the Bell state `|β₁₀⟩`, up to the global phase
`e^{-iπ/4}`.** With `c·t = π/4`, pushing `|00⟩` through the four stages of `nmrBellCircuit` yields
`nmrBellCircuit c t |00⟩ = e^{-iπ/4} • (bellState 1 0).vec = e^{-iπ/4} (|00⟩ − |11⟩)/√2`.

The proof assembles the verified single-stage actions:
* `R_x(π/2) ⊗ R_x(π/2)` sends `|00⟩` to `½(|00⟩ − i|01⟩ − i|10⟩ − |11⟩)`
  (`rotXGate_piDivTwo_op_qubitBasisZero` on each factor, distributed over the product basis);
* the coupling box multiplies each `|a⟩⊗|b⟩` by `(1 − (-1)^{a+b} i)/√2`
  (`couplingBox_op_qubitBasis`);
* `R_y(-π/2)` on the second spin (`rotYGate_negPiDivTwo_op_qubitBasis{Zero,One}`) interferes the
  four branches, cancelling the `|01⟩`/`|10⟩` amplitudes and leaving `e^{-iπ/4}(|00⟩ − |11⟩)/√2`.

Each stage is threaded through the computational product basis
`((qubitBasis a).tmul (qubitBasis b)).vec` (whose `•`/`+`/`-` live at the composite-system head, so
the linearity of each `Evolution.op` fires), and the residual scalar identity closes on
`Concrete.invSqrt2 ^ 2 = 2⁻¹` and `Complex.I ^ 2 = -1`. -/
theorem nmrBellCircuit_op_qubitBasisZeroZero (c t : ℝ) (h : c * t = Real.pi / 4) :
    (nmrBellCircuit c t).op ((qubitBasis 0).tmul (qubitBasis 0)).vec
      = Complex.exp (-(Complex.I * ((Real.pi : ℂ) / 4))) • (bellState 1 0).vec := by
  -- The coupled free-evolution box acts diagonally on each computational product-basis atom.
  have hbox : ∀ a b : Fin 2,
      ((couplingZZHamiltonian c).propagator 1 0 t).op ((qubitBasis a).tmul (qubitBasis b)).vec
        = (Concrete.invSqrt2 - (-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * Concrete.invSqrt2 * Complex.I)
          • ((qubitBasis a).tmul (qubitBasis b)).vec := by
    intro a b
    rw [PureState.tmul_vec, couplingBox_op_qubitBasis c t h a b, ← PureState.tmul_vec]
    rfl
  -- `R_y(-π/2)` on the second spin of each atom (`|b=0⟩ ↦ (|0⟩−|1⟩)/√2`, `|b=1⟩ ↦ (|0⟩+|1⟩)/√2`).
  have hry0 : ∀ a : Fin 2,
      ((rotYGate (-(Real.pi / 2))).onRight qubit).op ((qubitBasis a).tmul (qubitBasis 0)).vec
        = Concrete.invSqrt2 • (((qubitBasis a).tmul (qubitBasis 0)).vec
            - ((qubitBasis a).tmul (qubitBasis 1)).vec) := by
    intro a
    rw [PureState.tmul_vec, Evolution.onRight_op_tmul, rotYGate_negPiDivTwo_op_qubitBasisZero,
      TensorProduct.tmul_smul, TensorProduct.tmul_sub, ← PureState.tmul_vec, ← PureState.tmul_vec]
    rfl
  have hry1 : ∀ a : Fin 2,
      ((rotYGate (-(Real.pi / 2))).onRight qubit).op ((qubitBasis a).tmul (qubitBasis 1)).vec
        = Concrete.invSqrt2 • (((qubitBasis a).tmul (qubitBasis 0)).vec
            + ((qubitBasis a).tmul (qubitBasis 1)).vec) := by
    intro a
    rw [PureState.tmul_vec, Evolution.onRight_op_tmul, rotYGate_negPiDivTwo_op_qubitBasisOne,
      TensorProduct.tmul_smul, TensorProduct.tmul_add, ← PureState.tmul_vec, ← PureState.tmul_vec]
    rfl
  -- Stage 1: `R_x(π/2) ⊗ R_x(π/2)` on `|00⟩`, expanded over the product basis.
  have hstage1 :
      ((rotXGate (Real.pi / 2)).onLeft qubit).op
        (((rotXGate (Real.pi / 2)).onRight qubit).op ((qubitBasis 0).tmul (qubitBasis 0)).vec)
        = (2 : ℂ)⁻¹
          • (((qubitBasis 0).tmul (qubitBasis 0)).vec
              - Complex.I • ((qubitBasis 0).tmul (qubitBasis 1)).vec
              - Complex.I • ((qubitBasis 1).tmul (qubitBasis 0)).vec
              - ((qubitBasis 1).tmul (qubitBasis 1)).vec) := by
    -- Prove it over the raw tensor head, then transport across the (defeq) composite head.
    have hraw :
        ((rotXGate (Real.pi / 2)).onLeft qubit).op
          (((rotXGate (Real.pi / 2)).onRight qubit).op ((qubitBasis 0).tmul (qubitBasis 0)).vec)
          = (2 : ℂ)⁻¹
            • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
                - Complex.I • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec)
                - Complex.I • ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec)
                - (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec) := by
      rw [PureState.tmul_vec, Evolution.onRight_op_tmul, rotXGate_piDivTwo_op_qubitBasisZero,
        Evolution.onLeft_op_tmul, rotXGate_piDivTwo_op_qubitBasisZero, TensorProduct.smul_tmul_smul,
        Concrete.invSqrt2_mul_self]
      congr 1
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub, smul_sub, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', smul_smul, Complex.I_mul_I, neg_one_smul, TensorProduct.neg_tmul]
      abel
    exact hraw
  -- Compose the four stages by linearity and collapse the interference.
  rw [nmrBellCircuit, Evolution.comp_op, Evolution.comp_op, Evolution.comp_op,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hstage1, map_smul, map_smul]
  simp only [map_sub, map_smul, hbox]
  rw [hry0 0, hry1 0, hry0 1, hry1 1, bellState_vec, bellBasisVec,
    Concrete.exp_neg_pi_div_four_mul_I]
  simp only [show ((0 : Fin 2) + 1) = 1 from rfl, Fin.val_zero, Fin.val_one, pow_one,
    show ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = Concrete.invSqrt2 from rfl]
  match_scalars <;>
    · ring_nf
      simp only [Complex.I_sq, Concrete.invSqrt2_sq]
      ring

end AxQM
