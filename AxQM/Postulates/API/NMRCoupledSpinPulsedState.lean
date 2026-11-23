/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRCoupledSpinFID
import AxQM.Postulates.API.HighTempThermalState
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy

/-!
# AxQM.Postulates.API — the coupled two-spin NMR thermal equilibrium state

The **thermal equilibrium state** of the two-spin, `J`-coupled NMR system of Nielsen & Chuang
Exercise 7.37, on the two-qubit system `qubit.compose qubit`. In the high-temperature approximation
(N&C eq. 7.140) it is

`ρ_th = ¼(I − βℏω(Z₁ + Z₂))`,

the first-order Gibbs state of the Zeeman Hamiltonian `H_Z = ℏω(Z₁ + Z₂)` (both spins at the same
Larmor frequency `ω`, as in Exercise 7.37). This module builds `ρ_th` as a genuine `State` and
records its density operator in closed form; the `90°` read pulse turning it into the exercise's
`ρ = e^{iπY₁/4} ρ_th e^{−iπY₁/4}` is `nmrCoupledPairPulsedState` below.

* `nmrCoupledPairZeeman ℏ ω` — the two-spin Zeeman Hamiltonian `H_Z = ℏω(Z₁ + Z₂)`.
* `nmrCoupledPairThermal β ℏ ω h` — its high-temperature thermal state `¼(I − βℏω(Z₁+Z₂))`, a
  `State (qubit.compose qubit)` for `(2βℏω)² ≤ 1` (the two-spin high-temperature/positivity window).
* `nmrCoupledPairThermal_op` — its density operator in closed form.

## Design

* **Construction.** `ρ_th` is built from `highTempThermalState` (N&C eq. 7.140; see
  `AxQM/Postulates/API/HighTempThermalState.lean`).
* **Positivity.** `I − b(Z₁+Z₂)` (`b = βℏω`) is positive because
  `I − b(Z₁+Z₂) = ½(I − 2b Z₁) + ½(I − 2b Z₂)` and each `I − 2b Zⱼ` is positive: the general fact
  that `I − cG ⪰ 0` for a self-adjoint involution `G` and `c² ≤ 1`
  (`ContinuousLinearMap.isPositive_one_sub_smul_of_selfAdjoint_involution`, via the projections
  `½(I ± G)`). Unlike the single-qudit thermal state (`nmrThermalStateSpinTwo`, realised as a
  diagonal matrix on `qudit 4`), the state here lives on the *tensor* system `qubit ⊗ qubit`, so
  positivity is proved at the operator level rather than by `Matrix.PosSemidef`.
* **Unit trace** is automatic: `Z₁, Z₂ = Z ⊗ 1, 1 ⊗ Z` are traceless (`tr(A ⊗ B) = tr A · tr B`).
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

/-- The two-qubit dimension: `dim (qubit ⊗ qubit) = 4`. -/
theorem finrank_two_qubit : Module.finrank ℂ (qubit.compose qubit).space = 4 := by
  change Module.finrank ℂ (TensorProduct ℂ qubit.space qubit.space) = 4
  rw [Module.finrank_tensorProduct, finrank_qubit_space]

/-! ### The two-spin Zeeman Hamiltonian -/

/-- The **two-spin NMR Zeeman Hamiltonian** `H_Z = ℏω(Z₁ + Z₂)` on `qubit.compose qubit`, both spins
precessing at the same Larmor frequency `ω` (as in Nielsen & Chuang Exercise 7.37). Its operator is
`ℏω • (Z₁ + Z₂)`, a real multiple of the sum of the single-spin `Z` observables `Z₁ = Z ⊗ 1`,
`Z₂ = 1 ⊗ Z`. -/
def nmrCoupledPairZeeman (ℏ ω : ℝ) : Observable (qubit.compose qubit) where
  op := ((ℏ * ω : ℝ) : ℂ) •
    ((pauliZObservable.tmul (Observable.id qubit)).op
      + ((Observable.id qubit).tmul pauliZObservable).op)
  selfAdjoint :=
    ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp rfl).smul
      ((pauliZObservable.tmul (Observable.id qubit)).selfAdjoint.add
        ((Observable.id qubit).tmul pauliZObservable).selfAdjoint)

@[simp]
theorem nmrCoupledPairZeeman_op (ℏ ω : ℝ) :
    (nmrCoupledPairZeeman ℏ ω).op
      = ((ℏ * ω : ℝ) : ℂ) •
        ((pauliZObservable.tmul (Observable.id qubit)).op
          + ((Observable.id qubit).tmul pauliZObservable).op) :=
  rfl

/-- `Z₁ = Z ⊗ 1` is a **self-adjoint involution** (`Z₁² = 1`). -/
theorem pauliZ_tmul_one_mul_self :
    (pauliZObservable.tmul (Observable.id qubit)).op
        * (pauliZObservable.tmul (Observable.id qubit)).op = 1 := by
  rw [Observable.tmul_op, Observable.id_op]
  exact ContinuousLinearMap.mapL_mul_mapL_self pauliZObservable_op_mul_self (one_mul 1)

/-- `Z₂ = 1 ⊗ Z` is a **self-adjoint involution** (`Z₂² = 1`). -/
theorem one_tmul_pauliZ_mul_self :
    ((Observable.id qubit).tmul pauliZObservable).op
        * ((Observable.id qubit).tmul pauliZObservable).op = 1 := by
  rw [Observable.tmul_op, Observable.id_op]
  exact ContinuousLinearMap.mapL_mul_mapL_self (one_mul 1) pauliZObservable_op_mul_self

/-! ### The coupled two-spin thermal equilibrium state -/

/-- **The high-temperature thermal equilibrium state of the two-spin Zeeman Hamiltonian**
`ρ_th = ¼(I − βℏω(Z₁ + Z₂))` (Nielsen & Chuang eq. 7.140), a genuine `State` on
`qubit.compose qubit` whenever `(2βℏω)² ≤ 1` (the two-spin high-temperature/positivity window,
`‖βℏω(Z₁+Z₂)‖ ≤ 1`). Positivity uses the split `I − b(Z₁+Z₂) = ½(I − 2b Z₁) + ½(I − 2b Z₂)` and the
involution-positivity of each `I − 2b Zⱼ`; unit trace is automatic (`Z₁, Z₂` are traceless). -/
def nmrCoupledPairThermal (β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) :
    State (qubit.compose qubit) :=
  highTempThermalState β (nmrCoupledPairZeeman ℏ ω) <| by
    -- normalise the thermal operator to `¼(I − b(Z₁+Z₂))`, `b = βℏω`
    have hop : (Module.finrank ℂ (qubit.compose qubit).space : ℂ)⁻¹
          • (1 - (β : ℂ) • (nmrCoupledPairZeeman ℏ ω).op)
        = ((4⁻¹ : ℝ) : ℂ) • (1 - ((β * ℏ * ω : ℝ) : ℂ)
            • ((pauliZObservable.tmul (Observable.id qubit)).op
              + ((Observable.id qubit).tmul pauliZObservable).op)) := by
      rw [nmrCoupledPairZeeman_op, finrank_two_qubit, smul_smul]
      push_cast
      module
    rw [hop]
    refine ⟨?_, ?_⟩
    · -- positivity via the ½-split
      have hp1 : (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
            • (pauliZObservable.tmul (Observable.id qubit)).op).IsPositive :=
        ContinuousLinearMap.isPositive_one_sub_smul_of_selfAdjoint_involution
          (pauliZObservable.tmul (Observable.id qubit)).selfAdjoint pauliZ_tmul_one_mul_self h
      have hp2 : (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
            • ((Observable.id qubit).tmul pauliZObservable).op).IsPositive :=
        ContinuousLinearMap.isPositive_one_sub_smul_of_selfAdjoint_involution
          ((Observable.id qubit).tmul pauliZObservable).selfAdjoint one_tmul_pauliZ_mul_self h
      have hsplit : (1 : (qubit.compose qubit).space →L[ℂ] (qubit.compose qubit).space)
            - ((β * ℏ * ω : ℝ) : ℂ) • ((pauliZObservable.tmul (Observable.id qubit)).op
                + ((Observable.id qubit).tmul pauliZObservable).op)
          = ((2⁻¹ : ℝ) : ℂ) • (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
                • (pauliZObservable.tmul (Observable.id qubit)).op)
            + ((2⁻¹ : ℝ) : ℂ) • (1 - ((2 * (β * ℏ * ω) : ℝ) : ℂ)
                • ((Observable.id qubit).tmul pauliZObservable).op) := by
        push_cast
        module
      refine ContinuousLinearMap.IsPositive.smul_of_nonneg ?_
        (Complex.zero_le_real.mpr (by norm_num))
      rw [hsplit]
      exact (hp1.smul_of_nonneg (Complex.zero_le_real.mpr (by norm_num))).add
        (hp2.smul_of_nonneg (Complex.zero_le_real.mpr (by norm_num)))
    · -- unit trace: `Z₁, Z₂` traceless, `tr 1 = 4`
      have htrZ₁ : LinearMap.trace ℂ (qubit.compose qubit).space
          ↑(pauliZObservable.tmul (Observable.id qubit)).op = 0 := by
        rw [Observable.tmul_op, Observable.id_op]
        exact (ContinuousLinearMap.trace_mapL pauliZObservable.op 1).trans (by
          rw [trace_pauliZObservable, zero_mul])
      have htrZ₂ : LinearMap.trace ℂ (qubit.compose qubit).space
          ↑((Observable.id qubit).tmul pauliZObservable).op = 0 := by
        rw [Observable.tmul_op, Observable.id_op]
        exact (ContinuousLinearMap.trace_mapL 1 pauliZObservable.op).trans (by
          rw [trace_pauliZObservable, mul_zero])
      rw [ContinuousLinearMap.toLinearMap_smul, map_smul, ContinuousLinearMap.toLinearMap_sub,
          map_sub,
        ContinuousLinearMap.toLinearMap_smul, map_smul, ContinuousLinearMap.toLinearMap_add,
            map_add,
        htrZ₁, htrZ₂, add_zero, smul_zero, sub_zero, ContinuousLinearMap.toLinearMap_one,
        LinearMap.trace_one, finrank_two_qubit, smul_eq_mul]
      norm_num

@[simp]
theorem nmrCoupledPairThermal_op (β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) :
    (nmrCoupledPairThermal β ℏ ω h).op
      = ((4⁻¹ : ℝ) : ℂ) • (1 - ((β * ℏ * ω : ℝ) : ℂ)
        • ((pauliZObservable.tmul (Observable.id qubit)).op
          + ((Observable.id qubit).tmul pauliZObservable).op)) := by
  rw [nmrCoupledPairThermal, highTempThermalState_op, nmrCoupledPairZeeman_op, finrank_two_qubit,
    smul_smul]
  push_cast
  module

/-! ### The π/2 read pulse and the pulsed initial state -/

/-- The **`Y₁` observable** `Y ⊗ 1` on the first spin, the generator of the read pulse. -/
def nmrPulseGen : Observable (qubit.compose qubit) := pauliYObservable.tmul (Observable.id qubit)

theorem nmrPulseGen_op :
    nmrPulseGen.op = TensorProduct.mapL pauliYObservable.op 1 := by
  rw [nmrPulseGen, Observable.tmul_op, Observable.id_op]

/-- `Y₁ = Y ⊗ 1` is a **self-adjoint involution** (`Y₁² = 1`). -/
theorem nmrPulseGen_op_mul_self : nmrPulseGen.op * nmrPulseGen.op = 1 := by
  rw [nmrPulseGen_op]
  exact ContinuousLinearMap.mapL_mul_mapL_self pauliYObservable_op_mul_self (one_mul 1)

/-- **`Z₁ Y₁ = −i X₁`** on the first spin: the single-qubit Pauli product `Z Y = −i X` (N&C
eq. 2.40 / 2.43), lifted through `mapL` to `Z ⊗ 1`, `Y ⊗ 1`, `X ⊗ 1`. -/
theorem pauliZ_tmul_one_mul_nmrPulseGen :
    (pauliZObservable.tmul (Observable.id qubit)).op * nmrPulseGen.op
      = -Complex.I • (pauliXObservable.tmul (Observable.id qubit)).op := by
  have H : TensorProduct.mapL pauliZObservable.op (1 : qubit.space →L[ℂ] qubit.space)
        * TensorProduct.mapL pauliYObservable.op 1
      = -Complex.I • TensorProduct.mapL pauliXObservable.op 1 := by
    rw [← TensorProduct.mapL_mul, pauliZObservable_op_mul_pauliYObservable_op, mul_one,
      TensorProduct.mapL_smul_left]
  rw [Observable.tmul_op, Observable.id_op, nmrPulseGen_op, Observable.tmul_op, Observable.id_op]
  exact H

/-- `Z₁` **anticommutes** with the pulse generator `Y₁`: `Z₁ Y₁ = −(Y₁ Z₁)`. -/
theorem pauliZ_tmul_one_anticomm_nmrPulseGen :
    (pauliZObservable.tmul (Observable.id qubit)).op * nmrPulseGen.op
      = -(nmrPulseGen.op * (pauliZObservable.tmul (Observable.id qubit)).op) := by
  have hZY : pauliZObservable.op * pauliYObservable.op
      = -(pauliYObservable.op * pauliZObservable.op) := by
    rw [pauliYObservable_op_anticomm_pauliZObservable_op, neg_neg]
  have H : TensorProduct.mapL pauliZObservable.op (1 : qubit.space →L[ℂ] qubit.space)
        * TensorProduct.mapL pauliYObservable.op 1
      = -(TensorProduct.mapL pauliYObservable.op 1 * TensorProduct.mapL pauliZObservable.op 1) := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, mul_one, hZY,
      TensorProduct.mapL_neg_left]
  rw [Observable.tmul_op, Observable.id_op, nmrPulseGen_op]
  exact H

/-- `Z₂` **commutes** with the pulse generator `Y₁` (different spins): `Z₂ Y₁ = Y₁ Z₂`. -/
theorem one_tmul_pauliZ_comm_nmrPulseGen :
    ((Observable.id qubit).tmul pauliZObservable).op * nmrPulseGen.op
      = nmrPulseGen.op * ((Observable.id qubit).tmul pauliZObservable).op := by
  have H : TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.op
        * TensorProduct.mapL pauliYObservable.op 1
      = TensorProduct.mapL pauliYObservable.op 1
        * TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.op := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, one_mul, mul_one, one_mul, mul_one]
  rw [Observable.tmul_op, Observable.id_op, nmrPulseGen_op]
  exact H

/-- The **`π/2` (`90°`) read pulse** `e^{iπ Y₁/4}` on the first spin (Nielsen & Chuang §7.7.2),
as an `Evolution`: the adjoint of the `Y₁`-propagator `exp(-i Y₁ (π/4)) = e^{-iπ Y₁/4}`. -/
def nmrCoupledPairPulse : Evolution (qubit.compose qubit) :=
  (nmrPulseGen.propagator 1 0 (Real.pi / 4)).adjoint

/-- **The pulse rotates `Z₁` into `−X₁`:** `e^{iπ Y₁/4} Z₁ e^{−iπ Y₁/4} = −X₁`. Since `Z₁`
anticommutes with the involution `Y₁`, the Heisenberg-conjugation lemma gives (at the doubled angle
`π/2`, `cos = 0`, `sin = 1`) `−i(Z₁ Y₁) = −i(−i X₁) = −X₁`. -/
theorem nmrCoupledPairPulse_conj_pauliZ_one :
    ContinuousLinearMap.adjoint (nmrPulseGen.propagator 1 0 (Real.pi / 4)).op
        * (pauliZObservable.tmul (Observable.id qubit)).op
        * (nmrPulseGen.propagator 1 0 (Real.pi / 4)).op
      = -(pauliXObservable.tmul (Observable.id qubit)).op := by
  have hconj := nmrPulseGen.propagator_conj_op_anticomm (c := 1) (G := nmrPulseGen.op)
    (A := (pauliZObservable.tmul (Observable.id qubit)).op)
    (one_smul ℂ nmrPulseGen.op).symm nmrPulseGen_op_mul_self nmrPulseGen.selfAdjoint
    pauliZ_tmul_one_anticomm_nmrPulseGen (Real.pi / 4)
  have harg : (2 : ℝ) * 1 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [hconj, harg, Real.cos_pi_div_two, Real.sin_pi_div_two, pauliZ_tmul_one_mul_nmrPulseGen]
  push_cast
  rw [zero_smul, smul_smul, mul_neg, one_mul, Complex.I_mul_I, neg_neg, one_smul, zero_sub]

/-- **The pulse fixes `Z₂`:** `e^{iπ Y₁/4} Z₂ e^{−iπ Y₁/4} = Z₂`, because `Z₂ = 1 ⊗ Z` commutes with
the pulse generator `Y₁ = Y ⊗ 1`. -/
theorem nmrCoupledPairPulse_conj_pauliZ_two :
    ContinuousLinearMap.adjoint (nmrPulseGen.propagator 1 0 (Real.pi / 4)).op
        * ((Observable.id qubit).tmul pauliZObservable).op
        * (nmrPulseGen.propagator 1 0 (Real.pi / 4)).op
      = ((Observable.id qubit).tmul pauliZObservable).op :=
  nmrPulseGen.propagator_conj_op_commute (c := 1) (G := nmrPulseGen.op)
    (A := ((Observable.id qubit).tmul pauliZObservable).op)
    (one_smul ℂ nmrPulseGen.op).symm nmrPulseGen_op_mul_self
    one_tmul_pauliZ_comm_nmrPulseGen (Real.pi / 4)

/-- **The `π/2`-pulsed initial state of Exercise 7.37**, `ρ = e^{iπ Y₁/4} ρ_th e^{−iπ Y₁/4}`, the
two-spin thermal state after the read pulse on the first spin, as a `State`. -/
def nmrCoupledPairPulsedState (β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) :
    State (qubit.compose qubit) :=
  nmrCoupledPairPulse.evolve (nmrCoupledPairThermal β ℏ ω h)

/-- **The density operator of the pulsed initial state of Exercise 7.37 in closed form:**
`ρ.op = ¼(I + βℏω X₁ − βℏω Z₂)`. The `90°` read pulse turns the thermal population difference
`−βℏω Z₁` on the first spin into observable transverse magnetization `+βℏω X₁`, while the neighbour
term `−βℏω Z₂` is unaffected. Proof: `ρ.op = U ρ_th U†` with `U = e^{iπ Y₁/4}` the adjoint of the
`Y₁`-propagator, so the conjugation distributes over `ρ_th = ¼(I − βℏω(Z₁+Z₂))`, fixing `I` and `Z₂`
and sending `Z₁ ↦ −X₁`. -/
theorem nmrCoupledPairPulsedState_op (β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) :
    (nmrCoupledPairPulsedState β ℏ ω h).op
      = ((4⁻¹ : ℝ) : ℂ) • (1
          + ((β * ℏ * ω : ℝ) : ℂ) • (pauliXObservable.tmul (Observable.id qubit)).op
          - ((β * ℏ * ω : ℝ) : ℂ) • ((Observable.id qubit).tmul pauliZObservable).op) := by
  rw [nmrCoupledPairPulsedState, Evolution.evolve_op, nmrCoupledPairThermal_op,
    nmrCoupledPairPulse, Evolution.adjoint_op, ContinuousLinearMap.adjoint_adjoint]
  set V := (nmrPulseGen.propagator 1 0 (Real.pi / 4)).op with hV
  -- V† V = 1 (unitarity of the propagator)
  have hunit : ContinuousLinearMap.adjoint V * V = 1 := by
    rw [hV, ← Evolution.adjoint_op]
    exact (nmrPulseGen.propagator 1 0 (Real.pi / 4)).adjoint_comp_self
  -- comp is mul; reassociate and distribute the conjugation
  change ContinuousLinearMap.adjoint V
      * (((4⁻¹ : ℝ) : ℂ) • (1 - ((β * ℏ * ω : ℝ) : ℂ)
          • ((pauliZObservable.tmul (Observable.id qubit)).op
            + ((Observable.id qubit).tmul pauliZObservable).op))) * V = _
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, hunit, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul, nmrCoupledPairPulse_conj_pauliZ_one,
    nmrCoupledPairPulse_conj_pauliZ_two]
  module

end AxQM
