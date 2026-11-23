/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRCoupledSpinPulsedState

/-!
# AxQM.Postulates.API — the coupled two-spin NMR free-induction-decay signal (N&C Ex 7.37)

The **free-induction-decay (FID) signal** `V(t)` of the two-spin, `J`-coupled NMR system of
Nielsen & Chuang Exercise 7.37 (the `H = J Z₁Z₂` half), and its closed-form value. N&C eq. 7.143
defines the signal as `V(t) = V₀ tr[e^{-iHt} ρ e^{iHt} (i Xₖ + Yₖ)]`, the ensemble average of the
(non-Hermitian) transverse magnetization readout `i Xₖ + Yₖ` against the Heisenberg-evolved thermal
state. For the coupled pair (`k = 1`, `H = J Z₁Z₂`, and `ρ` the `π/2`-pulsed thermal state
`e^{iπY₁/4} ¼(1 − βℏω₀(Z₁+Z₂)) e^{-iπY₁/4}` of the exercise) this evaluates to

* `nmrCoupledPairFID_eq` — `V(t) = i · V₀ · βℏω₀ · cos(2Jt)`,

a single spectral **doublet** at `±2J` (the `cos(2Jt)` of the coupled precession), whose amplitude
is the transverse magnetization `βℏω₀` produced by the `90°` read pulse.

## Design

* **Statement.** `V(t)` is the operator trace of the Schrödinger-evolved `State`
  `nmrCoupledPairPulsedState` against the readout `nmrTransverseReadout`.
* **Proof.** No matrices. Trace cyclicity (`trace_cyclic`, from `LinearMap.trace_mul_comm`) turns
  `tr[e^{-iHt} ρ e^{iHt} R]` into `tr[ρ · (e^{iHt} R e^{-iHt})]`, and the Heisenberg readout
  `nmrReadout_heisenberg` gives the closed form `e^{iHt} R e^{-iHt} = R (cos(2Jt) − i sin(2Jt) Z₂)`.
  Written in the clean two-qubit Pauli monomial basis (`nmrReadout_heisenberg_rhs_monomial`), the
  trace is evaluated by **Hilbert–Schmidt orthogonality** `tr(A ⊗ B) = tr A · tr B`
  (`ContinuousLinearMap.trace_mapL`): every Pauli string but the identity is traceless, so only the
  term `βℏω₀ X₁ · (i cos(2Jt) X₁)` survives, giving `i βℏω₀ cos(2Jt) · tr(1)/4 = i βℏω₀ cos(2Jt)`.
* **Scalar-tower workaround.** On the raw tensor operator ring the instance `IsScalarTower ℂ _ _`
  does not synthesise for abstract operators, so the scalar-pull helpers push scalars through the
  `LinearMap` coercion (where `Module.End` provides the tower) rather than the continuous-linear-map
  ring directly.
-/

open scoped ComplexOrder

noncomputable section

namespace AxQM

/-! ### Generic trace lemmas and the two-qubit tensor factorisation

The single-qubit Pauli traces (`trace_pauliXObservable`/`…YObservable`/`…ZObservable`,
`trace_one_qubit`, `pauliXObservable_op_mul_pauliYObservable_op` = `X Y = i Z`, and its trace) are
the shared Hilbert–Schmidt building blocks of `AxQM/Postulates/API/Qubit.lean`. The scalar-pull and
cyclicity lemmas here are generic (any `E →L[ℂ] E`); the tensor-factorisation lemmas are
two-qubit-specific through `TensorProduct.mapL`.

On the raw tensor operator ring the abstract instance `IsScalarTower ℂ _ _` fails to synthesise, so
scalars are pulled through the `LinearMap` coercion (where `Module.End` provides the tower). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Pull a left scalar out of an operator trace: `tr((a • X) Y) = a · tr(X Y)`. -/
theorem trace_smul_left (a : ℂ) (X Y : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑((a • X) * Y) = a * LinearMap.trace ℂ E ↑(X * Y) := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_smul, smul_mul_assoc,
      map_smul,
    smul_eq_mul, ← ContinuousLinearMap.toLinearMap_mul]

/-- Pull a right scalar out of an operator trace: `tr(X (d • Y)) = d · tr(X Y)`. -/
theorem trace_smul_right (d : ℂ) (X Y : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(X * (d • Y)) = d * LinearMap.trace ℂ E ↑(X * Y) := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_smul, mul_smul_comm,
      map_smul,
    smul_eq_mul, ← ContinuousLinearMap.toLinearMap_mul]

/-- Trace of a scalar multiple of a single clean tensor: `tr(a • (A ⊗ B)) = a · tr A · tr B`. -/
theorem trace_smul_mapL (a : ℂ) (A B : qubit.space →L[ℂ] qubit.space) :
    LinearMap.trace ℂ (TensorProduct ℂ qubit.space qubit.space) ↑(a • TensorProduct.mapL A B)
      = a * (LinearMap.trace ℂ qubit.space ↑A * LinearMap.trace ℂ qubit.space ↑B) := by
  rw [ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, ContinuousLinearMap.trace_mapL]

/-- Trace of a product of two scalar-weighted clean tensors, factorised by Hilbert–Schmidt:
`tr((a • A⊗B)(d • C⊗D)) = a·d·tr(AC)·tr(BD)`. -/
theorem trace_smul_mapL_mul_smul_mapL (a d : ℂ) (A B C D : qubit.space →L[ℂ] qubit.space) :
    LinearMap.trace ℂ (TensorProduct ℂ qubit.space qubit.space)
        ↑((a • TensorProduct.mapL A B) * (d • TensorProduct.mapL C D))
      = a * d
        * (LinearMap.trace ℂ qubit.space ↑(A * C) * LinearMap.trace ℂ qubit.space ↑(B * D)) := by
  rw [trace_smul_left, trace_smul_right, ← TensorProduct.mapL_mul, ContinuousLinearMap.trace_mapL,
    mul_assoc]

/-- **Trace cyclicity:** `tr(A B) = tr(B A)` (from `LinearMap.trace_mul_comm`, through the
`ContinuousLinearMap` → `LinearMap` coercion). -/
theorem trace_cyclic (A B : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(A * B) = LinearMap.trace ℂ E ↑(B * A) := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
      LinearMap.trace_mul_comm]

/-! ### The Heisenberg-evolved readout in the Pauli monomial basis -/

set_option synthInstance.maxHeartbeats 400000 in
-- `module`/`mapL_mul` on the raw tensor operator ring need extra instance-search budget.
/-- **The Heisenberg-evolved readout in the Pauli monomial basis.** Expanding
`R (cos(2Jt) − i sin(2Jt) Z₂)` (the closed form of `e^{iHt}(i X₁+Y₁)e^{-iHt}` from
`nmrReadout_heisenberg`) over the four clean tensors gives
`i cos X₁ + cos Y₁ + (sin·i·i) X₁Z₂ − i sin Y₁Z₂`; the `X₁Z₂` coefficient is kept un-normalised
(`sin·i·i`) — it is traceless against `ρ` regardless. -/
theorem nmrReadout_heisenberg_rhs_monomial (c s : ℂ) :
    (Complex.I • TensorProduct.mapL pauliXObservable.op (1 : qubit.space →L[ℂ] qubit.space)
        + TensorProduct.mapL pauliYObservable.op 1)
      * (c • (1 : TensorProduct ℂ qubit.space qubit.space →L[ℂ]
              TensorProduct ℂ qubit.space qubit.space)
          - (s * Complex.I) • TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
              pauliZObservable.op)
      = (Complex.I * c) • TensorProduct.mapL pauliXObservable.op 1
        + c • TensorProduct.mapL pauliYObservable.op 1
        - (s * Complex.I * Complex.I)
          • TensorProduct.mapL pauliXObservable.op pauliZObservable.op
        - (s * Complex.I) • TensorProduct.mapL pauliYObservable.op pauliZObservable.op := by
  have hXZ : TensorProduct.mapL pauliXObservable.op (1 : qubit.space →L[ℂ] qubit.space)
        * TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.op
      = TensorProduct.mapL pauliXObservable.op pauliZObservable.op := by
    rw [← TensorProduct.mapL_mul, mul_one, one_mul]
  have hYZ : TensorProduct.mapL pauliYObservable.op (1 : qubit.space →L[ℂ] qubit.space)
        * TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.op
      = TensorProduct.mapL pauliYObservable.op pauliZObservable.op := by
    rw [← TensorProduct.mapL_mul, mul_one, one_mul]
  simp only [mul_sub, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, hXZ, hYZ]
  module

/-! ### The core trace value and the FID signal -/

set_option synthInstance.maxHeartbeats 400000 in
-- The trace-factorisation helpers below carry the same raw-tensor-ring instance-search cost.
/-- **The core FID trace value (raw tensor-ring form).** For the two-spin thermal
`ρ = ¼(1 + b X₁ − b Z₂)` (`b = βℏω₀`) and the Heisenberg-evolved readout `R (cos − i sin Z₂)`,
Hilbert–Schmidt orthogonality collapses the trace to the single surviving `X₁·X₁` term:
`tr[ρ · e^{iHt} R e^{-iHt}] = i b cos(2Jt)`. -/
theorem nmrCoupledPairFID_core_trace_raw (b c s : ℂ) :
    LinearMap.trace ℂ (TensorProduct ℂ qubit.space qubit.space)
      ↑( (((4⁻¹ : ℝ) : ℂ) • ((1 : TensorProduct ℂ qubit.space qubit.space →L[ℂ]
              TensorProduct ℂ qubit.space qubit.space)
            + b • TensorProduct.mapL pauliXObservable.op (1 : qubit.space →L[ℂ] qubit.space)
            - b • TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.op))
        * ((Complex.I • TensorProduct.mapL pauliXObservable.op (1 : qubit.space →L[ℂ] qubit.space)
              + TensorProduct.mapL pauliYObservable.op (1 : qubit.space →L[ℂ] qubit.space))
          * (c • (1 : TensorProduct ℂ qubit.space qubit.space →L[ℂ]
                TensorProduct ℂ qubit.space qubit.space)
              - (s * Complex.I) • TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
                  pauliZObservable.op)) )
      = b * c * Complex.I := by
  rw [nmrReadout_heisenberg_rhs_monomial, trace_smul_left, sub_mul, add_mul, one_mul]
  simp only [mul_add, mul_sub, map_add, map_sub, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_sub, trace_smul_mapL, trace_smul_mapL_mul_smul_mapL,
    pauliXObservable_op_mul_self, pauliZObservable_op_mul_self, one_mul, mul_one,
    ContinuousLinearMap.toLinearMap_one, trace_one_qubit, trace_pauliXObservable,
        trace_pauliYObservable,
    trace_pauliZObservable, trace_pauliXObservable_op_mul_pauliYObservable_op]
  push_cast
  ring

/-- **The core FID trace value on the composite system.** The same identity as
`nmrCoupledPairFID_core_trace_raw`, restated over `(qubit.compose qubit).space` with the readout
`nmrTransverseReadout` and the clean tensors `(P.tmul Q).op`; the two forms are definitionally equal
(`(P.tmul Q).op = mapL P.op Q.op`, `nmrTransverseReadout = i X₁ + Y₁`). -/
theorem nmrCoupledPairFID_core_trace (b c s : ℂ) :
    LinearMap.trace ℂ (qubit.compose qubit).space
      ↑( (((4⁻¹ : ℝ) : ℂ) • ((1 : (qubit.compose qubit).space →L[ℂ] (qubit.compose qubit).space)
            + b • (pauliXObservable.tmul (Observable.id qubit)).op
            - b • ((Observable.id qubit).tmul pauliZObservable).op))
        * (nmrTransverseReadout
          * (c • (1 : (qubit.compose qubit).space →L[ℂ] (qubit.compose qubit).space)
              - (s * Complex.I) • ((Observable.id qubit).tmul pauliZObservable).op)) )
      = b * c * Complex.I :=
  nmrCoupledPairFID_core_trace_raw b c s

/-- The **free-induction-decay signal** `V(t) = V₀ tr[e^{-iHt} ρ e^{iHt} (i X₁ + Y₁)]` of the
coupled two-spin NMR system (Nielsen & Chuang eq. 7.143, `k = 1`), for the `J`-coupling Hamiltonian
`H = J Z₁Z₂` and the `π/2`-pulsed thermal initial state `ρ = nmrCoupledPairPulsedState`. The
Schrödinger-evolved state `e^{-iHt} ρ e^{iHt}` is
`((couplingZZHamiltonian J).propagator 1 0 t).evolve ρ` and the readout is
`nmrTransverseReadout = i X₁ + Y₁`. -/
def nmrCoupledPairFID (V₀ J β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) (t : ℝ) : ℂ :=
  (V₀ : ℂ) • LinearMap.trace ℂ (qubit.compose qubit).space
    ↑((((couplingZZHamiltonian J).propagator 1 0 t).evolve
        (nmrCoupledPairPulsedState β ℏ ω h)).op * nmrTransverseReadout)

/-- **The FID signal of the coupled NMR pair (Nielsen & Chuang Exercise 7.37, `H = J Z₁Z₂`):**
`V(t) = i · V₀ · βℏω₀ · cos(2Jt)`. The free-induction decay of the `π/2`-pulsed thermal state is a
single spectral doublet at `±2J`, with amplitude the transverse magnetization `βℏω₀`. Proof: trace
cyclicity moves the propagators onto the readout, `nmrReadout_heisenberg` gives its closed form
`(i X₁+Y₁)(cos(2Jt) − i sin(2Jt) Z₂)`, and the trace against `ρ.op = ¼(1 + βℏω₀ X₁ − βℏω₀ Z₂)` is
evaluated by Pauli Hilbert–Schmidt orthogonality (`nmrCoupledPairFID_core_trace`). -/
theorem nmrCoupledPairFID_eq (V₀ J β ℏ ω : ℝ) (h : (2 * (β * ℏ * ω)) ^ 2 ≤ 1) (t : ℝ) :
    nmrCoupledPairFID V₀ J β ℏ ω h t
      = Complex.I * (V₀ : ℂ) * ((β * ℏ * ω : ℝ) : ℂ) * (Real.cos (2 * J * t) : ℂ) := by
  rw [nmrCoupledPairFID, Evolution.evolve_op]
  -- cyclicity: tr[U ρ U† R] = tr[ρ (U† R U)]
  simp only [← ContinuousLinearMap.mul_def]
  rw [mul_assoc, mul_assoc, trace_cyclic, mul_assoc]
  -- closed-form readout and pulsed state, then Hilbert–Schmidt evaluation of the trace
  rw [nmrReadout_heisenberg, nmrCoupledPairPulsedState_op,
    nmrCoupledPairFID_core_trace ((β * ℏ * ω : ℝ) : ℂ) (Real.cos (2 * J * t) : ℂ)
      (Real.sin (2 * J * t) : ℂ), smul_eq_mul]
  ring

end AxQM
