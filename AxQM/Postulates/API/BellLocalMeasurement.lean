/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.MeasurementCoarseGrain
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.CascadedMeasurement
import AxQM.Postulates.API.PauliMeasurement
import AxQM.Postulates.API.BellReducedState
import AxQM.Postulates.API.PhaseFlipCode

/-!
# AxQM.Postulates.API — local `Z`/`X` measurements vs. Bell projectors `Π_bf`/`Π_pf`

Apparatus for Nielsen & Chuang Exercise 12.32 (§12.6.5, p. 595), both halves:
the **bit-flip** projector `Π_bf = |β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁|` onto the Bell states carrying a bit flip
and its realisation by **local** single-qubit `Z` measurements, and the **phase-flip** projector
`Π_pf = |β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁|` onto the Bell states carrying a phase flip and its realisation by
**local** single-qubit `X` measurements.  N&C observe that although the individual local
measurements `Z ⊗ I`, `I ⊗ Z` (resp. `X ⊗ I`, `I ⊗ X`) do *not* commute with the Bell basis, the
statistics Alice and Bob compile from them coincide with those of a genuine `Π_bf` (resp. `Π_pf`)
measurement.  This
file supplies the operator identities behind that coincidence; the statements of the exercise are in
`AxQM/NC/Ch12/Exercise12_32.lean`.

The phase-flip half mirrors the bit-flip half through the Hadamard basis: the local `X`
eigenprojectors are `|+⟩⟨+|`, `|−⟩⟨−|` (`pauliXObservable_projPlus_rankOne`,
`pauliXObservable_projMinus_rankOne`, on `qubitPlus`/`qubitMinus`, beside the `Z` versions in
`Postulates/API/PauliMeasurement`), and the "same statistics" crux
`localXMeasurement_map_elements_eq` reuses the identical cross-term-cancellation helper
`rankOne_sqrtTwoInv_add_sub_self` — here the Hadamard products `|±⟩⊗|±⟩` are the normalised
sum/difference `(β_x0 ± β_x1)/√2` of the two Bell vectors sharing a phase-flip label `x`
(`pmQubit_zero_tmul_zero_eq_bell` and companions), the mirror image of the bit-flip decomposition.

## Contents

* `bitFlipProjector` — N&C's `Π_bf = |β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁|` (`bellState 0 1 = β₀₁`,
  `bellState 1 1 = β₁₁`).  `bitFlipProjector_eq_bellMap` records that it is exactly the "bit flip
  detected" effect of the Bell measurement coarse-grained by `bitFlipIndex` — i.e. measuring `Π_bf`.
* `localZMeasurement` — Alice and Bob each measure `Z` locally: the cascade of the two single-qubit
  `Z` sign measurements (`onLeft` then `onRight`), a genuine four-outcome joint measurement.  Its
  operator at `(a, b)` is the computational projector `|ab⟩⟨ab|` (`localZMeasurement_op`).
* `zParity (a, b) = a + b` — the compiled statistic ("did the two local `Z` outcomes disagree?"),
  and `bitFlipIndex (x, y) = y` — the Bell-measurement coordinate detecting a bit flip.
* `localZMeasurement_map_elements_eq` — **the heart**: for every merged outcome `k`, the
  coarse-grained local-`Z` POVM effect equals the coarse-grained Bell POVM effect (the `Π_bf`
  effect).  Because a POVM effect fixes the Born statistics on *every* state, this is N&C's claim.

## Design

The single-qubit `Z` eigenprojectors are `|0⟩⟨0|`, `|1⟩⟨1|` (`pauliZObservable_projPlus_rankOne`,
`pauliZObservable_projMinus_rankOne`, in `Postulates/API/PauliMeasurement`), so the cascade operator
factorises as `|a⟩⟨a| ⊗ |b⟩⟨b| = |ab⟩⟨ab|` through `TensorProduct.mapL` and `rankOne_tmul_self`;
each such projector is a unit rank-one projector, hence its own POVM effect
(`InnerProductSpace.adjoint_rankOne_comp_self`).  The key identity then reduces, at each outcome, to
the general `ToMathlib` fact `rankOne_sqrtTwoInv_add_sub_self` that
`|β₊⟩⟨β₊| + |β₋⟩⟨β₋| = |u⟩⟨u| + |w⟩⟨w|` for the normalised sum/difference `|β±⟩ = (|u⟩ ± |w⟩)/√2` —
the `|u⟩⟨w|`, `|w⟩⟨u|` cross terms cancel.  This is the "same statistics despite not commuting with
the Bell basis" mechanism: the compiled parity statistic sees only the diagonal of the Bell
decomposition.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **Instance-diamond bridge.** `(qubit ⊗ qubit).space` (bundled) and `qubit.space ⊗[ℂ]
qubit.space` (generic) are `rfl`-defeq, but a scalar multiple of a bundled `PureState.tmul` vector
carries the *bundled* `Module` instance, which blocks `one_smul`/`smul_smul`/`abel` (all stated
against the *generic* instance) from firing. This crosses the diamond for the one scalar-wrapped
summand `bellBasisVec` produces. -/
private theorem smul_tmul_bridge (c : ℂ) (a b : Fin 2) :
    c • (qubitBasis a ⊗ qubitBasis b).vec
      = c • ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec : qubit.space ⊗[ℂ] qubit.space) := rfl

/-! ### N&C's bit-flip projector `Π_bf` (Bell-basis form) -/

/-- **The bit-flip detector `Π_bf`** of Nielsen & Chuang §12.6.5 (p. 595):
`Π_bf = |β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁|`, the projector onto the two Bell states that carry a bit flip
(`bellState 0 1 = β₀₁`, `bellState 1 1 = β₁₁`; equivalently `Π_bf = (I⊗I − Z⊗Z)/2`).  This is the
Bell-basis projector whose statistics N&C's local `Z` measurements reproduce. -/
def bitFlipProjector : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  rankOne ℂ (bellState 0 1).vec (bellState 0 1).vec
    + rankOne ℂ (bellState 1 1).vec (bellState 1 1).vec

/-! ### The local `Z` measurement and the compiled parity statistic -/

/-- The single-qubit `Z` (sign) measurement, outcome `0 ↔ +1` (`|0⟩`), `1 ↔ −1` (`|1⟩`). -/
def zSignMeasurement : Measurement (Fin 2) qubit :=
  pauliZObservable.signMeasurement pauliZObservable_op_mul_self

/-- The operator of the single-qubit `Z` measurement is the computational projector `|a⟩⟨a|` (the
Pauli-`Z` eigenprojectors `pauliZObservable_projPlus_rankOne` / `pauliZObservable_projMinus_rankOne`
from `Postulates/API/PauliMeasurement`). -/
theorem zSignMeasurement_op (a : Fin 2) :
    zSignMeasurement.op a = rankOne ℂ (qubitBasis a).vec (qubitBasis a).vec := by
  fin_cases a
  · exact pauliZObservable_projPlus_rankOne
  · exact pauliZObservable_projMinus_rankOne

/-- **Alice and Bob each measure `Z` locally.**  The joint local `Z` measurement is the cascade of
the two single-qubit `Z` sign measurements — `zSignMeasurement` on the left factor (Alice), then on
the right factor (Bob) — a genuine four-outcome `Measurement (Fin 2 × Fin 2)`. -/
def localZMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ qubit) :=
  (zSignMeasurement.onLeft qubit).cascade (zSignMeasurement.onRight qubit)

/-- The joint local-`Z` measurement operator at outcome `(a, b)` is the computational projector
`|ab⟩⟨ab| = |a⟩⟨a| ⊗ |b⟩⟨b|`: the cascade composes the two single-qubit projectors on disjoint
factors, which `TensorProduct.mapL` and `rankOne_tmul_self` reassemble into the product. -/
theorem localZMeasurement_op (a b : Fin 2) :
    localZMeasurement.op (a, b)
      = rankOne ℂ ((qubitBasis a ⊗ qubitBasis b).vec) ((qubitBasis a ⊗ qubitBasis b).vec) := by
  have h : localZMeasurement.op (a, b)
      = TensorProduct.mapL (zSignMeasurement.op a) (zSignMeasurement.op b) := by
    rw [localZMeasurement, Measurement.cascade_op, Measurement.onRight_op, Measurement.onLeft_op]
    exact (TensorProduct.mapL_comp _ _ _ _).symm.trans
      (by simp only [← ContinuousLinearMap.mul_def, one_mul, mul_one])
  rw [h, zSignMeasurement_op, zSignMeasurement_op, PureState.tmul_vec]
  exact (InnerProductSpace.rankOne_tmul_self (qubitBasis a).vec (qubitBasis b).vec).symm

/-- The POVM effect of the local-`Z` measurement at `(a, b)` is the projector `|ab⟩⟨ab|` itself: the
operator is a unit rank-one projector, hence its own effect (`adjoint_rankOne_comp_self`). -/
theorem localZMeasurement_toPOVM_elements (a b : Fin 2) :
    localZMeasurement.toPOVM.elements (a, b)
      = rankOne ℂ ((qubitBasis a ⊗ qubitBasis b).vec) ((qubitBasis a ⊗ qubitBasis b).vec) := by
  rw [Measurement.toPOVM_elements, localZMeasurement_op]
  exact InnerProductSpace.adjoint_rankOne_comp_self (qubitBasis a ⊗ qubitBasis b).normalized

/-- **The compiled bit-flip statistic** `a + b`: Alice and Bob record whether their two local `Z`
outcomes *disagree* (`a + b = 1`, a bit flip) or *agree* (`a + b = 0`). -/
def zParity : Fin 2 × Fin 2 → Fin 2 := fun p => p.1 + p.2

/-- **The bit-flip outcome coordinate** of the Bell measurement: `|β_xy⟩` carries a bit flip iff
`y = 1`, so coarse-graining the Bell measurement along `bitFlipIndex` is exactly the `Π_bf`
measurement. -/
def bitFlipIndex : Fin 2 × Fin 2 → Fin 2 := fun p => p.2

/-- **`Π_bf` is the "bit flip detected" effect of the Bell measurement.**  Coarse-graining the Bell
measurement along `bitFlipIndex` and reading outcome `1` gives the effect
`|β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁| = bitFlipProjector`: reading `1` from `bellMeasurement.coarseGrain
bitFlipIndex` *is* measuring `Π_bf`. -/
theorem bitFlipProjector_eq_bellMap :
    (bellMeasurement.toPOVM.map bitFlipIndex).elements 1 = bitFlipProjector := by
  have hfib : (Finset.univ.filter fun p : Fin 2 × Fin 2 => bitFlipIndex p = 1)
      = {(0, 1), (1, 1)} := by decide
  rw [POVM.map_elements, hfib, Finset.sum_pair (by decide),
    bellMeasurement_toPOVM_elements_eq_bellProjector,
    bellMeasurement_toPOVM_elements_eq_bellProjector]
  rfl

/-- **The heart of Exercise 12.32 (bit-flip half).**  For every merged outcome `k`, the effect of
the coarse-grained local-`Z` measurement (grouped by the parity statistic `zParity`) equals the
effect of the coarse-grained Bell measurement (grouped by `bitFlipIndex`, i.e. the `Π_bf`
measurement).  Since a POVM effect determines the Born statistics on *every* state, the two produce
identical statistics — this is N&C's claim that the local `Z` measurements reproduce the `Π_bf`
statistics despite `Z ⊗ I`, `I ⊗ Z` not commuting with the Bell basis.

The two fibres over `k` are `{(0,1),(1,0)}` vs `{(0,1),(1,1)}` (bit flip, `k = 1`) and
`{(0,0),(1,1)}` vs `{(0,0),(1,0)}` (no flip, `k = 0`); in each case the local side sums to
`|u⟩⟨u| + |w⟩⟨w|` and the Bell side to `|β₊⟩⟨β₊| + |β₋⟩⟨β₋|` for the same `u, w`, equal by
`rankOne_sqrtTwoInv_add_sub_self`. -/
theorem localZMeasurement_map_elements_eq (k : Fin 2) :
    (localZMeasurement.toPOVM.map zParity).elements k
      = (bellMeasurement.toPOVM.map bitFlipIndex).elements k := by
  rw [POVM.map_elements, POVM.map_elements, Finset.sum_filter, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, zParity, bitFlipIndex, localZMeasurement_toPOVM_elements,
    bellMeasurement_toPOVM_elements_eq_bellProjector]
  fin_cases k <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, add_zero, zero_add, bellState_vec,
      bellBasisVec, Fin.val_zero, Fin.val_one, pow_zero, pow_one, reduceIte]
  all_goals simp only [smul_tmul_bridge]
  all_goals simp only [one_smul, neg_one_smul, Fin.reduceAdd, PureState.tmul_vec]
  · exact (rankOne_sqrtTwoInv_add_sub_self (𝕜 := ℂ) ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec)
      ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec)).symm
  · exact (rankOne_sqrtTwoInv_add_sub_self (𝕜 := ℂ) ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec)
      ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec)).symm

/-! ### N&C's phase-flip projector `Π_pf` (Bell-basis form) -/

/-- **The phase-flip detector `Π_pf`** of Nielsen & Chuang §12.6.5 (p. 595):
`Π_pf = |β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁|`, the projector onto the two Bell states that carry a phase flip
(`bellState 1 0 = β₁₀`, `bellState 1 1 = β₁₁`; equivalently `Π_pf = (I⊗I − X⊗X)/2`).  This is the
Bell-basis projector whose statistics N&C's local `X` measurements reproduce — the phase-flip mirror
of `bitFlipProjector`. -/
def phaseFlipProjector : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
  rankOne ℂ (bellState 1 0).vec (bellState 1 0).vec
    + rankOne ℂ (bellState 1 1).vec (bellState 1 1).vec

/-! ### The local `X` measurement and the compiled parity statistic -/

/-- The single-qubit `X` (sign) measurement, outcome `0 ↔ +1` (`|+⟩`), `1 ↔ −1` (`|−⟩`). -/
def xSignMeasurement : Measurement (Fin 2) qubit :=
  pauliXObservable.signMeasurement pauliXObservable_op_mul_self

/-- The operator of the single-qubit `X` measurement is the Hadamard projector `|x_a⟩⟨x_a|`
(`pmQubit 0 = |+⟩`, `pmQubit 1 = |−⟩`), the `X`-eigenprojectors
`pauliXObservable_projPlus_rankOne` / `pauliXObservable_projMinus_rankOne`. -/
theorem xSignMeasurement_op (a : Fin 2) :
    xSignMeasurement.op a = rankOne ℂ (pmQubit a) (pmQubit a) := by
  fin_cases a
  · exact pauliXObservable_projPlus_rankOne
  · exact pauliXObservable_projMinus_rankOne

/-- **Alice and Bob each measure `X` locally.**  The joint local `X` measurement is the cascade of
the two single-qubit `X` sign measurements — `xSignMeasurement` on the left factor (Alice), then on
the right factor (Bob) — a genuine four-outcome `Measurement (Fin 2 × Fin 2)`.  The Hadamard-basis
mirror of `localZMeasurement`. -/
def localXMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ qubit) :=
  (xSignMeasurement.onLeft qubit).cascade (xSignMeasurement.onRight qubit)

/-- The joint local-`X` measurement operator at outcome `(a, b)` is the Hadamard projector
`|x_a x_b⟩⟨x_a x_b| = |x_a⟩⟨x_a| ⊗ |x_b⟩⟨x_b|`: the cascade composes the two single-qubit `X`
projectors on disjoint factors, which `TensorProduct.mapL` and `rankOne_tmul_self` reassemble into
the product. -/
theorem localXMeasurement_op (a b : Fin 2) :
    localXMeasurement.op (a, b)
      = rankOne ℂ (pmQubit a ⊗ₜ[ℂ] pmQubit b) (pmQubit a ⊗ₜ[ℂ] pmQubit b) := by
  have h : localXMeasurement.op (a, b)
      = TensorProduct.mapL (xSignMeasurement.op a) (xSignMeasurement.op b) := by
    rw [localXMeasurement, Measurement.cascade_op, Measurement.onRight_op, Measurement.onLeft_op]
    exact (TensorProduct.mapL_comp _ _ _ _).symm.trans
      (by simp only [← ContinuousLinearMap.mul_def, one_mul, mul_one])
  rw [h, xSignMeasurement_op, xSignMeasurement_op]
  exact (InnerProductSpace.rankOne_tmul_self (pmQubit a) (pmQubit b)).symm

/-- The POVM effect of the local-`X` measurement at `(a, b)` is the projector `|x_a x_b⟩⟨x_a x_b|`
itself: the operator is a unit rank-one projector, hence its own effect
(`adjoint_rankOne_comp_self`). -/
theorem localXMeasurement_toPOVM_elements (a b : Fin 2) :
    localXMeasurement.toPOVM.elements (a, b)
      = rankOne ℂ (pmQubit a ⊗ₜ[ℂ] pmQubit b) (pmQubit a ⊗ₜ[ℂ] pmQubit b) := by
  rw [Measurement.toPOVM_elements, localXMeasurement_op]
  refine InnerProductSpace.adjoint_rankOne_comp_self ?_
  fin_cases a <;> fin_cases b
  exacts [(qubitPlus.tmul qubitPlus).normalized, (qubitPlus.tmul qubitMinus).normalized,
    (qubitMinus.tmul qubitPlus).normalized, (qubitMinus.tmul qubitMinus).normalized]

/-- **The compiled phase-flip statistic** `a + b`: Alice and Bob record whether their two local `X`
outcomes *disagree* (`a + b = 1`, a phase flip) or *agree* (`a + b = 0`). -/
def xParity : Fin 2 × Fin 2 → Fin 2 := fun p => p.1 + p.2

/-- **The phase-flip outcome coordinate** of the Bell measurement: `|β_xy⟩` carries a phase flip iff
`x = 1`, so coarse-graining the Bell measurement along `phaseFlipIndex` is exactly the `Π_pf`
measurement. -/
def phaseFlipIndex : Fin 2 × Fin 2 → Fin 2 := fun p => p.1

/-- **`Π_pf` is the "phase flip detected" effect of the Bell measurement.**  Coarse-graining the
Bell measurement along `phaseFlipIndex` and reading outcome `1` gives the effect
`|β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁| = phaseFlipProjector`: reading `1` from `bellMeasurement.coarseGrain
phaseFlipIndex` *is* measuring `Π_pf`. -/
theorem phaseFlipProjector_eq_bellMap :
    (bellMeasurement.toPOVM.map phaseFlipIndex).elements 1 = phaseFlipProjector := by
  have hfib : (Finset.univ.filter fun p : Fin 2 × Fin 2 => phaseFlipIndex p = 1)
      = {(1, 0), (1, 1)} := by decide
  rw [POVM.map_elements, hfib, Finset.sum_pair (by decide),
    bellMeasurement_toPOVM_elements_eq_bellProjector,
    bellMeasurement_toPOVM_elements_eq_bellProjector]
  rfl

/-! ### The Hadamard products `|±⟩⊗|±⟩` as `±`-combinations of Bell vectors -/

/-- **`|++⟩ = (|β₀₀⟩ + |β₀₁⟩)/√2`.**  The local-`X` product `|+⟩⊗|+⟩` is the normalised sum of the
two Bell vectors sharing phase-flip label `x = 0`; the Hadamard-basis mirror of the computational
decomposition of the Bell vectors. -/
theorem pmQubit_zero_tmul_zero_eq_bell :
    pmQubit 0 ⊗ₜ[ℂ] pmQubit 0
      = (Real.sqrt 2 : ℂ)⁻¹ • ((bellState 0 0).vec + (bellState 0 1).vec) := by
  change qubitPlus.vec ⊗ₜ[ℂ] qubitPlus.vec = _
  rw [qubitPlus_vec_eq_smul_add, TensorProduct.smul_tmul_smul, bellState_vec, bellState_vec,
    bellBasisVec, bellBasisVec]
  simp only [Concrete.invSqrt2, Fin.val_zero, pow_zero]
  simp only [smul_tmul_bridge]
  simp only [one_smul, Fin.reduceAdd, PureState.tmul_vec, ← smul_add, smul_smul]
  congr 1
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- **`|−−⟩ = (|β₀₀⟩ − |β₀₁⟩)/√2`.**  The local-`X` product `|−⟩⊗|−⟩` is the normalised difference
of the two Bell vectors sharing phase-flip label `x = 0`. -/
theorem pmQubit_one_tmul_one_eq_bell :
    pmQubit 1 ⊗ₜ[ℂ] pmQubit 1
      = (Real.sqrt 2 : ℂ)⁻¹ • ((bellState 0 0).vec - (bellState 0 1).vec) := by
  change qubitMinus.vec ⊗ₜ[ℂ] qubitMinus.vec = _
  rw [qubitMinus_vec_eq_smul_sub, TensorProduct.smul_tmul_smul, bellState_vec, bellState_vec,
    bellBasisVec, bellBasisVec]
  simp only [Concrete.invSqrt2, Fin.val_zero, pow_zero]
  simp only [smul_tmul_bridge]
  simp only [one_smul, Fin.reduceAdd, PureState.tmul_vec, ← smul_sub, smul_smul]
  congr 1
  simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

/-- **`|+−⟩ = (|β₁₀⟩ − |β₁₁⟩)/√2`.**  The local-`X` product `|+⟩⊗|−⟩` is the normalised difference
of the two Bell vectors sharing phase-flip label `x = 1`. -/
theorem pmQubit_zero_tmul_one_eq_bell :
    pmQubit 0 ⊗ₜ[ℂ] pmQubit 1
      = (Real.sqrt 2 : ℂ)⁻¹ • ((bellState 1 0).vec - (bellState 1 1).vec) := by
  change qubitPlus.vec ⊗ₜ[ℂ] qubitMinus.vec = _
  rw [qubitPlus_vec_eq_smul_add, qubitMinus_vec_eq_smul_sub, TensorProduct.smul_tmul_smul,
    bellState_vec, bellState_vec, bellBasisVec, bellBasisVec]
  simp only [Concrete.invSqrt2, Fin.val_one, pow_one]
  simp only [smul_tmul_bridge]
  simp only [neg_one_smul, Fin.reduceAdd, PureState.tmul_vec, ← smul_sub, smul_smul]
  congr 1
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_sub]
  abel

/-- **`|−+⟩ = (|β₁₀⟩ + |β₁₁⟩)/√2`.**  The local-`X` product `|−⟩⊗|+⟩` is the normalised sum of the
two Bell vectors sharing phase-flip label `x = 1`. -/
theorem pmQubit_one_tmul_zero_eq_bell :
    pmQubit 1 ⊗ₜ[ℂ] pmQubit 0
      = (Real.sqrt 2 : ℂ)⁻¹ • ((bellState 1 0).vec + (bellState 1 1).vec) := by
  change qubitMinus.vec ⊗ₜ[ℂ] qubitPlus.vec = _
  rw [qubitMinus_vec_eq_smul_sub, qubitPlus_vec_eq_smul_add, TensorProduct.smul_tmul_smul,
    bellState_vec, bellState_vec, bellBasisVec, bellBasisVec]
  simp only [Concrete.invSqrt2, Fin.val_one, pow_one]
  simp only [smul_tmul_bridge]
  simp only [neg_one_smul, Fin.reduceAdd, PureState.tmul_vec, ← smul_add, smul_smul]
  congr 1
  simp only [TensorProduct.sub_tmul, TensorProduct.tmul_add]
  abel

/-- **The heart of Exercise 12.32 (phase-flip half).**  For every merged outcome `k`, the effect of
the coarse-grained local-`X` measurement (grouped by the parity statistic `xParity`) equals the
effect of the coarse-grained Bell measurement (grouped by `phaseFlipIndex`, i.e. the `Π_pf`
measurement).  Since a POVM effect determines the Born statistics on *every* state, the two produce
identical statistics — this is N&C's claim that the local `X` measurements reproduce the `Π_pf`
statistics despite `X ⊗ I`, `I ⊗ X` not commuting with the Bell basis.

The fibres over `k` are `{(0,0),(1,1)}` vs `{(0,0),(0,1)}` (agree, `k = 0`) and
`{(0,1),(1,0)}` vs `{(1,0),(1,1)}` (phase flip, `k = 1`); in each case the local side is the pair
`|±⟩⊗|±⟩` of Hadamard products, which are the normalised sum/difference `(β_x0 ± β_x1)/√2` of the
Bell pair sharing the phase-flip label `x`, equal by `rankOne_sqrtTwoInv_add_sub_self`. -/
theorem localXMeasurement_map_elements_eq (k : Fin 2) :
    (localXMeasurement.toPOVM.map xParity).elements k
      = (bellMeasurement.toPOVM.map phaseFlipIndex).elements k := by
  rw [POVM.map_elements, POVM.map_elements, Finset.sum_filter, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, xParity, phaseFlipIndex, localXMeasurement_toPOVM_elements,
    bellMeasurement_toPOVM_elements_eq_bellProjector]
  fin_cases k <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, add_zero, zero_add, Fin.reduceAdd,
      Fin.reduceEq, reduceIte]
  · rw [pmQubit_zero_tmul_zero_eq_bell, pmQubit_one_tmul_one_eq_bell]
    exact rankOne_sqrtTwoInv_add_sub_self (𝕜 := ℂ) (bellState 0 0).vec (bellState 0 1).vec
  · rw [pmQubit_zero_tmul_one_eq_bell, pmQubit_one_tmul_zero_eq_bell]
    conv_lhs => rw [add_comm]
    exact rankOne_sqrtTwoInv_add_sub_self (𝕜 := ℂ) (bellState 1 0).vec (bellState 1 1).vec

end AxQM
