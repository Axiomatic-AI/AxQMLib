/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.Teleportation

/-!
# AxQM.Postulates.API — CNOT propagates Pauli byproducts

The **Clifford propagation rules for `CNOT`** — how a single-qubit Pauli gate on an input of `CNOT`
commutes to the output — and, as their combined form, the propagation of a **Pauli byproduct**
`X^y Z^x` (`pauliByproduct`) through `CNOT`.  This is the algebraic crux of Nielsen & Chuang
**Problem 4.6** ("Universality with prior entanglement").

## The role in Problem 4.6

Problem 4.6 asks to show that `{single-qubit unitaries, Bell-basis measurement, four-qubit state
preparation}` is a universal set, given that `{CNOT, single-qubit gates}` is.  Since single-qubit
gates are shared, it suffices to implement a `CNOT` from the new resources, which is done by
**gate teleportation** (Gottesman–Chuang): the two input qubits are teleported through the
four-qubit resource state `cnotGateTeleportResource` (a `CNOT` pre-applied to two Bell pairs), and
`CNOT` — having been applied to the resource — acts on the teleported inputs.  Each teleportation
leaves a **Pauli byproduct** `X^y Z^x` (`pauliByproduct`, resource #1 of Problem 4.6) on its output;
these byproducts sit on the *input* side of the pre-applied `CNOT`.  The protocol succeeds — with a
*single-qubit* final correction, as the resource set demands — precisely because **conjugating
single-qubit Pauli byproducts by `CNOT` again yields single-qubit Pauli byproducts** (the Clifford
property).  `cnotGate_comp_pauliByproduct_tmul` is exactly that fact, so it is the reason the
gate-teleportation corrections stay single-qubit and hence the reason the alternative resource set
is universal.

## What is formalised

The **elementary propagation rules** (the four generators, `CNOT` control = left qubit, target =
right qubit):

* `cnotGate_comp_pauliXGate_onRight` — `X` on the **target** commutes with `CNOT`:
  `CNOT · (1 ⊗ X) = (1 ⊗ X) · CNOT`.
* `cnotGate_comp_pauliXGate_onLeft` — `X` on the **control** copies to the target:
  `CNOT · (X ⊗ 1) = (X ⊗ 1) · (1 ⊗ X) · CNOT`.
* `cnotGate_comp_pauliZGate_onLeft` — `Z` on the **control** commutes with `CNOT`:
  `CNOT · (Z ⊗ 1) = (Z ⊗ 1) · CNOT`.
* `cnotGate_comp_pauliZGate_onRight` — `Z` on the **target** copies back to the control:
  `CNOT · (1 ⊗ Z) = (Z ⊗ 1) · (1 ⊗ Z) · CNOT`.

The **combined byproduct rule** assembled from them:

* `cnotGate_comp_pauliByproduct_tmul` —
  `CNOT · (X^{y₁}Z^{x₁} ⊗ X^{y₂}Z^{x₂}) = (X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) · CNOT`,
  i.e. a pair of single-qubit byproducts on the inputs of `CNOT` propagates to a pair of
  single-qubit byproducts on its outputs (control `Z`-exponent `x₁ ⊕ x₂`, target `X`-exponent
  `y₁ ⊕ y₂`).  Stated over `pauliByproduct` so it reads as "the teleportation corrections propagate
  through `CNOT` to teleportation corrections".

Plus the reusable operator-level (arbitrary-vector) companions of the `Evolution` factorisation
lemmas (`Evolution.tmul_op_tmul`, `Evolution.onLeft_op_tmul`, `Evolution.onRight_op_tmul`), general
over `{S T : QSystem}` like their `evolvePure` siblings.

## Design notes

* **Statement shape (fidelity).**  Each rule is a genuine equality of the gate `Evolution`s (values
  of `Evolution`, Postulate 5), so it holds on *every* input, not up to phase or on
  basis states.  The commutation form `CNOT · P = P' · CNOT` (rather than the conjugation form
  `CNOT · P · CNOT = P'`) is what the gate-teleportation protocol uses — pushing a byproduct from
  the input side of `CNOT` to the output side — and needs no separate `CNOT² = 1` input.
* **Proof.**  Each rule is verified on the four computational-basis inputs via
  `twoQubit_evolution_ext`, dropping to the underlying vectors (`PureState.ext`) and computing with
  the `CNOT` truth table and the Pauli actions.  The `X` rules are sign-free (they stay at the
  `PureState`/`evolvePure` level); the `Z` rules carry the phase `Z|i⟩ = (-1)ⁱ|i⟩`, so they descend
  to the vector level where the sign is a scalar, reusing the raw-tensor-head homogeneity lemma
  `cnotGate_op_smul` (of `Postulates/API/CnotXBasis.lean`) to move the phase through `CNOT`.
* **Reuse.**  The same Clifford conjugation facts recur throughout the stabiliser formalism of
  Chapter 10.  Problem 4.6 itself is in `AxQM/NC/Ch4/Problem4_6.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### Operator-level companions of the `Evolution` factorisation lemmas

The `evolvePure`-level factorisation lemmas of `Postulates/Composite.lean` /
`Postulates/API/ControlledControlledUnitary.lean` (`Evolution.tmul_evolvePure`,
`Evolution.onLeft_evolvePure`, `Evolution.onRight_evolvePure`) act on *pure states*.  Their
operator-level companions below act on *arbitrary vectors* `a, b` (needed once a phase `(-1)ⁱ`
turns a basis state into `(-1)ⁱ • |i⟩`, no longer a `PureState`); they are stated general over the
factor systems `{S T : QSystem}` to match their siblings and `Evolution.tmul_op`.  (The gate
composite `(U · V) ψ = U (V ψ)` is the existing `Evolution.evolvePure_comp` of
`Postulates/Evolution.lean`, reused directly.) -/

/-- **Operator action of a product gate on a pure tensor:** `(U ⊗ V)(a ⊗ b) = (U a) ⊗ (V b)` at the
vector level, for arbitrary vectors `a, b` (the operator-level companion of
`Evolution.tmul_evolvePure`).  Since `(U ⊗ V).op` is *definitionally* `TensorProduct.mapL U.op V.op`
(`Evolution.tmul_op`), this is a direct application of `TensorProduct.mapL_tmul`. -/
theorem Evolution.tmul_op_tmul {S T : QSystem} (U : Evolution S) (V : Evolution T)
    (a : S.space) (b : T.space) :
    (U ⊗ V).op (a ⊗ₜ[ℂ] b) = U.op a ⊗ₜ[ℂ] V.op b :=
  TensorProduct.mapL_tmul U.op V.op a b

/-- **Operator action of a left-factor gate on a pure tensor:** `(U ⊗ 1)(a ⊗ b) = (U a) ⊗ b` at the
vector level, for arbitrary vectors `a, b` (the operator-level companion of
`Evolution.onLeft_evolvePure`). -/
theorem Evolution.onLeft_op_tmul {S : QSystem} (U : Evolution S) (T : QSystem)
    (a : S.space) (b : T.space) :
    (U.onLeft T).op (a ⊗ₜ[ℂ] b) = U.op a ⊗ₜ[ℂ] b := by
  rw [Evolution.onLeft, Evolution.tmul_op_tmul, Evolution.id_op, one_apply_eq_self]

/-- **Operator action of a right-factor gate on a pure tensor:** `(1 ⊗ V)(a ⊗ b) = a ⊗ (V b)` at
the vector level, for arbitrary vectors `a, b` (the operator-level companion of
`Evolution.onRight_evolvePure`). -/
theorem Evolution.onRight_op_tmul {T : QSystem} (V : Evolution T) (S : QSystem)
    (a : S.space) (b : T.space) :
    (V.onRight S).op (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] V.op b := by
  rw [Evolution.onRight, Evolution.tmul_op_tmul, Evolution.id_op, one_apply_eq_self]

/-- **Operator of a right-factor gate:** `(V.onRight S).op = TensorProduct.mapL 1 V.op` — the full
`1 ⊗ V` operator, the operator-valued companion of the pointwise `Evolution.onRight_op_tmul`.
Unfolds `Evolution.onRight = id ⊗ V` through `Evolution.tmul_op` (`(U ⊗ V).op = mapL U.op V.op`) and
`Evolution.id_op` (`id.op = 1`), stated as a `TensorProduct.mapL` identity so a right-factor gate
composes with other `TensorProduct.mapL`s. -/
theorem Evolution.onRight_op {T : QSystem} (V : Evolution T) (S : QSystem) :
    (V.onRight S).op = TensorProduct.mapL (1 : S.space →L[ℂ] S.space) V.op := by
  simp only [Evolution.onRight, Evolution.tmul_op, Evolution.id_op]
  rfl

/-- **Operator of a left-factor gate:** `(U.onLeft T).op = TensorProduct.mapL U.op 1` — the full
`U ⊗ 1` operator, the operator-valued companion of the pointwise `Evolution.onLeft_op_tmul` and the
left-factor mirror of `Evolution.onRight_op`. Unfolds `Evolution.onLeft = U ⊗ id` through
`Evolution.tmul_op` and `Evolution.id_op`, stated as a `TensorProduct.mapL` identity so a
left-factor gate composes with other `TensorProduct.mapL`s. -/
theorem Evolution.onLeft_op {S : QSystem} (U : Evolution S) (T : QSystem) :
    (U.onLeft T).op = TensorProduct.mapL U.op (1 : T.space →L[ℂ] T.space) := by
  simp only [Evolution.onLeft, Evolution.tmul_op, Evolution.id_op]
  rfl

/-! ### Elementary CNOT–Pauli propagation rules -/

/-- **`X` on the target commutes with `CNOT`:** `CNOT · (1 ⊗ X) = (1 ⊗ X) · CNOT`.  Flipping the
target before or after `CNOT` gives the same gate, since `CNOT` only adds the control to the target.
The `Z₂`-linear (sign-free) generator; a basis-state verification via `twoQubit_evolution_ext`. -/
theorem cnotGate_comp_pauliXGate_onRight :
    cnotGate.comp (pauliXGate.onRight qubit) = (pauliXGate.onRight qubit).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp, Evolution.onRight_evolvePure,
    pauliXGate_evolvePure_qubitBasis, cnotGate_evolvePure_qubitBasis,
    cnotGate_evolvePure_qubitBasis, Evolution.onRight_evolvePure,
    pauliXGate_evolvePure_qubitBasis, add_right_comm]

/-- **`X` on the control copies to the target through `CNOT`:**
`CNOT · (X ⊗ 1) = (X ⊗ 1) · (1 ⊗ X) · CNOT`.  Flipping the control before `CNOT` also flips the
value copied onto the target, so pushing the `X` to the output side leaves an `X` on *both* qubits.
A basis-state verification via `twoQubit_evolution_ext` (sign-free). -/
theorem cnotGate_comp_pauliXGate_onLeft :
    cnotGate.comp (pauliXGate.onLeft qubit)
      = ((pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit)).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  rw [Evolution.evolvePure_comp, Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis,
    cnotGate_evolvePure_qubitBasis, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    cnotGate_evolvePure_qubitBasis, Evolution.onRight_evolvePure, pauliXGate_evolvePure_qubitBasis,
    Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis, add_assoc]

/-- **`Z` on the control commutes with `CNOT`:** `CNOT · (Z ⊗ 1) = (Z ⊗ 1) · CNOT`.  `Z` on the
control multiplies by the phase `(-1)ᶜ`, which `CNOT` (leaving the control fixed) does not disturb.
Verified on the computational basis via `twoQubit_evolution_ext`, descending to the vector level for
the phase. -/
theorem cnotGate_comp_pauliZGate_onLeft :
    cnotGate.comp (pauliZGate.onLeft qubit) = (pauliZGate.onLeft qubit).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  apply PureState.ext
  simp only [Evolution.evolvePure_comp, Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [Evolution.onLeft_op_tmul, pauliZGate_op_apply_qubitBasis, ← TensorProduct.smul_tmul',
    cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul]
  rw [Evolution.onLeft_op_tmul, pauliZGate_op_apply_qubitBasis, ← TensorProduct.smul_tmul']
  rfl

/-- **`Z` on the target copies back to the control through `CNOT`:**
`CNOT · (1 ⊗ Z) = (Z ⊗ 1) · (1 ⊗ Z) · CNOT`.  `Z` on the target multiplies `|t⟩` by `(-1)ᵗ`; after
`CNOT` maps `t ↦ t ⊕ c`, the same phase reads as `(-1)^{t⊕c}`, i.e. a `Z` on *both* qubits.
Verified on the computational basis via `twoQubit_evolution_ext`, descending to the vector level
for the phase. -/
theorem cnotGate_comp_pauliZGate_onRight :
    cnotGate.comp (pauliZGate.onRight qubit)
      = ((pauliZGate.onLeft qubit).comp (pauliZGate.onRight qubit)).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  apply PureState.ext
  simp only [Evolution.evolvePure_comp, Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [Evolution.onRight_op_tmul, pauliZGate_op_apply_qubitBasis, TensorProduct.tmul_smul,
    cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul]
  rw [Evolution.onRight_op_tmul, pauliZGate_op_apply_qubitBasis,
    Evolution.onLeft_op_tmul, pauliZGate_op_apply_qubitBasis, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul]
  congr 1
  fin_cases c <;> fin_cases t <;> simp

/-! ### The combined Pauli byproduct propagation -/

/-- **`CNOT` propagates single-qubit Pauli byproducts to single-qubit Pauli byproducts.**
For the teleportation byproducts `X^{y₁}Z^{x₁}` (control) and `X^{y₂}Z^{x₂}` (target),
`CNOT · (X^{y₁}Z^{x₁} ⊗ X^{y₂}Z^{x₂}) = (X^{y₁}Z^{x₁ ⊕ x₂} ⊗ X^{y₁ ⊕ y₂}Z^{x₂}) · CNOT`,
i.e. `cnotGate.comp (pauliByproduct x₁ y₁ ⊗ pauliByproduct x₂ y₂)
= (pauliByproduct (x₁ + x₂) y₁ ⊗ pauliByproduct x₂ (y₁ + y₂)).comp cnotGate`.

This is the Clifford property behind Nielsen & Chuang **Problem 4.6**: a pair of single-qubit Pauli
byproducts on the inputs of `CNOT` (the corrections left by teleporting the two input qubits into
the gate-teleportation resource state) commutes to a pair of single-qubit Pauli byproducts on the
outputs — the control acquires the target's `Z`-exponent (`x₁ ⊕ x₂`) and the target acquires the
control's `X`-exponent (`y₁ ⊕ y₂`).  Because the propagated corrections are again single-qubit
unitaries, the gate-teleportation protocol implements `CNOT` using only the resource set's
single-qubit corrections; that is why `{single-qubit unitaries, Bell-basis measurement, four-qubit
state preparation}` is universal.

Proved directly on the four computational-basis inputs (`twoQubit_evolution_ext` + `PureState.ext`):
each byproduct acts as `X^y Z^x|j⟩ = (-1)^{x·j}|j ⊕ y⟩` (`pauliByproduct_op_apply_qubitBasis`), and
after applying the `CNOT` truth table both sides reduce to a common signed computational-basis
vector whose phase is checked by cases. -/
theorem cnotGate_comp_pauliByproduct_tmul (x₁ y₁ x₂ y₂ : Fin 2) :
    cnotGate.comp (pauliByproduct x₁ y₁ ⊗ pauliByproduct x₂ y₂)
      = (pauliByproduct (x₁ + x₂) y₁ ⊗ pauliByproduct x₂ (y₁ + y₂)).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  apply PureState.ext
  simp only [Evolution.evolvePure_comp, Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [Evolution.tmul_op_tmul, pauliByproduct_op_apply_qubitBasis,
    pauliByproduct_op_apply_qubitBasis, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul, cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul]
  rw [cnotGate_op_qubitBasisVec_tmul, Evolution.tmul_op_tmul,
    pauliByproduct_op_apply_qubitBasis, pauliByproduct_op_apply_qubitBasis,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    show t + y₂ + (c + y₁) = t + c + (y₁ + y₂) by abel]
  congr 1
  fin_cases x₁ <;> fin_cases x₂ <;> fin_cases c <;> fin_cases t <;> simp

end AxQM
