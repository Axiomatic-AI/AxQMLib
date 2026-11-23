/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.QubitThree

/-!
# AxQM.Postulates.API — the doubly-controlled gate `C²(U)` and three-qubit machinery

Infrastructure for Nielsen & Chuang's **multiply-controlled** operations
(N&C §4.3, eq. 4.29): the doubly-controlled gate `C²(U)` and the tools needed to verify
three-qubit circuit identities against it (e.g. Exercise 4.21 — Figure 4.8). It sits above
`ControlledUnitary` (the single-qubit-controlled `C(U)` and `CNOT`) and is reused wherever a
two-control gate appears (the Toffoli gate `C²(X)`, Exercises 4.21–4.25).

## What is formalised

* **Factorised action of composite evolutions.** `Evolution.id_evolvePure`,
  `Evolution.tmul_evolvePure`, `Evolution.onLeft_evolvePure`, `Evolution.onRight_evolvePure` — the
  Schrödinger action of `1`, `U ⊗ V`, `U ⊗ 1` and `1 ⊗ V` on product pure states, all definitional
  (`mapL` on a pure tensor is factorwise). These are the generic tools for computing a gate's
  action on a computational-basis input, one tensor factor at a time.
* `ccontrolledUnitary U` — the **doubly-controlled gate** `C²(U) = C(C(U))` on the three-qubit
  system `qubit ⊗ (qubit ⊗ qubit)`: apply the single-qubit unitary `U` to the last qubit exactly
  when *both* of the first two ("control") qubits are `|1⟩` (N&C eq. 4.29 with `n = 2`, `k = 1`).
  It is literally the single-qubit-controlled gate `controlledUnitary` applied twice, so it is a
  genuine `Evolution` (its unitarity is inherited, no new obligation).
* `ccontrolledUnitary_evolvePure_ketZero_left` / `ccontrolledUnitary_evolvePure_ketOne_left` — the
  **defining action** split on the first control: control `|0⟩` leaves the other two qubits
  untouched; control `|1⟩` applies the *single*-controlled `C(U)` to the remaining two qubits.
  Together with the `controlledUnitary` action lemmas these give the full `C²(U)` truth table.
* `threeQubit_evolution_ext` — **computational-basis extensionality** for three-qubit gates: two
  evolutions of `qubit ⊗ (qubit ⊗ qubit)` are equal as soon as they agree on every computational
  basis state `|q₁⟩ ⊗ |q₂⟩ ⊗ |q₃⟩`. This is what turns "verify the circuit on each of the eight
  basis inputs" into a genuine equality of unitary gates.

## Design notes

* **`C²(U) = C(C(U))` (fidelity).** N&C defines `Cⁿ(U)` by `Cⁿ(U)|x₁…xₙ⟩|ψ⟩ = |x₁…xₙ⟩ U^{x₁⋯xₙ}|ψ⟩`
  (eq. 4.29). For `n = 2` this is exactly `C(C(U))`: the outer `C` conditions on the first control,
  and its target — the two-qubit gate `C(U)` — conditions on the second, so `U` fires iff both bits
  are set. Taking the right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)` (control₁ ⊗
  (control₂ ⊗ target)) makes this the definitional `controlledUnitary (controlledUnitary U)`, with
  *no* associator bookkeeping. All five gates of a Figure-4.8-style decomposition then live on this
  same system.
* **The extensionality bridge.** A unitary on the eight-dimensional space is determined by its
  action on the computational basis `|q₁⟩⊗(|q₂⟩⊗|q₃⟩)`. The proof reduces `Evolution` equality to
  operator equality (`Evolution.ext`), then to linear-map equality
  (`ContinuousLinearMap.coe_injective`), and applies `Module.Basis.ext` to the tensor-product
  orthonormal basis `EuclideanSpace.basisFun ⊗ (EuclideanSpace.basisFun ⊗ EuclideanSpace.basisFun)`
  (via `OrthonormalBasis.tensorProduct`), whose eight vectors are exactly the
  `|qᵢ⟩ = (qubitBasis _).vec`.
  The `evolvePure` hypothesis supplies agreement on those vectors after unfolding `evolvePure_vec`
  and `PureState.tmul_vec`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-! ### Factorised Schrödinger action of composite evolutions -/

/-- **The identity evolution acts trivially on pure states:** `1 · ψ = ψ`. -/
theorem Evolution.id_evolvePure (ψ : PureState S) : Evolution.id.evolvePure ψ = ψ := by
  apply PureState.ext; rfl

/-- **A product gate acts factorwise on a product state:** `(U ⊗ V)(ψ ⊗ φ) = (Uψ) ⊗ (Vφ)`. The
tensor operator `U ⊗ V = TensorProduct.mapL U.op V.op` sends the pure tensor `ψ.vec ⊗ₜ φ.vec` to
`U.op ψ.vec ⊗ₜ V.op φ.vec`, definitionally. -/
theorem Evolution.tmul_evolvePure (U : Evolution S) (V : Evolution T)
    (ψ : PureState S) (φ : PureState T) :
    (U ⊗ V).evolvePure (ψ ⊗ φ) = (U.evolvePure ψ) ⊗ (V.evolvePure φ) := by
  apply PureState.ext; rfl

/-- **A gate on the left factor acts only there:** `(U ⊗ 1)(ψ ⊗ φ) = (Uψ) ⊗ φ`. -/
theorem Evolution.onLeft_evolvePure (U : Evolution S) (T : QSystem)
    (ψ : PureState S) (φ : PureState T) :
    (U.onLeft T).evolvePure (ψ ⊗ φ) = (U.evolvePure ψ) ⊗ φ := by
  apply PureState.ext; rfl

/-- **A gate on the right factor acts only there:** `(1 ⊗ V)(ψ ⊗ φ) = ψ ⊗ (Vφ)`. -/
theorem Evolution.onRight_evolvePure (V : Evolution T) (S : QSystem)
    (ψ : PureState S) (φ : PureState T) :
    (V.onRight S).evolvePure (ψ ⊗ φ) = ψ ⊗ (V.evolvePure φ) := by
  apply PureState.ext; rfl

/-! ### The doubly-controlled gate `C²(U)` -/

/-- **The doubly-controlled gate** `C²(U)` (Nielsen & Chuang eq. 4.29, `n = 2`, `k = 1`) on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)`: the single-qubit unitary `U` is applied to the last
qubit exactly when *both* of the first two control qubits are `|1⟩`. It is the single-controlled
gate `controlledUnitary` iterated once, `C²(U) = C(C(U))`: the outer control is the first qubit and
its target is the two-qubit gate `C(U)` conditioning on the second qubit. Being a composition of
`controlledUnitary`, it is automatically a unitary `Evolution`. -/
def ccontrolledUnitary (U : Evolution qubit) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (controlledUnitary U)

/-- **`C²(U)`, first control `|0⟩`:** the remaining two qubits are untouched,
`C²(U)(|0⟩ ⊗ ψ) = |0⟩ ⊗ ψ`. -/
theorem ccontrolledUnitary_evolvePure_ketZero_left (U : Evolution qubit)
    (ψ : PureState (qubit ⊗ qubit)) :
    (ccontrolledUnitary U).evolvePure ((qubitBasis 0) ⊗ ψ) = (qubitBasis 0) ⊗ ψ :=
  controlledUnitary_evolvePure_ketZero (controlledUnitary U) ψ

/-- **`C²(U)`, first control `|1⟩`:** the *single*-controlled gate `C(U)` is applied to the
remaining two qubits, `C²(U)(|1⟩ ⊗ ψ) = |1⟩ ⊗ C(U)ψ`. Conditioning `C(U)` further on the second
qubit yields the full `C²(U)` truth table: `U` fires on the target iff both controls are `|1⟩`. -/
theorem ccontrolledUnitary_evolvePure_ketOne_left (U : Evolution qubit)
    (ψ : PureState (qubit ⊗ qubit)) :
    (ccontrolledUnitary U).evolvePure ((qubitBasis 1) ⊗ ψ)
      = (qubitBasis 1) ⊗ ((controlledUnitary U).evolvePure ψ) :=
  controlledUnitary_evolvePure_ketOne (controlledUnitary U) ψ

/-! ### Computational-basis extensionality for three-qubit gates -/

/-- **A three-qubit gate is determined by its action on the computational basis.** Two evolutions
`A`, `B` of `qubit ⊗ (qubit ⊗ qubit)` are equal as soon as they agree on every computational-basis
state `|q₁⟩ ⊗ (|q₂⟩ ⊗ |q₃⟩)`, `qᵢ ∈ {0, 1}`. This is the tool that turns a case-by-case verification
of a circuit on the eight basis inputs into a genuine equality of unitary gates.

The proof reduces to operator equality (`Evolution.ext`), then linear-map equality
(`ContinuousLinearMap.coe_injective`), and applies `Module.Basis.ext` to the tensor-product basis
built from `EuclideanSpace.basisFun` by `OrthonormalBasis.tensorProduct`, whose basis vectors are
the computational-basis unit vectors `(qubitBasis _).vec`; the hypothesis supplies the required
agreement after unfolding `evolvePure_vec` and `PureState.tmul_vec`. -/
theorem threeQubit_evolution_ext {A B : Evolution (qubit ⊗ (qubit ⊗ qubit))}
    (h : ∀ q1 q2 q3 : Fin 2,
      A.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
        = B.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))) :
    A = B := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  let bq : OrthonormalBasis (Fin 2) ℂ qubit.space := EuclideanSpace.basisFun (Fin 2) ℂ
  have hbq : ∀ i : Fin 2, bq i = (qubitBasis i).vec := fun i => by
    rw [qubitBasis_vec]; exact EuclideanSpace.basisFun_apply (Fin 2) ℂ i
  refine Module.Basis.ext (bq.tensorProduct (bq.tensorProduct bq)).toBasis ?_
  rintro ⟨q1, q2, q3⟩
  have hb : (bq.tensorProduct (bq.tensorProduct bq)).toBasis (q1, q2, q3)
      = (qubitBasis q1).vec ⊗ₜ[ℂ] ((qubitBasis q2).vec ⊗ₜ[ℂ] (qubitBasis q3).vec) := by
    rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
      OrthonormalBasis.tensorProduct_apply, hbq, hbq, hbq]
  rw [hb]
  have hh := congrArg PureState.vec (h q1 q2 q3)
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec] at hh
  exact hh

/-! ### The Toffoli gate `C²(X)`

(The three-qubit computational basis `qubitThreeBasis` used as the reference frame for
`toffoliGate`'s truth table now lives in `Postulates/API/QubitThree.lean`, imported above, so it can
be shared without dragging the Toffoli machinery into its other consumers.) -/

/-- **The Toffoli gate** (controlled-controlled-`NOT`, `C²(X)`; Nielsen & Chuang §1.3.4) on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)`: it flips the last (target) qubit exactly when *both*
of the first two control qubits are `|1⟩`. It is the doubly-controlled gate `ccontrolledUnitary`
with `U = X`, exactly mirroring `cnotGate = controlledUnitary pauliXGate`. The canonical two-control
gate, reused throughout Chapter 4 (Exercises 4.24–4.27). -/
def toffoliGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) := ccontrolledUnitary pauliXGate

/-- **The Toffoli truth table** (Nielsen & Chuang §1.3.4):
`Toffoli|q₁, q₂, q₃⟩ = |q₁, q₂, q₃ ⊕ q₁·q₂⟩` — the control qubits `q₁, q₂` are unchanged and the
target `q₃` is flipped exactly when both are `1` (`q₃ + q₁ * q₂` in `Fin 2`, using that `Fin 2`
multiplication is the logical `AND`). -/
theorem toffoliGate_evolvePure_qubitBasis (q1 q2 q3 : Fin 2) :
    toffoliGate.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis (q3 + q1 * q2))) := by
  rw [toffoliGate]
  fin_cases q1 <;> fin_cases q2 <;>
    simp only [Fin.mk_zero, Fin.mk_one, ccontrolledUnitary_evolvePure_ketZero_left,
      ccontrolledUnitary_evolvePure_ketOne_left, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, pauliXGate_evolvePure_qubitBasis, mul_zero, mul_one,
      add_zero]

/-- **The Toffoli truth table at the raw-operator level:** `C²(X) |a, b, t⟩ = |a, b, t ⊕ ab⟩` on
the underlying vectors — the `Evolution.op`-on-`.vec` form of `toffoliGate_evolvePure_qubitBasis`.
The canonical op-level Toffoli truth table, sitting beside `toffoliGate` and its `evolvePure`
companion; reused wherever a phase must be moved through a Toffoli (e.g.
`RzThreeFifthsCircuit`, `ToffoliPauliPropagation`). -/
theorem toffoliGate_op_qubitBasis_vec (a b t : Fin 2) :
    toffoliGate.op ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t))).vec
      = ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis (t + a * b)))).vec := by
  rw [← Evolution.evolvePure_vec, toffoliGate_evolvePure_qubitBasis]

/-- **The Toffoli truth table on bare tensors:** `C²(X)(|a⟩ ⊗ |b⟩ ⊗ |c⟩) = |a⟩ ⊗ |b⟩ ⊗ |c ⊕ ab⟩`
(`c + a * b` in `Fin 2`) — the bare-`⊗ₜ` form of `toffoliGate_op_qubitBasis_vec`, obtained by
unfolding `PureState.tmul_vec`. In the same `.op`-on-bare-`⊗ₜ` shape as
`cnotGate_op_qubitBasisVec_tmul`, so it fires directly on a distributed superposition of
computational-basis tensors (e.g. the ancilla preparation of Exercises 10.68 / 10.72). -/
theorem toffoliGate_op_qubitBasisVec_tmul (a b c : Fin 2) :
    toffoliGate.op ((qubitBasis a).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis c).vec))
      = (qubitBasis a).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis (c + a * b)).vec) := by
  have h := toffoliGate_op_qubitBasis_vec a b c
  simp only [PureState.tmul_vec] at h
  exact h

/-- **The Toffoli gate is an involution:** `C²(X) · C²(X) = 1`. The Toffoli permutes the
computational basis by the single transposition `|110⟩ ↔ |111⟩`, so applying it twice restores every
basis state (`(q₃ ⊕ q₁q₂) ⊕ q₁q₂ = q₃` in `Fin 2`); verified on the eight basis inputs via
`threeQubit_evolution_ext`. The Toffoli analogue of `cnotGate_comp_cnotGate`: it is the ingredient
that turns each Clifford commutation rule `C²(X)·P = P'·C²(X)` into the conjugation identity
`C²(X)·P·C²(X) = P'` (via `Evolution.comp_comp_self_of_comm`). -/
theorem toffoliGate_comp_toffoliGate : toffoliGate.comp toffoliGate = Evolution.id := by
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  simp only [Evolution.evolvePure_comp, toffoliGate_evolvePure_qubitBasis, Evolution.id_evolvePure]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;> rfl

end AxQM
