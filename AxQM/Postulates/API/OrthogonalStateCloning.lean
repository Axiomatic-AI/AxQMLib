/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# AxQM.Postulates.API — copying a pair of orthogonal qubit states

The construction behind Nielsen & Chuang's remark that the no-cloning theorem
"doesn't prohibit the cloning" of **orthogonal** states (N&C §12.1, p. 530, the observation that
sets up **Exercise 12.1**): the explicit two-qubit circuit that copies whichever of two fixed
orthogonal single-qubit states `|ψ⟩`, `|φ⟩` is presented on the data qubit.

The construction is the textbook one. Let `V` be the single-qubit unitary sending the computational
basis to the pair, `V|0⟩ = |ψ⟩`, `V|1⟩ = |φ⟩` (a unitary exists precisely because `{|ψ⟩, |φ⟩}` is
orthonormal — this is where orthogonality enters). Conjugating the `CNOT` "copy a classical bit"
gate by `V` yields a circuit that copies `|ψ⟩` and `|φ⟩`:

`U = (V ⊗ V) ∘ CNOT ∘ (V† ⊗ 1)`,   `U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩`,   `U(|φ⟩ ⊗ |0⟩) = |φ⟩ ⊗ |φ⟩`.

Indeed `V† ⊗ 1` rotates `|ψ⟩ ⊗ |0⟩` (resp. `|φ⟩ ⊗ |0⟩`) back to the computational input
`|0⟩ ⊗ |0⟩` (resp. `|1⟩ ⊗ |0⟩`); `CNOT` copies the classical control bit, `|c⟩ ⊗ |0⟩ ↦ |c⟩ ⊗ |c⟩`;
and `V ⊗ V` rotates the copied basis state back to `|ψ⟩ ⊗ |ψ⟩` (resp. `|φ⟩ ⊗ |φ⟩`).

## Contents

* `qubitOrthonormalBasis` — the computational basis `{|0⟩, |1⟩}` of the qubit as an
  `OrthonormalBasis`, with `qubitOrthonormalBasis_apply : qubitOrthonormalBasis i = |i⟩`.
* `qubitPair_orthonormal` — the pair `![|ψ⟩, |φ⟩]` is orthonormal, given `⟨ψ|φ⟩ = 0`.
* `qubitPairUnitary ψ φ h` (`V`) — the change-of-basis unitary with `V|0⟩ = |ψ⟩`, `V|1⟩ = |φ⟩`, and
  its defining actions `qubitPairUnitary_evolvePure_zero` / `_one`.
* `qubitCopyCircuit ψ φ h` (`U`) — the two-qubit copying circuit, with the two copying identities
  `qubitCopyCircuit_evolvePure_fst` (copies `|ψ⟩`) and `qubitCopyCircuit_evolvePure_snd`
  (copies `|φ⟩`).

## Statement of the exercise

The statement in `AxQM/NC/Ch12/Exercise12_1.lean` asserts the existence of the circuit with the
orthogonality hypothesis phrased as `fidelity = 0`, mirroring how the no-cloning theorem
(N&C Problem 12.2) phrases *non*-orthogonality as `0 < F(ψ, φ) < 1`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {ψ φ : PureState qubit}

/-- **The computational basis `{|0⟩, |1⟩}` of the qubit, as an `OrthonormalBasis`.** Repackages
`qubitModuleBasis` (which is orthonormal, `qubitModuleBasis_orthonormal`) as an `OrthonormalBasis
(Fin 2) ℂ qubit.space`. The qubit counterpart of `quditOrthonormalBasis`; its `i`-th vector is the
computational ket `|i⟩` (`qubitOrthonormalBasis_apply`). -/
def qubitOrthonormalBasis : OrthonormalBasis (Fin 2) ℂ qubit.space :=
  qubitModuleBasis.toOrthonormalBasis qubitModuleBasis_orthonormal

/-- The `i`-th vector of `qubitOrthonormalBasis` is the computational ket `|i⟩`, i.e.
`(qubitBasis i).vec`. -/
@[simp]
theorem qubitOrthonormalBasis_apply (i : Fin 2) :
    qubitOrthonormalBasis i = (qubitBasis i).vec := by
  rw [qubitOrthonormalBasis, ← qubitModuleBasis_apply]
  exact congrFun (Module.Basis.coe_toOrthonormalBasis _ _) i

/-- **A pair of orthogonal unit vectors is an orthonormal family.** For pure states `|ψ⟩`, `|φ⟩` of
the qubit with `⟨ψ|φ⟩ = 0`, the two-element family `![|ψ⟩, |φ⟩]` is orthonormal: each is a unit
vector (`PureState.normalized`) and the two are orthogonal by hypothesis. -/
theorem qubitPair_orthonormal (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    Orthonormal ℂ ![ψ.vec, φ.vec] := by
  have hψψ : inner ℂ ψ.vec ψ.vec = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ψ.normalized]; norm_num
  have hφφ : inner ℂ φ.vec φ.vec = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, φ.normalized]; norm_num
  have hφψ : inner ℂ φ.vec ψ.vec = (0 : ℂ) := inner_eq_zero_symm.mp h
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Fin.reduceEq, ↓reduceIte, hψψ, hφφ, h, hφψ]

/-- **The pair `{|ψ⟩, |φ⟩}` of orthogonal qubit states as an `OrthonormalBasis`.** Two orthonormal
vectors in the two-dimensional qubit space form an orthonormal basis; its `i`-th vector is
`![|ψ⟩, |φ⟩] i` (`qubitPairOrthonormalBasis_apply`): `|ψ⟩` for `i = 0`, `|φ⟩` for `i = 1`. -/
def qubitPairOrthonormalBasis (ψ φ : PureState qubit) (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    OrthonormalBasis (Fin 2) ℂ qubit.space :=
  (basisOfLinearIndependentOfCardEqFinrank (qubitPair_orthonormal h).linearIndependent
      (by rw [Fintype.card_fin, finrank_qubit_space])).toOrthonormalBasis
    (by rw [coe_basisOfLinearIndependentOfCardEqFinrank]; exact qubitPair_orthonormal h)

/-- The `i`-th vector of `qubitPairOrthonormalBasis ψ φ h` is `![|ψ⟩, |φ⟩] i`. -/
@[simp]
theorem qubitPairOrthonormalBasis_apply (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) (i : Fin 2) :
    qubitPairOrthonormalBasis ψ φ h i = ![ψ.vec, φ.vec] i := by
  rw [qubitPairOrthonormalBasis,
    congrFun (Module.Basis.coe_toOrthonormalBasis _ _) i,
    coe_basisOfLinearIndependentOfCardEqFinrank]

/-- **The change-of-basis unitary `V` sending the computational basis to the orthogonal pair**:
`V|0⟩ = |ψ⟩`, `V|1⟩ = |φ⟩`, for orthogonal qubit states `|ψ⟩`, `|φ⟩` (`⟨ψ|φ⟩ = 0`). It is
`Evolution.ofLinearIsometryEquiv` of the `OrthonormalBasis.equiv` carrying the computational
orthonormal basis to the pair `{|ψ⟩, |φ⟩}` (the identity index reindexing), so unitarity is
inherited from that isometry. This is the single-qubit unitary whose columns are `|ψ⟩`, `|φ⟩`. -/
def qubitPairUnitary (ψ φ : PureState qubit) (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    Evolution qubit :=
  Evolution.ofLinearIsometryEquiv
    (qubitOrthonormalBasis.equiv (qubitPairOrthonormalBasis ψ φ h) (Equiv.refl (Fin 2)))

/-- **The operator action of `V` on the computational basis:** `V|i⟩ = ![|ψ⟩, |φ⟩] i`. Follows from
the action of an `OrthonormalBasis.equiv` on a basis vector (`OrthonormalBasis.equiv_apply_basis`),
since `|i⟩ = qubitOrthonormalBasis i`. -/
theorem qubitPairUnitary_op_apply_qubitBasis (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) (i : Fin 2) :
    (qubitPairUnitary ψ φ h).op (qubitBasis i).vec = ![ψ.vec, φ.vec] i := by
  rw [qubitPairUnitary, Evolution.ofLinearIsometryEquiv_op_apply, ← qubitOrthonormalBasis_apply,
    OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, qubitPairOrthonormalBasis_apply]

/-- **`V|0⟩ = |ψ⟩`:** the change-of-basis unitary sends the computational ket `|0⟩` to `|ψ⟩`. -/
@[simp]
theorem qubitPairUnitary_evolvePure_zero (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    (qubitPairUnitary ψ φ h).evolvePure (qubitBasis 0) = ψ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, qubitPairUnitary_op_apply_qubitBasis]
  rfl

/-- **`V|1⟩ = |φ⟩`:** the change-of-basis unitary sends the computational ket `|1⟩` to `|φ⟩`. -/
@[simp]
theorem qubitPairUnitary_evolvePure_one (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    (qubitPairUnitary ψ φ h).evolvePure (qubitBasis 1) = φ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, qubitPairUnitary_op_apply_qubitBasis]
  rfl

/-- **The two-qubit circuit copying the orthogonal pair `{|ψ⟩, |φ⟩}`** (Nielsen & Chuang
Exercise 12.1): `U = (V ⊗ V) ∘ CNOT ∘ (V† ⊗ 1)`, with `V = qubitPairUnitary ψ φ h` the
change-of-basis unitary. The data qubit is the `CNOT` control and the target qubit its target;
`U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` and `U(|φ⟩ ⊗ |0⟩) = |φ⟩ ⊗ |φ⟩` (`qubitCopyCircuit_evolvePure_fst` /
`_snd`). This does not violate no-cloning: it copies only the two fixed orthogonal states, not an
arbitrary superposition. -/
def qubitCopyCircuit (ψ φ : PureState qubit) (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    Evolution (qubit ⊗ qubit) :=
  ((qubitPairUnitary ψ φ h).tmul (qubitPairUnitary ψ φ h)).comp
    (cnotGate.comp ((qubitPairUnitary ψ φ h).adjoint.tmul Evolution.id))

/-- **The copying circuit copies `|ψ⟩`:** `U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩`. Reading the circuit
`(V ⊗ V) ∘ CNOT ∘ (V† ⊗ 1)` right to left: `V† ⊗ 1` sends `|ψ⟩ ⊗ |0⟩ ↦ |0⟩ ⊗ |0⟩` (since
`V†|ψ⟩ = |0⟩`, `qubitPairUnitary_evolvePure_zero` and the uncompute cancellation
`Evolution.evolvePure_adjoint_evolvePure`), `CNOT` fixes `|0⟩ ⊗ |0⟩`
(`cnotGate_evolvePure_ketZero`), and `V ⊗ V` sends `|0⟩ ⊗ |0⟩ ↦ |ψ⟩ ⊗ |ψ⟩`. -/
theorem qubitCopyCircuit_evolvePure_fst (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    (qubitCopyCircuit ψ φ h).evolvePure (ψ.tmul (qubitBasis 0)) = ψ.tmul ψ := by
  have hV : (qubitPairUnitary ψ φ h).adjoint.evolvePure ψ = qubitBasis 0 := by
    have hcancel := Evolution.evolvePure_adjoint_evolvePure (qubitPairUnitary ψ φ h) (qubitBasis 0)
    rwa [qubitPairUnitary_evolvePure_zero h] at hcancel
  rw [qubitCopyCircuit, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.tmul_evolvePure, hV, Evolution.id_evolvePure, cnotGate_evolvePure_ketZero,
    Evolution.tmul_evolvePure, qubitPairUnitary_evolvePure_zero]

/-- **The copying circuit copies `|φ⟩`:** `U(|φ⟩ ⊗ |0⟩) = |φ⟩ ⊗ |φ⟩`. As in
`qubitCopyCircuit_evolvePure_fst`, but through the `|1⟩` branch: `V† ⊗ 1` sends
`|φ⟩ ⊗ |0⟩ ↦ |1⟩ ⊗ |0⟩` (since `V†|φ⟩ = |1⟩`), `CNOT` copies the control,
`|1⟩ ⊗ |0⟩ ↦ |1⟩ ⊗ |1⟩` (`cnotGate_evolvePure_ketOne`, `0 + 1 = 1`), and `V ⊗ V` sends
`|1⟩ ⊗ |1⟩ ↦ |φ⟩ ⊗ |φ⟩`. -/
theorem qubitCopyCircuit_evolvePure_snd (h : inner ℂ ψ.vec φ.vec = (0 : ℂ)) :
    (qubitCopyCircuit ψ φ h).evolvePure (φ.tmul (qubitBasis 0)) = φ.tmul φ := by
  have hV : (qubitPairUnitary ψ φ h).adjoint.evolvePure φ = qubitBasis 1 := by
    have hcancel := Evolution.evolvePure_adjoint_evolvePure (qubitPairUnitary ψ φ h) (qubitBasis 1)
    rwa [qubitPairUnitary_evolvePure_one h] at hcancel
  rw [qubitCopyCircuit, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.tmul_evolvePure, hV, Evolution.id_evolvePure, cnotGate_evolvePure_ketOne, zero_add,
    Evolution.tmul_evolvePure, qubitPairUnitary_evolvePure_one]

end AxQM
