/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledZ
import AxQM.Postulates.API.Reflection
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.ControlBranchExt
import AxQM.Postulates.API.BellBasis

/-!
# AxQM.Postulates.API — the two-qubit conditional phase shift `2|00⟩⟨00| − I`

Nielsen & Chuang's **conditional phase shift** on two qubits
(the `n = 2` case of the Grover phase shift, N&C eq. 6.5 / Exercise 6.1): the gate
`2|00⟩⟨00| − I` that fixes `|00⟩` and negates every other computational-basis state, together with
the reusable facts relating it to the state reflection `reflectionEvolution` (`Reflection.lean`) and
identifying the controlled-`Z` gate as a reflection.

* `ketZeroZero` / `ketOneOne` — the two-qubit computational-basis product states `|00⟩` / `|11⟩`.
* `conditionalPhaseShiftZeroZero` — the gate `2|00⟩⟨00| − I` as a unitary `Evolution` on
  `qubit ⊗ qubit`. It is a self-adjoint involution (`(2P − 1)² = 1` for the rank-one projector
  `P = |00⟩⟨00|`), hence a legitimate closed-system evolution; this is the operator N&C's Box 6.1
  names as the conditional phase shift.
* `conditionalPhaseShiftZeroZero_op` — its underlying operator `2 • |00⟩⟨00| − 1`.
* `conditionalPhaseShiftZeroZero_op_eq_neg_reflection` — `2|00⟩⟨00| − I = −(I − 2|00⟩⟨00|)`, i.e.
  the phase shift is the negation of `reflectionEvolution ketZeroZero`. This is the
  **global-phase factor `−1`** by which Exercise 6.6's dotted-box circuit differs from it.
* `controlledZGate_eq_reflection` — the controlled-`Z` gate is the reflection about `|11⟩`:
  `controlledZGate = reflectionEvolution ketOneOne` (`CZ = I − 2|11⟩⟨11|`, i.e. `diag(1,1,1,−1)`).
  The reusable identity that lets Exercise 6.6 rewrite the middle of its circuit as a reflection.
* `Evolution.adjoint_eq_self_of_comp_self` — the general fact **"a unitary involution is
  self-adjoint"** (`U · U = 1 ⇒ U† = U`), extracted from the `X ⊗ X` step of Exercise 6.6 as
  reusable `Evolution` API (it uses only `Evolution.adjoint_comp_self'` and the gate-monoid laws).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **A unitary involution is self-adjoint:** if `U · U = 1` then `U† = U`. Since `U` is a unitary
`Evolution`, `U†` is its two-sided inverse (`Evolution.adjoint_comp_self'`), so `U · U = 1` makes
`U` its own inverse and hence equal to `U†`. A general `Evolution` fact (used here for `X ⊗ X`, a
Pauli involution). -/
theorem Evolution.adjoint_eq_self_of_comp_self {S : QSystem} (U : Evolution S)
    (h : U.comp U = Evolution.id) : U.adjoint = U :=
  calc U.adjoint
      = U.adjoint.comp Evolution.id := (Evolution.comp_id _).symm
    _ = U.adjoint.comp (U.comp U) := by rw [h]
    _ = (U.adjoint.comp U).comp U := (Evolution.comp_assoc _ _ _).symm
    _ = Evolution.id.comp U := by rw [Evolution.adjoint_comp_self']
    _ = U := Evolution.id_comp _

/-- The two-qubit computational-basis product state `|00⟩ = |0⟩ ⊗ |0⟩`. -/
def ketZeroZero : PureState (qubit ⊗ qubit) := qubitBasis 0 ⊗ qubitBasis 0

/-- The two-qubit computational-basis product state `|11⟩ = |1⟩ ⊗ |1⟩`. -/
def ketOneOne : PureState (qubit ⊗ qubit) := qubitBasis 1 ⊗ qubitBasis 1

/-- **The conditional phase shift** `2|00⟩⟨00| − I` on two qubits (Nielsen & Chuang, Box 6.1 /
Exercise 6.1 at `n = 2`): the closed-system `Evolution` that fixes `|00⟩` and phase-flips every
other computational-basis state. Its operator `2 • |00⟩⟨00| − 1` is a **self-adjoint involution** —
`(2P − 1)² = 1` since the rank-one projector `P = |00⟩⟨00|` is idempotent (`⟪00, 00⟫ = 1`) and
self-adjoint — so unitarity (the `Evolution` proof obligation) is discharged. -/
def conditionalPhaseShiftZeroZero : Evolution (qubit ⊗ qubit) where
  op := (2 : ℂ) • rankOne ℂ ketZeroZero.vec ketZeroZero.vec - 1
  unitary := by
    have hself : inner ℂ ketZeroZero.vec ketZeroZero.vec = (1 : ℂ) :=
      inner_self_eq_one_of_norm_eq_one ketZeroZero.normalized
    set P : (qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space :=
      rankOne ℂ ketZeroZero.vec ketZeroZero.vec with hPdef
    have hPP : P * P = P := by
      rw [hPdef, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hself, one_smul]
    have hPsa : star P = P := by
      rw [hPdef, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]
    have hRsa : star ((2 : ℂ) • P - 1) = (2 : ℂ) • P - 1 := by
      rw [star_sub, star_smul, hPsa, star_one, star_ofNat]
    have hRR : ((2 : ℂ) • P - 1) * ((2 : ℂ) • P - 1) = 1 := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_smul_comm, hPP]
      module
    rw [Unitary.mem_iff, hRsa]
    exact ⟨hRR, hRR⟩

/-- The underlying operator of `conditionalPhaseShiftZeroZero` is `2 • |00⟩⟨00| − 1`. -/
@[simp]
theorem conditionalPhaseShiftZeroZero_op :
    conditionalPhaseShiftZeroZero.op
      = (2 : ℂ) • rankOne ℂ ketZeroZero.vec ketZeroZero.vec - 1 := rfl

/-- **The conditional phase shift is the negation of the reflection about `|00⟩`:**
`2|00⟩⟨00| − I = −(I − 2|00⟩⟨00|)`. The two operators differ by the scalar `−1` — the
"unimportant global phase factor" of Nielsen & Chuang, Exercise 6.6. -/
theorem conditionalPhaseShiftZeroZero_op_eq_neg_reflection :
    conditionalPhaseShiftZeroZero.op = -(reflectionEvolution ketZeroZero).op := by
  rw [conditionalPhaseShiftZeroZero_op, reflectionEvolution_op]
  module

/-- **The controlled-`Z` gate is the reflection about `|11⟩`:**
`controlledZGate = reflectionEvolution ketOneOne`, i.e. `CZ = I − 2|11⟩⟨11| = diag(1, 1, 1, −1)`.
It fixes `|00⟩, |01⟩, |10⟩` and negates `|11⟩` — the phase flip on the doubly-excited state.
Verified on the four computational-basis inputs (`twoQubit_evolution_ext`): `CZ` acts as the
identity when the control `|q₁⟩ = |0⟩` and as `Z` on the target when `|q₁⟩ = |1⟩`, matching the
reflection, which negates exactly the `|11⟩` component. -/
theorem controlledZGate_eq_reflection :
    controlledZGate = reflectionEvolution ketOneOne := by
  -- The single algebraic identity behind the `|11⟩` case, isolated so it is closed once by
  -- `module`; `exact`'s definitional unification then bridges the raw-tensor vs composite head
  -- forms the two simp passes leave the goal in.
  have hneg : ∀ (T : (qubit ⊗ qubit).space), (-1 : ℂ) • T = T - (2 : ℂ) • T := fun T => by module
  have hzero : ∀ (T U : (qubit ⊗ qubit).space), T = T - (0 : ℂ) • U := fun T U => by module
  refine twoQubit_evolution_ext (fun q1 q2 => ?_)
  apply PureState.ext
  unfold controlledZGate
  rw [Evolution.evolvePure_vec (reflectionEvolution ketOneOne), reflectionEvolution_op_apply]
  simp only [ketOneOne, qubitBasis_tmul_inner]
  simp only [PureState.tmul_vec]
  fin_cases q1 <;> fin_cases q2 <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne] <;>
    simp only [Evolution.evolvePure_vec, PureState.tmul_vec, pauliZGate_op_apply_qubitBasis,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, TensorProduct.tmul_smul,
      Fin.reduceEq, ↓reduceIte, mul_one, mul_zero]
  all_goals first
    | exact hneg _
    | exact hzero _ _

end AxQM
