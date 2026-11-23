/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Uhlmann
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.PureState
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.PurificationUnitaryInvariance

/-!
# AxQM.Postulates.API — invariance of purifications and overlaps under unitaries

Three lemmas on purifications and overlaps. The first two strengthen Uhlmann's theorem (N&C Theorem
9.4) into its fixed-purification form (N&C Exercise 9.15); the third (`PureState.overlap_tmul`)
supports the information-gain/disturbance rigidity argument (N&C Proposition 12.18):

* `PureState.reducedLeft_evolvePure_tmul_id` — **a unitary on the ancilla preserves the left
  marginal.** Applying `I_S ⊗ U` (`Evolution.id.tmul U`, i.e. a gate acting only on the reference
  factor `T`) to a pure state `φ` of `S ⊗ T` leaves `φ.toState.reducedLeft` unchanged. Physically:
  a purification of `ρ` stays a purification of `ρ` under any unitary on its ancilla. It is the
  marginal-side companion of the freedom-in-purifications theorem (N&C Exercise 2.81,
  `PureState.exists_evolution_tmul_id_evolvePure_eq`), which says two purifications of the same `ρ`
  differ by exactly such a unitary.
* `Evolution.overlap_evolvePure` — **a unitary preserves overlaps.** The transition amplitude
  `⟨ψ|φ⟩` (`PureState.overlap`) is unchanged when both states are evolved by the same unitary:
  `(Uψ).overlap (Uφ) = ψ.overlap φ`, since `U` is an isometry.
* `PureState.overlap_tmul` — **the overlap of product states factorises.**
  `⟨ψ ⊗ φ | ψ' ⊗ φ'⟩ = ⟨ψ|ψ'⟩ ⟨φ|φ'⟩` (`TensorProduct.inner_tmul` on the underlying tensors).

The proof of `reducedLeft_evolvePure_tmul_id` goes through the purification criterion
(`PureState.reducedLeft_toState_eq_iff_isPurification`) and the fact that
`TensorProduct.IsPurification` is invariant under a unitary on the ancilla
(`TensorProduct.isPurification_mapL_id`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A unitary on the ancilla preserves the left marginal.** For a pure state `φ` of the composite
system `S ⊗ T` and a unitary `V` on the reference factor `T`, applying `I_S ⊗ V`
(`Evolution.id.tmul V`, a gate acting only on `T`) via `Evolution.evolvePure` leaves the reduced
state on `S` unchanged: `Tr_T(|(I_S ⊗ V)φ⟩⟨(I_S ⊗ V)φ|) = Tr_T(|φ⟩⟨φ|)`.

Physically, this is the statement that a purification of `ρ` remains a purification of `ρ` under any
unitary acting on its ancilla — the marginal-side companion of the freedom-in-purifications theorem
(N&C Exercise 2.81). The proof translates the goal to the predicate `TensorProduct.IsPurification`
(`PureState.reducedLeft_toState_eq_iff_isPurification`), rewrites the evolved vector as
`(I_S ⊗ V)φ.vec = mapL 1 V.op φ.vec` (`Evolution.tmul_op`, `Evolution.id_op`), and applies the
invariance `TensorProduct.isPurification_mapL_id` (using unitarity of `V.op`). -/
theorem PureState.reducedLeft_evolvePure_tmul_id (φ : PureState (S.compose T)) (V : Evolution T) :
    (((Evolution.id (S := S)).tmul V).evolvePure φ).toState.reducedLeft
      = φ.toState.reducedLeft := by
  rw [PureState.reducedLeft_toState_eq_iff_isPurification _ φ.toState.reducedLeft,
    Evolution.evolvePure_vec, Evolution.tmul_op, Evolution.id_op]
  exact (TensorProduct.isPurification_mapL_id (stdOrthonormalBasis ℂ T.space) V.unitary φ.vec).mpr
    ((PureState.reducedLeft_toState_eq_iff_isPurification φ _).mp rfl)

/-- **A unitary preserves overlaps.** Evolving both pure states by the same unitary `V` leaves the
transition amplitude `⟨ψ|φ⟩` (`PureState.overlap`) unchanged: `(Vψ).overlap (Vφ) = ψ.overlap φ`.
Immediate from `V.op` being a linear isometry (`Evolution.toIsometryEquiv`). -/
theorem Evolution.overlap_evolvePure (V : Evolution S) (ψ φ : PureState S) :
    (V.evolvePure ψ).overlap (V.evolvePure φ) = ψ.overlap φ := by
  rw [PureState.overlap_def, PureState.overlap_def, Evolution.evolvePure_vec,
    Evolution.evolvePure_vec, ← Evolution.toIsometryEquiv_apply, ← Evolution.toIsometryEquiv_apply,
    LinearIsometryEquiv.inner_map_map]

/-- **The overlap of product pure states factorises.** For `ψ, ψ' : PureState S` and
`φ, φ' : PureState T`, the transition amplitude of the product states `ψ ⊗ φ`, `ψ' ⊗ φ'` on `S ⊗ T`
splits as `⟨ψ ⊗ φ | ψ' ⊗ φ'⟩ = ⟨ψ|ψ'⟩ ⟨φ|φ'⟩`. Stated over the grounded `PureState.overlap`
generator and the composite `PureState.tmul`; the proof unfolds to the underlying tensors and
applies `TensorProduct.inner_tmul`. -/
theorem PureState.overlap_tmul (ψ ψ' : PureState S) (φ φ' : PureState T) :
    (ψ ⊗ φ).overlap (ψ' ⊗ φ') = ψ.overlap ψ' * φ.overlap φ' := by
  rw [PureState.overlap_def, PureState.overlap_def, PureState.overlap_def,
    PureState.tmul_vec, PureState.tmul_vec]
  exact TensorProduct.inner_tmul ℂ ψ.vec ψ'.vec φ.vec φ'.vec

end AxQM
