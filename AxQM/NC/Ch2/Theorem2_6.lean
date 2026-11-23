/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.UnitaryFreedom

/-!
# Nielsen & Chuang, Theorem 2.6 (Unitary freedom in the ensemble for density matrices)

Unitary freedom in the ensemble: two sets generate the same density matrix iff unitarily related.

The theorem characterizes exactly the freedom in the ensembles `{pᵢ, |ψᵢ⟩}` that give rise to a
given density operator `ρ`.

The statement is the ensemble form (2.167): two ensembles `e`, `f` **of the same size** (the padded
form) give the same quantum state, `e.toState = f.toState`, if and only if they are *unitarily
related* (`Ensemble.UnitarilyRelated`), i.e. their subnormalized vectors `√pᵢ|ψᵢ⟩` are related by a
unitary coefficient matrix. Two ensembles of unequal size may still give the same state (by
padding); the theorem is stated for the equal-size case, exactly as Nielsen & Chuang state the
result after padding.

The subnormalized vectors `Ensemble.tildeVec`, the bridge
`Ensemble.toState_op_eq_sum_rankOne_tildeVec` (`ρ = ∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|`), the relation
`Ensemble.UnitarilyRelated`, and the operator-form biconditional
`Ensemble.toState_op_eq_iff_unitarilyRelated` are in `AxQM/Postulates/API/UnitaryFreedom.lean`. The
vector-family biconditional `InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup` is
in `ToMathlib/Analysis/InnerProductSpace/RankOneSum.lean`.
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen–Chuang Theorem 2.6 (unitary freedom in the ensemble).** Two ensembles `e`, `f` of a
quantum system `S`, of the same size (`e.card = f.card` — the padded form, obtained by padding the
smaller ensemble with probability-zero entries), give rise to the same quantum state
`e.toState = f.toState` **if and only if** they are unitarily related (`Ensemble.UnitarilyRelated`):
their subnormalized state vectors `√pᵢ|ψᵢ⟩` are related by a unitary coefficient matrix,
`√pᵢ|ψᵢ⟩ = ∑ⱼ uᵢⱼ √qⱼ|φⱼ⟩` (N&C eq. (2.167)).

Equality of states is
`Ensemble.toState_op_eq_iff_unitarilyRelated` under `State`-extensionality (`State.ext_iff`), which
in turn is the vector-family biconditional applied to the subnormalized vectors. -/
theorem Ensemble.toState_eq_iff_unitarilyRelated {e f : Ensemble S} (hcard : e.card = f.card) :
    e.toState = f.toState ↔ e.UnitarilyRelated f := by
  rw [State.ext_iff, Ensemble.toState_op_eq_iff_unitarilyRelated hcard]

end AxQM
