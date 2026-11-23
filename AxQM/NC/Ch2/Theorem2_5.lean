/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Ensemble

/-!
# Nielsen & Chuang, Theorem 2.5 (Characterization of density operators)

Characterization of density operators: rho is a density operator iff trace one and positive.

The theorem characterizes exactly which operators are quantum states.

A `State S` is by definition a positive operator of trace one (Postulate 1 in the density-operator
formulation), so the conditions on a density operator are already part of the notion of state.
Theorem 2.5 is therefore the statement that the map from ensembles to states,
`Ensemble.toState : Ensemble S → State S`, sending an ensemble `{pᵢ, |ψᵢ⟩}` to its density operator
`∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, is **surjective**:

* that `Ensemble.toState` lands in `State S` at all is the **forward** direction — every ensemble's
  density operator satisfies the trace and positivity conditions;
* its **surjectivity** is the **converse** — every trace-one positive operator arises from an
  ensemble (its eigenensemble, via the spectral decomposition, N&C eq. (2.157)).

The `Ensemble` structure, the density-operator map `Ensemble.toState`, the eigenensemble
construction `Ensemble.ofState`, and the round-trip `Ensemble.ofState_toState` are in
`AxQM/Postulates/API/Ensemble.lean`. The operator-level biconditional "density operator iff trace
one and positive" is `AxQM.isDensityOp_iff_exists_ensemble`, also in that file.
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen–Chuang Theorem 2.5 (characterization of density operators).** The map sending an
ensemble of pure states `{pᵢ, |ψᵢ⟩}` to its density operator `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` is surjective onto
the states: every quantum state (a positive operator of trace one) arises from an ensemble.

The codomain being `State S` encodes the *forward* direction of the biconditional (an ensemble's
density operator is positive with trace one); surjectivity is the *converse* (every positive
trace-one operator is realized by an ensemble — its eigenensemble, `Ensemble.ofState`). Together
they are Theorem 2.5. -/
theorem Ensemble.toState_surjective :
    Function.Surjective (Ensemble.toState (S := S)) :=
  fun ρ => ⟨Ensemble.ofState ρ, Ensemble.ofState_toState ρ⟩

end AxQM
