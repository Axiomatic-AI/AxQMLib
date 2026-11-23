/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.API.Purity
import AxQM.Postulates.PartialTraceTensor

/-!
# Nielsen & Chuang, Exercise 2.74 (reduced state of a pure product state)

For product state |a>|b>, show reduced density operator of A is pure.

The composite system is `A ⊗ B` and the joint state is the product pure state `ψ ⊗ φ`
(`PureState.tmul`), whose density operator is `|ψ ⊗ φ⟩⟨ψ ⊗ φ|` (`PureState.toState`). The
reduced density operator of `A` is the left marginal `ρᴬ = Tr_B(|ψ ⊗ φ⟩⟨ψ ⊗ φ|)`
(`State.reducedLeft`). The exercise asks to show `ρᴬ` is pure.

The statement uses `State.reducedLeft` (partial trace, §2.4.3) and
`State.IsPure` (`AxQM/Postulates/API/Purity.lean`), and two shared results:

* `PureState.toState_tmul` (`AxQM/Postulates/API/CompositeState.lean`) — the density operator of a
  product pure state factorizes, `|ψ ⊗ φ⟩⟨ψ ⊗ φ| = |ψ⟩⟨ψ| ⊗ |φ⟩⟨φ|`.
* `State.reducedLeft_tmul` (`AxQM/Postulates/PartialTraceTensor.lean`) — the left marginal of a
  product density state is its left factor, `Tr_B(ρ ⊗ σ) = ρ`.

Chaining them computes the reduced state *explicitly* — `ρᴬ = |ψ⟩⟨ψ|`, exactly N&C's
`ρ = trB(ρ ⊗ σ) = ρ tr(σ) = ρ` (eq. 2.184) specialized to pure factors — which is manifestly
pure, discharging the exercise. (By contrast the Bell state, Ex 2.75, has a *mixed* reduced
state: entanglement, not a product, is what makes a subsystem mixed.)

The main result is the explicit value `reducedLeft_toState_tmul`; the exercise's literal claim is
the corollary `isPure_reducedLeft_toState_tmul`. The symmetric **right-marginal** versions
`reducedRight_toState_tmul` / `isPure_reducedRight_toState_tmul` (`ρᴮ = |φ⟩⟨φ|`, via
`State.reducedRight_tmul`) are co-located here as the natural pair, reused by Exercise 2.78's
`product ⟺ ρᴮ pure` equivalence.
-/

namespace AxQM

variable {S T : QSystem}

/-- **Nielsen & Chuang, Exercise 2.74 (explicit reduced state).** The reduced density operator
of system `A` for the product pure state `|ψ⟩|φ⟩` is exactly `|ψ⟩⟨ψ|`:
`Tr_B(|ψ ⊗ φ⟩⟨ψ ⊗ φ|) = |ψ⟩⟨ψ|`. Combines `PureState.toState_tmul` (factorization of the
product density operator) with `State.reducedLeft_tmul` (the left marginal of a product state
is its left factor). -/
theorem reducedLeft_toState_tmul (ψ : PureState S) (φ : PureState T) :
    ((ψ ⊗ φ).toState).reducedLeft = ψ.toState := by
  rw [PureState.toState_tmul, State.reducedLeft_tmul]

/-- **Nielsen & Chuang, Exercise 2.74.** The reduced density operator of system `A` alone, for a
composite in the product pure state `|ψ⟩|φ⟩`, is a pure state — namely `|ψ⟩⟨ψ|`, by
`reducedLeft_toState_tmul`. -/
theorem isPure_reducedLeft_toState_tmul (ψ : PureState S) (φ : PureState T) :
    ((ψ ⊗ φ).toState).reducedLeft.IsPure :=
  ⟨ψ, reducedLeft_toState_tmul ψ φ⟩

/-- **Right-marginal mirror.** The reduced density operator of system `B` for the product pure
state `|ψ⟩|φ⟩` is exactly `|φ⟩⟨φ|`: `Tr_A(|ψ ⊗ φ⟩⟨ψ ⊗ φ|) = |φ⟩⟨φ|`. Symmetric to
`reducedLeft_toState_tmul`, via `PureState.toState_tmul` and `State.reducedRight_tmul` (the right
marginal of a product density state is its right factor). -/
theorem reducedRight_toState_tmul (ψ : PureState S) (φ : PureState T) :
    ((ψ ⊗ φ).toState).reducedRight = φ.toState := by
  rw [PureState.toState_tmul, State.reducedRight_tmul]

/-- **Right-marginal mirror.** The reduced density operator of system `B` alone, for a composite in
the product pure state `|ψ⟩|φ⟩`, is a pure state — namely `|φ⟩⟨φ|`, by `reducedRight_toState_tmul`.
The `ρᴮ` companion of `isPure_reducedLeft_toState_tmul`. -/
theorem isPure_reducedRight_toState_tmul (ψ : PureState S) (φ : PureState T) :
    ((ψ ⊗ φ).toState).reducedRight.IsPure :=
  ⟨φ, reducedRight_toState_tmul ψ φ⟩

end AxQM
