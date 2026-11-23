/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution

/-!
# Nielsen & Chuang, Exercise 8.1 (Unitary evolution as a quantum operation)

*(N&C p. 357.)*

Show unitary evolution |ψ⟩→U|ψ⟩ is equivalently ρ→UρU† for ρ=|ψ⟩⟨ψ|.

A state is described either by a pure-state vector or by a density operator, and the two
descriptions are related by `PureState.toState`, `ψ ↦ |ψ⟩⟨ψ|`. A closed-system
**evolution** (Postulate 5, `Evolution`) acts on each: on pure states by
application, `Evolution.evolvePure U ψ = U|ψ⟩` (Schrödinger picture), and on density operators by
conjugation, `Evolution.evolve U ρ = U ρ U†` (the quantum operation `E(ρ) = U ρ U†`). The exercise
asks that these two descriptions of the *same* dynamics agree on a pure state: forming the density
operator of the evolved vector gives the conjugated density operator.

## The formalisation

Both statements are in terms of `evolvePure`, `toState`, `evolve` and `IsPure`. The
`evolvePure ↔ evolve` bridge (the fact that a unitary transports a pure state the same way in both
pictures) is also used elsewhere, e.g. in the CSS-code equivalence of Exercise 10.27. The two
declarations are in `AxQM/Postulates/API/Evolution.lean`.

* `AxQM.toState_evolvePure`
  (in `AxQM/Postulates/API/Evolution.lean`) — **the exercise:**
  `(U.evolvePure ψ).toState = U.evolve ψ.toState`, i.e. `|U ψ⟩⟨U ψ| = U |ψ⟩⟨ψ| U†`. Taking the
  density operator of the unitarily-evolved pure state `U|ψ⟩` yields the same state as evolving the
  pure state's density operator `ρ = |ψ⟩⟨ψ|` by the quantum operation `E(ρ) = U ρ U†`. This is the
  equivalence N&C asks for — a genuine identity of `State`s (density operators) for every pure state
  `ψ` and every evolution `U`, not a basis-dependent or up-to-phase surrogate.
* `AxQM.isPure_evolve`
  (in `AxQM/Postulates/API/Evolution.lean`) — **the physical upshot:** unitary evolution
  preserves purity, `ρ.IsPure → (U.evolve ρ).IsPure`. So if `ρ = |ψ⟩⟨ψ|` then
  `U.evolve ρ = |U ψ⟩⟨U ψ|` is again a rank-one projector: the quantum operation `E(ρ) = U ρ U†`
  maps pure states to pure states, recording why unitary dynamics is the paradigmatic reversible
  quantum operation.

The proof reduces to the underlying operators (`State.ext`) and rewrites the evolved density
operator `U (|ψ⟩⟨ψ|) U†` with the rank-one composition lemmas `InnerProductSpace.rankOne_comp`
(`|x⟩⟨y| ∘ f = |x⟩⟨f† y|`) and `InnerProductSpace.comp_rankOne` (`f ∘ |x⟩⟨y| = |f x⟩⟨y|`), together
with `adjoint_adjoint` (`U†† = U`), collapsing it to `|U ψ⟩⟨U ψ|`. The purity corollary is
immediate.
-/
