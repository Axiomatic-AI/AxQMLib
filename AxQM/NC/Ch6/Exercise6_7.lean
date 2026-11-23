/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MarkingOracle
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Core.ProjectorPropagatorConjugation

/-!
# Nielsen & Chuang, Exercise 6.7 (circuits simulating `exp(-i|x⟩⟨x|Δt)` and `exp(-i|ψ⟩⟨ψ|Δt)`)

*(N&C p. 258.)*

Verify circuits in Figs 6.4/6.5 implement exp(-i|x><x|dt) and exp(-i|psi><psi|dt).

**The setting (N&C §6.2, "Quantum search as a quantum simulation", p. 256–258).** The quantum
search algorithm can be recovered as the simulation of a Hamiltonian: for the solution `x` and the
uniform superposition `|ψ⟩` (eq. 6.24), the system evolving under `H = |x⟩⟨x| + |ψ⟩⟨ψ|` (eq. 6.18)
rotates `|ψ⟩` into `|x⟩`. Simulating `H` by the method of §4.7 means alternately simulating the two
projector summands `H₁ = |x⟩⟨x|` and `H₂ = |ψ⟩⟨ψ|` for short time increments `Δt` — **Figure 6.4**
implements `exp(−i|x⟩⟨x|Δt)` (two oracle calls), **Figure 6.5** implements `exp(−i|ψ⟩⟨ψ|Δt)`.

## What "the circuit implements `exp(-iHΔt)`" means here

Made precise: a circuit `C` on the query
register `S` and a response qubit *implements* the query-register propagator `exp(-iHΔt)` iff, on a
response qubit supplied in `|0⟩`, `C.evolvePure (φ ⊗ |0⟩) = (exp(-iHΔt) φ) ⊗ |0⟩` for **every**
query state `φ` — i.e. `C` acts as the genuine propagator `H.propagator 1 0 Δt` on the query, and
returns the response to `|0⟩`. The target propagator is the honest `exp(-iHΔt)` of the
projector Hamiltonian `H = |x⟩⟨x|` (`PureState.projObservable`, whose closed form
`exp(-i|x⟩⟨x|Δt) = I + (e^{-iΔt}−1)|x⟩⟨x|` is proved in
`AxQM/Postulates/API/ProjectorHamiltonian.lean`).

## What is formalised

* `hamSimCircuit_evolvePure_tmul_zero` — **N&C Exercise 6.7, Figure 6.4**: for an arbitrary
  marked pure state `x` (generalising N&C's computational-basis marked item), the
  compute–phase–uncompute circuit `hamSimCircuit x Δt` (two calls to the marking oracle around the
  phase gate `P(-Δt)`) implements `exp(-i|x⟩⟨x|Δt)`: `hamSimCircuit x Δt |>.evolvePure (φ ⊗ |0⟩) =
  (exp(-i|x⟩⟨x|Δt) φ) ⊗ |0⟩` for every query state `φ`.

* `hamSimCircuitConj` — **N&C Exercise 6.7, Figure 6.5** (the circuit): the Figure 6.4 circuit for a
  reference marked state `x`, conjugated on the query register by a state-preparation unitary `W`,
  `hamSimCircuitConj W x Δt = (W ⊗ I) · hamSimCircuit x Δt · (W† ⊗ I)` — the "`H^{⊗n}`, marked-state
  circuit, `H^{⊗n}`" sandwich of Figure 6.5.

* `hamSimCircuitConj_evolvePure_tmul_zero` — **N&C Exercise 6.7, Figure 6.5**: that circuit
  implements `exp(-i|ψ⟩⟨ψ|Δt)` for the transported state `|ψ⟩ = W|x⟩` (`W.evolvePure x`): with the
  response qubit in `|0⟩`, `hamSimCircuitConj W x Δt |>.evolvePure (φ ⊗ |0⟩) =
  (exp(-i|ψ⟩⟨ψ|Δt) φ) ⊗ |0⟩` for every query state `φ`. **N&C's exercise** ("`|ψ⟩` as in (6.24)") is
  the special case where `W = H^{⊗n}` is the Walsh–Hadamard transform and `x = |0⟩`, so
  `|ψ⟩ = H^{⊗n}|0⟩` is the uniform superposition (6.24); the general `(W, x)` statement captures the
  circuit's mechanism and subsumes that case.

The circuit `hamSimCircuit` and the marking oracle `markingOracle` are built in
`AxQM/Postulates/API/MarkingOracle.lean`; the covariance law behind Figure 6.5,
`exp(-i|Wx⟩⟨Wx|Δt) = W · exp(-i|x⟩⟨x|Δt) · W†`
(`PureState.projObservable_propagator_conj`), is the shared engine in
`AxQM/Core/ProjectorPropagatorConjugation.lean`.

## Design notes

* **Fidelity.** `hamSimCircuit` is the literal compute–phase–uncompute circuit
  (`O · (I ⊗ P(-Δt)) · O`, N&C's two oracle calls); `markingOracle` is N&C's genuine single-item
  search oracle `|x⟩⟨x|⊗X + (I−|x⟩⟨x|)⊗I` (a real unitary — no vacuous oracle-spec hypothesis),
  faithful for an *arbitrary* marked pure state. The target is the genuine propagator of the
  `|x⟩⟨x|` Hamiltonian, and "implements the operation" is the honest whole-channel statement over
  *every* query state `φ` (not a single basis vector), with the response provably returned to `|0⟩`.
* **Supporting results.** The construction of the oracle (its `mapL` operator, its unitarity as a
  self-adjoint involution, and the operator-level `hamSimCircuit_op_tmul_zero`) is in
  `AxQM/Postulates/API/MarkingOracle.lean`, imported here.
* **Figure 6.5 by conjugation (fidelity).** N&C's Figure 6.5 is the Figure 6.4 circuit for a *known*
  reference state, sandwiched between two Walsh–Hadamard transforms `H^{⊗n}` on the query register,
  so that the marked reference `|0⟩` is carried to the uniform superposition `|ψ⟩ = H^{⊗n}|0⟩`
  (eq. 6.24). We formalise this as `hamSimCircuitConj W x Δt`, the Figure 6.4 circuit conjugated by
  an arbitrary state-preparation unitary `W` on the query register, and prove it implements
  `exp(-i|Wx⟩⟨Wx|Δt)`. This is faithful and strictly general: N&C's case is `W = H^{⊗n}`, `x = |0⟩`,
  giving exactly `exp(-i|ψ⟩⟨ψ|Δt)` for the (6.24) uniform state, and the proof is the conjugation
  covariance of the projector propagator (`PureState.projObservable_propagator_conj`, `Core`).
  Nothing in the argument depends on `W` being the Walsh–Hadamard transform, so we do not tie the
  statement to a concrete `H^{⊗n}` (which the library does not yet build) — the general `(W, x)`
  form captures the exercise's mechanism without weakening it.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 6.7 — Figure 6.4 implements `exp(-i|x⟩⟨x|Δt)`.** For an arbitrary
marked pure state `x` (generalising N&C's computational-basis marked item), the
compute–phase–uncompute circuit `hamSimCircuit x Δt` — the marking oracle, then the response-qubit
phase gate `P(-Δt) = diag(1, e^{-iΔt})`, then the marking oracle again (N&C's **two oracle calls**)
— implements the projector-Hamiltonian propagator `exp(-i|x⟩⟨x|Δt)`: with the response qubit
supplied in `|0⟩`, for **every** query state `φ`,
`hamSimCircuit x Δt |>.evolvePure (φ ⊗ |0⟩) = (exp(-i|x⟩⟨x|Δt) φ) ⊗ |0⟩`, where the target is the
genuine propagator `x.projObservable.propagator 1 0 Δt` of the `|x⟩⟨x|` Hamiltonian and the response
is returned to `|0⟩`. This discharges to the operator identity `hamSimCircuit_op_tmul_zero`
(`AxQM/Postulates/API/MarkingOracle.lean`) by unfolding `evolvePure`/`tmul` to the underlying
operators and vectors. -/
theorem hamSimCircuit_evolvePure_tmul_zero (x : PureState S) (Δt : ℝ) (φ : PureState S) :
    (hamSimCircuit x Δt).evolvePure (φ.tmul (qubitBasis 0))
      = ((x.projObservable.propagator 1 0 Δt).evolvePure φ).tmul (qubitBasis 0) := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [hamSimCircuit_op_tmul_zero]

/-- **The Figure 6.5 circuit** for `exp(-i|ψ⟩⟨ψ|Δt)`. The Figure 6.4 marked-state circuit
`hamSimCircuit x Δt` (for a reference marked state `x`), conjugated on the query register by a
state-preparation unitary `W`: `(W ⊗ I) · hamSimCircuit x Δt · (W† ⊗ I)`, with `W`/`W†` on the query
factor and the identity on the response qubit. This is N&C's Figure 6.5 — the "`H^{⊗n}`,
marked-state circuit, `H^{⊗n}`" sandwich — for the general state-preparation unitary `W`; N&C's
figure is the case `W = H^{⊗n}`, `x = |0⟩`, carrying the marked reference `|0⟩` to the uniform
superposition `|ψ⟩ = H^{⊗n}|0⟩` (eq. 6.24). -/
def hamSimCircuitConj (W : Evolution S) (x : PureState S) (Δt : ℝ) : Evolution (S ⊗ qubit) :=
  (W.onLeft qubit).comp ((hamSimCircuit x Δt).comp (W.adjoint.onLeft qubit))

/-- **Nielsen & Chuang, Exercise 6.7 — Figure 6.5 implements `exp(-i|ψ⟩⟨ψ|Δt)`.** For a
state-preparation unitary `W` and a reference marked state `x`, the conjugated circuit
`hamSimCircuitConj W x Δt` implements the projector-Hamiltonian propagator of the *transported*
state `|ψ⟩ = W|x⟩` (`W.evolvePure x`): with the response qubit supplied in `|0⟩`, for **every**
query state `φ`, `hamSimCircuitConj W x Δt |>.evolvePure (φ ⊗ |0⟩) = (exp(-i|ψ⟩⟨ψ|Δt) φ) ⊗ |0⟩`,
where the target is the genuine propagator `(W.evolvePure x).projObservable.propagator 1 0 Δt` and
the response is returned to `|0⟩`. **N&C's exercise** ("`|ψ⟩` as in (6.24)") is the special case
`W = H^{⊗n}`, `x = |0⟩`, so `|ψ⟩ = H^{⊗n}|0⟩` is the uniform superposition (6.24); the general
`(W, x)` statement subsumes it. The proof pushes the conjugating gates through the tensor product
(`onLeft_evolvePure`), applies Figure 6.4 on the query factor
(`hamSimCircuit_evolvePure_tmul_zero`) to `W†φ`, and closes with the conjugation covariance
`exp(-i|Wx⟩⟨Wx|Δt) = W · exp(-i|x⟩⟨x|Δt) · W†` (`PureState.projObservable_propagator_conj`). -/
theorem hamSimCircuitConj_evolvePure_tmul_zero (W : Evolution S) (x : PureState S) (Δt : ℝ)
    (φ : PureState S) :
    (hamSimCircuitConj W x Δt).evolvePure (φ.tmul (qubitBasis 0))
      = (((W.evolvePure x).projObservable.propagator 1 0 Δt).evolvePure φ).tmul (qubitBasis 0) := by
  unfold hamSimCircuitConj
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp, Evolution.onLeft_evolvePure,
    hamSimCircuit_evolvePure_tmul_zero, Evolution.onLeft_evolvePure,
    PureState.projObservable_propagator_conj, Evolution.evolvePure_comp, Evolution.evolvePure_comp]

end AxQM
