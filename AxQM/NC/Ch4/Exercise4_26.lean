/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.RelativePhase

/-!
# Nielsen & Chuang, Exercise 4.26 (a Toffoli gate up to relative phases)

*(N&C p. 183.)*

Show a given circuit equals a Toffoli gate up to relative phases.

The circuit is a closed-system evolution (Postulate 5 / `Evolution`) built from the single-qubit
rotation gates `rotYGate` and the controlled gate `controlledUnitary`; the claim is that its
action on every computational-basis input agrees with the Toffoli gate's *up to a phase*. The
circuit and the quantitative computation are in `AxQM/Postulates/API/RelativePhaseToffoli.lean`.

## The formalisation

* The circuit is `relativePhaseToffoliGate` (`AxQM/Postulates/API/RelativePhaseToffoli.lean`):
  reading left to right on the target (third) qubit,
  `R_y(π/4) · CNOT₂₃ · R_y(π/4) · CNOT₁₃ · R_y(-π/4) · CNOT₂₃ · R_y(-π/4)`, with `CNOT₂₃` controlled
  by qubit 2 and `CNOT₁₃` by qubit 1, both targeting qubit 3.
* `relativePhaseToffoliGate_relativePhaseEquiv_toffoliGate` — **the exercise's claim**: on every
  computational-basis input `|c₁, c₂, t⟩`, the circuit's output and the Toffoli gate's output
  `|c₁, c₂, t ⊕ c₁·c₂⟩` are equal *in the computational basis up to a relative phase*
  (`PureState.RelativePhaseEquiv`, N&C's own §2.2.7 notion). Equivalently (and this is how it is
  proved), the circuit takes `|c₁, c₂, t⟩` to `e^{iθ(c₁,c₂,t)} |c₁, c₂, t ⊕ c₁·c₂⟩`; the phase is
  `+1` everywhere except at `|1,0,1⟩`, where it is `-1`.

## Design notes

* **Statement shape (N&C fidelity).** N&C's precise reading of "differs only by relative phases" is
  the parenthetical: input `|c₁, c₂, t⟩ ↦ e^{iθ} |c₁, c₂, t ⊕ c₁·c₂⟩`. We render this with the
  library's own basis-relative-phase predicate `PureState.RelativePhaseEquiv` (Exercise 2.65),
  comparing the circuit output to the *actual* Toffoli output `toffoliGate.evolvePure`. Because the
  Toffoli output is a single basis vector, `RelativePhaseEquiv` in the computational-basis frame
  forces the circuit output to be that same vector up to a phase — pinning both the output bit
  (`t ⊕ c₁·c₂`) and the phase-only deviation, exactly as N&C states. The phase genuinely varies with
  the input (it is `-1` only at `|1,0,1⟩`), which is what makes it a *relative*, not global, phase —
  the whole point of the exercise. The quantitative form with the explicit phase is
  `relativePhaseToffoliGate_evolvePure_vec` in `AxQM/Postulates/API/RelativePhaseToffoli.lean`.
* **Proof.** The quantitative identity `relativePhaseToffoliGate_evolvePure_vec` is stated in
  terms of the state vector `PureState.vec` and a scalar multiple; it and the supporting gate
  algebra are in `AxQM/Postulates/API/`. The theorem here, stated with `RelativePhaseEquiv`,
  `evolvePure`, `relativePhaseToffoliGate`, `toffoliGate` and `qubitBasis`, is obtained by
  applying them.
* **Not formalised: the gate-count remark.** N&C's closing sentence (such phase-only gates can be
  easier to implement) is motivational prose, not a proposition.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.26.** On every computational-basis input `|c₁, c₂, t⟩`, the
circuit `relativePhaseToffoliGate` differs from the Toffoli gate only by a relative phase: its
output is `RelativePhaseEquiv` (in the computational-basis frame `qubitThreeBasis`) to the Toffoli
output
`|c₁, c₂, t ⊕ c₁·c₂⟩`. Since the latter is a single basis vector, this says the circuit takes
`|c₁, c₂, t⟩` to `e^{iθ(c₁,c₂,t)} |c₁, c₂, t ⊕ c₁·c₂⟩` — a Toffoli gate up to (input-dependent)
phases. Proved from the explicit-phase computation `relativePhaseToffoliGate_evolvePure_vec` and the
Toffoli truth table `toffoliGate_evolvePure_qubitBasis`, with phase `e^{iθ}` realised as
`exp(i·π) = -1` at `|1,0,1⟩` and `exp(i·0) = 1` elsewhere. -/
theorem relativePhaseToffoliGate_relativePhaseEquiv_toffoliGate (c₁ c₂ t : Fin 2) :
    PureState.RelativePhaseEquiv qubitThreeBasis
      (relativePhaseToffoliGate.evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ qubitBasis t)))
      (toffoliGate.evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ qubitBasis t))) := by
  refine PureState.relativePhaseEquiv_of_vec_eq_smul _
    (if c₁ = 1 ∧ c₂ = 0 ∧ t = 1 then Real.pi else 0) ?_
  have hp : toffoliRelPhase c₁ c₂ t
      = Complex.exp (((if c₁ = 1 ∧ c₂ = 0 ∧ t = 1 then Real.pi else 0 : ℝ) : ℂ) * Complex.I) := by
    rw [toffoliRelPhase]
    split_ifs with h <;> simp [Complex.exp_pi_mul_I]
  rw [relativePhaseToffoliGate_evolvePure_vec, toffoliGate_evolvePure_qubitBasis, hp]

end AxQM
