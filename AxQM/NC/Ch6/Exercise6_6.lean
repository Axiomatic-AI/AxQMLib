/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ConditionalPhaseShift
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 6.6 (the dotted-box conditional phase shift)

*(N&C p. 255, Box 6.1.)*

Verify the gates in the dotted box perform conditional phase shift 2|00><00| - I up to global phase.

Box 6.1 is the explicit `N = 4` (two-qubit) run of the quantum search algorithm. The **dotted box**
in its circuit — reading the two top (query) qubits left to right — is `X ⊗ X`, then a Hadamard on
the second qubit, then a `CNOT` (control = first qubit, target = second), then a Hadamard on the
second qubit, then `X ⊗ X`. This is step 3 of the Grover iteration (the conditional phase shift, N&C
eq. 6.5) at `n = 2`, whose operator is `2|00⟩⟨00| − I` (Exercise 6.1). The exercise asks us to
verify that the circuit realises that operator up to a global phase.

## What is formalised (this file)

* `dottedBoxCircuit` — the dotted box as a closed-system `Evolution` on `qubit ⊗ qubit`, the exact
  gate list `(X ⊗ X) · (1 ⊗ H) · CNOT · (1 ⊗ H) · (X ⊗ X)`.
* `dottedBoxCircuit_eq_xx_cz_xx` — the middle `(1 ⊗ H) · CNOT · (1 ⊗ H)` collapses to the
  controlled-`Z` gate (Exercise 4.17, `CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)`, and `H² = 1`), so the whole
  box is `(X ⊗ X) · CZ · (X ⊗ X)`.
* `dottedBoxCircuit_eq_reflection` — **the box is exactly the reflection about `|00⟩`:**
  `dottedBoxCircuit = reflectionEvolution ketZeroZero`, i.e. `I − 2|00⟩⟨00|`. Since `CZ` is the
  reflection about `|11⟩` (`controlledZGate_eq_reflection`) and `X ⊗ X` maps `|11⟩ ↦ |00⟩`,
  conjugating by `X ⊗ X` moves the reflection to `|00⟩` (`reflectionEvolution_evolvePure_conj`).
* `dottedBoxCircuit_evolve_eq_conditionalPhaseShift` — **the exercise, up to global phase:** for
  every state `ρ`, the box and the conditional phase shift `2|00⟩⟨00| − I`
  (`conditionalPhaseShiftZeroZero`) induce the *same* evolution, `dottedBoxCircuit.evolve ρ =
  conditionalPhaseShiftZeroZero.evolve ρ`. The two unitaries differ only by the global phase `−1`
  (`I − 2|00⟩⟨00| = −(2|00⟩⟨00| − I)`), which is unobservable precisely because it cancels in the
  conjugation `U ρ U†` — this is the exact sense in which the global phase is "unimportant".

## Design notes

* **Fidelity.** `dottedBoxCircuit` is the literal gate sequence of the figure (not a
  pre-simplified surrogate); each gate is an `Evolution` (Postulate 5). The exercise is stated for
  the genuine `2|00⟩⟨00| − I` operator (`conditionalPhaseShiftZeroZero`, N&C's stated target), and
  "up to global phase" is made precise as equality of the channels `evolve` on *every* `ρ`, rather
  than swept into an unverified remark.
* **Supporting results.** The construction of the phase-shift gate and the `CZ`-is-a-reflection
  identity are in `AxQM/Postulates/API/ConditionalPhaseShift.lean`, imported here.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The dotted box of Box 6.1** as a closed-system `Evolution` on the two query qubits: the exact
gate list `(X ⊗ X) · (1 ⊗ H) · CNOT · (1 ⊗ H) · (X ⊗ X)`, reading the figure left to right (the
right-most factor `X ⊗ X` is applied first). Here `X ⊗ X = pauliXGate ⊗ pauliXGate`, `1 ⊗ H =
hadamardGate.onRight qubit`, and `CNOT = cnotGate`. -/
def dottedBoxCircuit : Evolution (qubit ⊗ qubit) :=
  (pauliXGate ⊗ pauliXGate).comp
    ((hadamardGate.onRight qubit).comp
      (cnotGate.comp
        ((hadamardGate.onRight qubit).comp
          (pauliXGate ⊗ pauliXGate))))

/-- **The Hadamard-conjugated `CNOT` in the box is a controlled-`Z`.** The middle three gates of the
dotted box collapse: `dottedBoxCircuit = (X ⊗ X) · CZ · (X ⊗ X)`. Proof: Exercise 4.17 gives
`CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)`, so the box's `(1 ⊗ H) · CNOT · (1 ⊗ H)` becomes
`(1 ⊗ H) · (1 ⊗ H) · CZ · (1 ⊗ H) · (1 ⊗ H) = CZ`, using `H² = 1` (`hadamardGate_comp_self`, so
`(1 ⊗ H) · (1 ⊗ H) = 1`). -/
theorem dottedBoxCircuit_eq_xx_cz_xx :
    dottedBoxCircuit
      = (pauliXGate ⊗ pauliXGate).comp
          (controlledZGate.comp (pauliXGate ⊗ pauliXGate)) := by
  have hih : (hadamardGate.onRight qubit).comp (hadamardGate.onRight qubit) = Evolution.id := by
    rw [Evolution.onRight_comp, hadamardGate_comp_self, Evolution.id_onRight]
  have hmid : (hadamardGate.onRight qubit).comp
      (cnotGate.comp (hadamardGate.onRight qubit)) = controlledZGate := by
    rw [cnotGate_eq_hadamard_conj_controlledZGate, Evolution.comp_assoc, Evolution.comp_assoc, hih,
      Evolution.comp_id, ← Evolution.comp_assoc, hih, Evolution.id_comp]
  unfold dottedBoxCircuit
  rw [← Evolution.comp_assoc cnotGate (hadamardGate.onRight qubit) (pauliXGate ⊗ pauliXGate),
    ← Evolution.comp_assoc (hadamardGate.onRight qubit)
      (cnotGate.comp (hadamardGate.onRight qubit)) (pauliXGate ⊗ pauliXGate),
    hmid]

/-- **The dotted box is the reflection about `|00⟩`:** `dottedBoxCircuit = reflectionEvolution
ketZeroZero`, i.e. `I − 2|00⟩⟨00|`. From `dottedBoxCircuit_eq_xx_cz_xx` the box is
`(X ⊗ X) · CZ · (X ⊗ X)`; `CZ` is the reflection about `|11⟩` (`controlledZGate_eq_reflection`);
`X ⊗ X` is a self-adjoint involution with `(X ⊗ X)|11⟩ = |00⟩`, so conjugating the reflection by it
(`reflectionEvolution_evolvePure_conj`) yields the reflection about `|00⟩`. -/
theorem dottedBoxCircuit_eq_reflection :
    dottedBoxCircuit = reflectionEvolution ketZeroZero := by
  -- `X ⊗ X` squares to the identity (`X² = 1` on each factor), hence equals its own adjoint.
  have hXX : pauliXGate.op.comp pauliXGate.op = 1 := by
    change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX).comp
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX) = 1
    rw [← ContinuousLinearMap.mul_def, ← map_mul, Concrete.pauliX_mul_self, map_one]
  have hxx2 : (pauliXGate ⊗ pauliXGate).comp (pauliXGate ⊗ pauliXGate) = Evolution.id := by
    apply Evolution.ext
    change (TensorProduct.mapL pauliXGate.op pauliXGate.op).comp
        (TensorProduct.mapL pauliXGate.op pauliXGate.op) = 1
    rw [← TensorProduct.mapL_comp, hXX, TensorProduct.mapL_one]
  have hxxsa : (pauliXGate ⊗ pauliXGate).adjoint = pauliXGate ⊗ pauliXGate :=
    Evolution.adjoint_eq_self_of_comp_self _ hxx2
  -- `(X ⊗ X)|11⟩ = |00⟩`.
  have hxx11 : (pauliXGate ⊗ pauliXGate).evolvePure ketOneOne = ketZeroZero := by
    simp only [ketOneOne, ketZeroZero, Evolution.tmul_evolvePure, pauliXGate_evolvePure_qubitBasis]
    rfl
  rw [dottedBoxCircuit_eq_xx_cz_xx, controlledZGate_eq_reflection, ← hxx11,
    reflectionEvolution_evolvePure_conj, hxxsa]

/-- **Nielsen & Chuang, Exercise 6.6.** The gates in the dotted box perform the conditional phase
shift `2|00⟩⟨00| − I`, up to an unimportant global phase: for every state `ρ`, the box and the
conditional phase shift induce the same evolution, `dottedBoxCircuit.evolve ρ =
conditionalPhaseShiftZeroZero.evolve ρ`. The two unitaries are `I − 2|00⟩⟨00|` and its negation
`2|00⟩⟨00| − I` (`conditionalPhaseShiftZeroZero_op_eq_neg_reflection`), i.e. their operators differ
by the unit-modulus scalar `c = −1`. That is exactly the hypothesis of the library's canonical
"up-to-global-phase ⇒ same channel" lemma `Evolution.evolve_eq_of_op_eq_phase_smul`
(`U.op = c • V.op` with `‖c‖ = 1 ⇒ ∀ ρ, U.evolve ρ = V.evolve ρ`), whose `star c · c = ‖c‖² = 1`
cancels the phase in the conjugation `U ρ U†` — which is exactly why it is physically unimportant.
The `‖c‖ = 1` hypothesis makes that unobservability explicit. -/
theorem dottedBoxCircuit_evolve_eq_conditionalPhaseShift (ρ : State (qubit ⊗ qubit)) :
    dottedBoxCircuit.evolve ρ = conditionalPhaseShiftZeroZero.evolve ρ :=
  Evolution.evolve_eq_of_op_eq_phase_smul dottedBoxCircuit conditionalPhaseShiftZeroZero
    (c := -1) (by norm_num)
    (by rw [dottedBoxCircuit_eq_reflection, conditionalPhaseShiftZeroZero_op_eq_neg_reflection];
        module) ρ

end AxQM
