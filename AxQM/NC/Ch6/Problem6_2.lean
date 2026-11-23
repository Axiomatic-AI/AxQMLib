/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PureState
import AxQM.Postulates.API.ReflectionQubit
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.PauliYGate
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# Nielsen & Chuang, Problem 6.2 (generalized quantum searching)

*(N&C p. 274.)*

Generalized quantum searching: implement U_psi=I-2|psi><psi| from U; identify oracle among a set;
research k-state case.

## The operator `U_ψ = I − 2|ψ⟩⟨ψ|`

The reflection `U_ψ` is defined in `AxQM/Postulates/API/Reflection.lean`:

* `AxQM.reflectionEvolution ψ` — `U_ψ = I − 2|ψ⟩⟨ψ|` as a unitary `Evolution`.
* `AxQM.reflectionEvolution_hasEigenstate_neg_one` — the "`−1` phase to `|ψ⟩`":
  `U_ψ|ψ⟩ = −|ψ⟩`.
* `AxQM.reflectionEvolution_op_apply_of_orthogonal` — "leaves orthogonal states
  invariant": `⟪ψ, φ⟫ = 0 ⇒ U_ψ φ = φ`.

Together these two facts are exactly N&C's characterizing sentence ("gives `|ψ⟩` a `−1` phase,
and leaves states orthogonal to `|ψ⟩` invariant").

## Part (1) — implementing `U_ψ` (this file)

`reflectionEvolution_eq_conj_of_prep` below is the answer: if a circuit `U` prepares
`|ψ⟩ = U|0⟩⊗ⁿ` (i.e. `U.evolvePure |0⟩⊗ⁿ = |ψ⟩`), then

`U_ψ = U ∘ U_{|0⟩⊗ⁿ} ∘ U†`,

i.e. one implements the reflection about the prepared state by conjugating the reference
reflection `U_{|0⟩⊗ⁿ}` — the conditional phase shift of Exercise 6.1 (up to global sign) — with
the state-preparation circuit `U` and its inverse `U†`. The underlying general fact
(`reflectionEvolution_evolvePure_conj`, in `AxQM/Postulates/API/Reflection.lean`) is that
reflections transform *covariantly* under unitary conjugation, `U_{Uψ} = U U_ψ U†`.

## Part (2) — the three oracles are the Pauli gates (this file)

For the specific single-qubit states the three oracles are exactly the Pauli operators:

* `reflectionEvolution_qubitOne_eq_pauliZGate` — `U_|ψ₁⟩ = U_|1⟩ = Z`;
* `reflectionEvolution_qubitMinus_eq_pauliXGate` — `U_|ψ₂⟩ = U_|−⟩ = X`;
* `reflectionEvolution_qubitMinusI_eq_pauliYGate` — `U_|ψ₃⟩ = U_|−i⟩ = Y`.

Each is an equality of `Evolution`s (`I − 2|ψ⟩⟨ψ| = P`), reduced through the qubit reflection
bridge `reflectionEvolution_qubit_op_eq_toEuclideanCLM` to a `2 × 2` matrix identity
`I − 2 · outerSelf • = pauliP` proved in `AxQM/Concrete/PauliEigenvectors.lean`.

## Part (2) — the one-shot algorithm (superdense coding, this file)

The discrimination is the superdense-coding protocol run in reverse:

* `searchReflectionOracle : Fin 3 → Evolution qubit` — the three oracles `U_|ψ₁⟩, U_|ψ₂⟩, U_|ψ₃⟩`.
* `oracleBellState i` — apply oracle `i` to Alice's (left) half of the Bell pair `|Φ⁺⟩`.
* `bellOutcome : Fin 3 → Fin 2 × Fin 2` (`= β₁₀, β₀₁, β₁₁`) and `bellOutcome_injective`.
* `oracleBellState_toState` — `(P ⊗ I)|Φ⁺⟩` is (up to a global phase, invisible to the state) the
  Bell state `β_{bellOutcome i}`; so the three post-oracle states are *distinct* Bell states —
  the pairwise orthogonality that makes the discrimination work.
* `bellMeasurement_bornProb_bellState` (a general fact, in
  `AxQM/Postulates/API/Teleportation.lean`) — measuring a Bell state in the Bell basis is
  deterministic.
* `oracleBellState_bornProb` — the main result: `Pr[outcome β_{bellOutcome i} ∣ oracle j] = δᵢⱼ`, so
  one oracle application followed by one Bell measurement returns three distinct deterministic
  outcomes, identifying the oracle (`oracleBellState_identified`: a nonzero outcome pins it down).

Since the oracle is one of `{X, Y, Z}` (Paulis), `X ⊗ I`, `Y ⊗ I`, `Z ⊗ I` send `|Φ⁺⟩` to three
pairwise-orthogonal Bell states, so a single Bell measurement identifies the oracle in one call.

## Supporting results

* `reflectionEvolution_evolvePure_conj` (`AxQM/Postulates/API/Reflection.lean`) — covariance
  `U_{Uψ} = U U_ψ U†`, the engine of part (1);
* `reflectionEvolution_qubit_op_eq_toEuclideanCLM` (`AxQM/Postulates/API/ReflectionQubit.lean`) and
  `one_sub_two_smul_outerSelf_{ket_one,xMinus,yMinus}` (`AxQM/Concrete/PauliEigenvectors.lean`) —
  the qubit reflection bridge and the matrix identities for the three Paulis;
* `bellMeasurement_bornProb_bellState` (`AxQM/Postulates/API/Teleportation.lean`) — a Bell-basis
  measurement reads out which Bell state it is (deterministic outcome);
* `PureState.toState_eq_of_vec_eq_smul` (`AxQM/Postulates/API/PureState.lean`) — a global phase is
  invisible to the density operator (used for the `Y`-case `−i` phase).

The declarations of this file are those named in parts (1), (2) and the one-shot algorithm above:
`reflectionEvolution_eq_conj_of_prep`; the three Pauli identities;
`searchReflectionOracle`, `oracleBellState`, `bellOutcome`, `bellOutcome_injective`,
`oracleBellState_toState`, `oracleBellState_bornProb` and `oracleBellState_identified`.

## Part (3)

* **Part (3)** is an open research question (the `k`-state query complexity of oracle
  identification); it states no definite proposition the library can express and is recorded here
  as out of scope, not formalized.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **N&C Problem 6.2(1).** How to implement `U_ψ = I − 2|ψ⟩⟨ψ|` from a state-preparation
circuit. If a unitary `U` prepares `|ψ⟩` from the reference state `|φ⟩` (`U|φ⟩ = |ψ⟩`; take
`|φ⟩ = |0⟩⊗ⁿ`), then the reflection about `|ψ⟩` is the reference reflection about `|φ⟩` conjugated
by `U`:

`U_ψ = U ∘ U_φ ∘ U†`.

Here `U_φ = reflectionEvolution |0⟩⊗ⁿ` is the conditional phase shift `I − 2|0⟩⊗ⁿ⟨0|⊗ⁿ` (the
Grover phase shift of Exercise 6.1 negated). Since `U ∘ U_φ ∘ U†` acts on an input rightmost-first,
the circuit for `U_ψ`, in order of application, is: run `U†`, apply the reference phase shift,
then run `U` — i.e. *un-prepare* `|ψ⟩ ↦ |φ⟩` with `U†`, reflect about the reference `|φ⟩`, then
*re-prepare* with `U`. Proved by covariance of reflections under unitary conjugation
(`reflectionEvolution_evolvePure_conj`). -/
theorem reflectionEvolution_eq_conj_of_prep {U : Evolution S} {φ ψ : PureState S}
    (h : U.evolvePure φ = ψ) :
    reflectionEvolution ψ = U.comp ((reflectionEvolution φ).comp U.adjoint) := by
  subst h
  exact reflectionEvolution_evolvePure_conj U φ

/-! ## Part (2) — the three single-qubit oracles are the Pauli gates

For `|ψ₁⟩ = |1⟩`, `|ψ₂⟩ = |−⟩ = (|0⟩ − |1⟩)/√2`, `|ψ₃⟩ = |−i⟩ = (|0⟩ − i|1⟩)/√2`, the reflection
oracles `U_|ψᵢ⟩ = I − 2|ψᵢ⟩⟨ψᵢ|` are the Pauli gates `Z`, `X`, `Y`: each `|ψᵢ⟩` is the
`−1`-eigenstate of its Pauli, so `I − 2|ψᵢ⟩⟨ψᵢ|` (which flips `|ψᵢ⟩` and fixes its orthogonal
complement) coincides with the Pauli itself. This is why superdense coding solves the problem — the
oracle is one of the three Paulis. -/

/-- **N&C Problem 6.2(2), oracle `U_|ψ₁⟩`.** For `|ψ₁⟩ = |1⟩` the reflection oracle is the
Pauli-`Z` gate: `U_|1⟩ = I − 2|1⟩⟨1| = Z`. -/
theorem reflectionEvolution_qubitOne_eq_pauliZGate :
    reflectionEvolution (qubitBasis 1) = pauliZGate := by
  apply Evolution.ext
  rw [reflectionEvolution_qubit_op_eq_toEuclideanCLM, pauliZGate_op]
  congr 1
  exact Concrete.one_sub_two_smul_outerSelf_ket_one

/-- **N&C Problem 6.2(2), oracle `U_|ψ₂⟩`.** For `|ψ₂⟩ = |−⟩ = (|0⟩ − |1⟩)/√2` the reflection
oracle is the Pauli-`X` gate: `U_|−⟩ = I − 2|−⟩⟨−| = X`. -/
theorem reflectionEvolution_qubitMinus_eq_pauliXGate :
    reflectionEvolution qubitMinus = pauliXGate := by
  apply Evolution.ext
  rw [reflectionEvolution_qubit_op_eq_toEuclideanCLM, pauliXGate_op]
  congr 1
  exact Concrete.one_sub_two_smul_outerSelf_xMinus

/-- **N&C Problem 6.2(2), oracle `U_|ψ₃⟩`.** For `|ψ₃⟩ = |−i⟩ = (|0⟩ − i|1⟩)/√2` the reflection
oracle is the Pauli-`Y` gate: `U_|−i⟩ = I − 2|−i⟩⟨−i| = Y`. -/
theorem reflectionEvolution_qubitMinusI_eq_pauliYGate :
    reflectionEvolution qubitMinusI = pauliYGate := by
  apply Evolution.ext
  rw [reflectionEvolution_qubit_op_eq_toEuclideanCLM, pauliYGate_op]
  congr 1
  exact Concrete.one_sub_two_smul_outerSelf_yMinus

/-! ## Part (2) — one-shot identification via a Bell measurement (superdense coding)

The three oracles are the Paulis `Z, X, Y` (above).  To identify the unknown oracle `O` with a
single application, prepare a Bell pair `|Φ⁺⟩`, apply `O` to its **first** qubit, and measure both
qubits in the Bell basis.  Because `Z ⊗ I`, `X ⊗ I`, `Y ⊗ I` send `|Φ⁺⟩` to the three *distinct*
Bell states `|β₁₀⟩`, `|β₀₁⟩`, `|β₁₁⟩` (the last up to a global `−i` phase), the Bell measurement
returns a different **deterministic** outcome for each oracle — so one oracle call identifies it
with certainty.  This is the superdense-coding protocol run in reverse (N&C §2.3). -/

/-- The three oracles of Problem 6.2(2): the reflection oracles `U_|ψᵢ⟩ = I − 2|ψᵢ⟩⟨ψᵢ|` for
`|ψ₁⟩ = |1⟩`, `|ψ₂⟩ = |−⟩`, `|ψ₃⟩ = |−i⟩`.  By part (2a) these are the Pauli gates `Z`, `X`, `Y`. -/
def searchReflectionOracle : Fin 3 → Evolution qubit
  | 0 => reflectionEvolution (qubitBasis 1)
  | 1 => reflectionEvolution qubitMinus
  | 2 => reflectionEvolution qubitMinusI

/-- The two-qubit state after applying oracle `i` to Alice's (left) half of the shared Bell pair
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
def oracleBellState (i : Fin 3) : PureState (qubit ⊗ qubit) :=
  ((searchReflectionOracle i).onLeft qubit).evolvePure bellPhiPlus

/-- The Bell-basis outcome each oracle deterministically produces: `Z ↦ β₁₀`, `X ↦ β₀₁`,
`Y ↦ β₁₁`.  These three outcomes are distinct (`bellOutcome_injective`), which is why one Bell
measurement identifies the oracle. -/
def bellOutcome : Fin 3 → Fin 2 × Fin 2
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)

/-- The three oracles map `|Φ⁺⟩` to **distinct** Bell outcomes, so those outcomes tell the oracles
apart. -/
theorem bellOutcome_injective : Function.Injective bellOutcome := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [bellOutcome]

/-- Each oracle sends `|Φ⁺⟩` to a Bell basis state, up to a global phase — hence to the *same
density operator* as that Bell state: `Z⊗I |Φ⁺⟩ = |β₁₀⟩`, `X⊗I |Φ⁺⟩ = |β₀₁⟩`,
`Y⊗I |Φ⁺⟩ = −i|β₁₁⟩`.  (The `−i` in the `Y` case is a global phase, invisible to the state, so all
three are exact Bell measurement outcomes.) -/
theorem oracleBellState_toState (i : Fin 3) :
    (oracleBellState i).toState
      = (bellState (bellOutcome i).1 (bellOutcome i).2).toState := by
  fin_cases i
  · change (oracleBellState 0).toState = (bellState 1 0).toState
    have hv : (oracleBellState 0).vec = bellBasisVec 1 0 := by
      change (((searchReflectionOracle 0).onLeft qubit).evolvePure bellPhiPlus).vec = _
      rw [show searchReflectionOracle 0 = pauliZGate
          from reflectionEvolution_qubitOne_eq_pauliZGate,
        Evolution.evolvePure_vec, bellPhiPlus_vec, bellVec, bellBasisVec]
      erw [map_smul, map_add]
      simp only [Evolution.onLeft_op_tmul, pauliZGate_op_apply_qubitBasis,
        Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, Fin.reduceAdd]
      rw [← TensorProduct.smul_tmul']
      -- Re-elaborate the tensor atoms as composite `(·.tmul ·).vec` (the raw-head atoms from
      -- `← smul_tmul'` and the composite-head atoms from `bellBasisVec` are defeq but `module`'s
      -- atom-matching distinguishes their instance arguments); then `module` closes the identity.
      change (Real.sqrt 2 : ℂ)⁻¹ •
            (((qubitBasis 0).tmul (qubitBasis 0)).vec +
              (-1 : ℂ) • ((qubitBasis 1).tmul (qubitBasis 1)).vec) =
          (Real.sqrt 2 : ℂ)⁻¹ •
            (((qubitBasis 0).tmul (qubitBasis 0)).vec +
              (-1 : ℂ) • ((qubitBasis 1).tmul (qubitBasis 1)).vec)
      module
    refine State.ext ?_; simp only [PureState.toState_op, hv, bellState_vec]
  · change (oracleBellState 1).toState = (bellState 0 1).toState
    have hv : (oracleBellState 1).vec = bellBasisVec 0 1 := by
      change (((searchReflectionOracle 1).onLeft qubit).evolvePure bellPhiPlus).vec = _
      rw [show searchReflectionOracle 1 = pauliXGate
          from reflectionEvolution_qubitMinus_eq_pauliXGate,
        Evolution.evolvePure_vec, bellPhiPlus_vec, bellVec, bellBasisVec]
      erw [map_smul, map_add]
      simp only [Evolution.onLeft_op_tmul, pauliXGate_op_apply_qubitBasis,
        Fin.reduceAdd, Fin.val_zero, pow_zero, one_smul]
      -- Re-elaborate the tensor atoms as composite `(·.tmul ·).vec` (the raw-head atoms from
      -- `onLeft_op_tmul` and the composite-head atoms from `bellBasisVec` are defeq but `module`'s
      -- atom-matching distinguishes their instance arguments); then `module` closes the identity.
      change (Real.sqrt 2 : ℂ)⁻¹ •
            (((qubitBasis 1).tmul (qubitBasis 0)).vec +
              ((qubitBasis 0).tmul (qubitBasis 1)).vec) =
          (Real.sqrt 2 : ℂ)⁻¹ •
            (((qubitBasis 0).tmul (qubitBasis 1)).vec +
              ((qubitBasis 1).tmul (qubitBasis 0)).vec)
      module
    refine State.ext ?_; simp only [PureState.toState_op, hv, bellState_vec]
  · change (oracleBellState 2).toState = (bellState 1 1).toState
    have hv : (oracleBellState 2).vec = (-Complex.I) • bellBasisVec 1 1 := by
      change (((searchReflectionOracle 2).onLeft qubit).evolvePure bellPhiPlus).vec = _
      rw [show searchReflectionOracle 2 = pauliYGate
          from reflectionEvolution_qubitMinusI_eq_pauliYGate,
        Evolution.evolvePure_vec, bellPhiPlus_vec, bellVec, bellBasisVec]
      erw [map_smul, map_add]
      simp only [Evolution.onLeft_op_tmul, pauliYGate_op_apply_qubitBasis, PureState.tmul_vec,
        Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, mul_neg, Fin.reduceAdd]
      -- Pull the `±i` phases out of the tensor factors (via `rw`, not `simp`).
      rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
      -- Re-elaborate the tensor atoms as composite `(·.tmul ·).vec` (the raw-head atoms from
      -- `← smul_tmul'` and the composite-head atoms from `bellBasisVec` are defeq but `module`'s
      -- atom-matching distinguishes their instance arguments); then `module` closes the ℂ-linear
      -- identity over the two atoms.
      change (Real.sqrt 2 : ℂ)⁻¹ •
            (Complex.I • ((qubitBasis 1).tmul (qubitBasis 0)).vec +
              -Complex.I • ((qubitBasis 0).tmul (qubitBasis 1)).vec) =
          -Complex.I • (Real.sqrt 2 : ℂ)⁻¹ •
            (((qubitBasis 0).tmul (qubitBasis 1)).vec +
              -1 • ((qubitBasis 1).tmul (qubitBasis 0)).vec)
      module
    -- The `−i` global phase is invisible to the density operator.
    exact PureState.toState_eq_of_vec_eq_smul (c := -Complex.I) (by simp)
      (by rw [hv, bellState_vec])

/-- **N&C Problem 6.2(2) — the discrimination.**  Preparing `|Φ⁺⟩`, applying the unknown oracle
`O = searchReflectionOracle j` to its first qubit and measuring in the Bell basis returns outcome
`bellOutcome i` with probability `1` when `i = j` and `0` otherwise:

`Pr[outcome β_{bellOutcome i} ∣ (O_j ⊗ I)|Φ⁺⟩] = δᵢⱼ`.

Since the three oracles yield three distinct *deterministic* outcomes, one oracle application
followed by one Bell measurement identifies the oracle — the superdense-coding solution. -/
theorem oracleBellState_bornProb (i j : Fin 3) :
    bellMeasurement.bornProb ((oracleBellState j).toState) (bellOutcome i)
      = if i = j then 1 else 0 := by
  rw [oracleBellState_toState j, bellMeasurement_bornProb_bellState, Prod.mk.eta]
  simp only [bellOutcome_injective.eq_iff]

/-- **One oracle call identifies the oracle with certainty.**  If the Bell measurement on the
post-oracle state `(O_j ⊗ I)|Φ⁺⟩` yields outcome `bellOutcome i` with nonzero probability, then the
unknown oracle must be `O_j` with `j = i`: the outcome pins down the oracle. -/
theorem oracleBellState_identified {i j : Fin 3}
    (h : bellMeasurement.bornProb ((oracleBellState j).toState) (bellOutcome i) ≠ 0) : i = j := by
  by_contra hne
  apply h
  rw [oracleBellState_bornProb, ite_eq_right hne]

end AxQM
