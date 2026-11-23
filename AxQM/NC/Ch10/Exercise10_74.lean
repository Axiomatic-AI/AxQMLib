/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_60
import AxQM.Postulates.API.StabilizedState

/-!
# Nielsen & Chuang, Exercise 10.74 — fault-tolerant preparation of the five-qubit code encoded |0⟩

*(N&C §10.6.3, p. 493.)*

Construct a quantum circuit to fault-tolerantly generate the encoded `|0⟩` of the five-qubit
code.

## What the exercise asks

N&C (§10.6.3, p. 492) gives the general recipe for a stabilizer code: to prepare the encoded `|0⟩`,
*fault-tolerantly measure all the stabilizer generators and the encoded `Z̄`, then fix the signs of
the generators and of `Z̄` by applying appropriate fault-tolerant operations (the prescription in
the proof of Proposition 10.4).* Exercise 10.73 illustrates this for the seven-qubit Steane code;
this exercise asks for the same construction for the five-qubit code (§10.5.6), whose four
Figure-10.12 stabilizer generators `g₁ = XZZXI`, `g₂ = IXZZX`, `g₃ = XIXZZ`, `g₄ = ZXIXZ`
(`Concrete.fiveQubitGenIdx`) and logical operators `X̄ = X⊗⁵`, `Z̄ = Z⊗⁵` are fixed.

"Constructing the circuit" is therefore: take the five-qubit syndrome-measuring circuit of
Exercise 10.60 (`fiveSyndromeCircuit`, one Figure-10.13 measurement block per generator) and
**adjoin a fifth block measuring the logical `Z̄`**. Measuring all five commuting operators projects
the input onto a joint eigenstate; the Proposition-10.4 sign corrections then move it into the
`+1`-eigenspace of every operator — the encoded `|0⟩`. Each measurement is made *fault-tolerant* by
running it with a verified cat-state ancilla and transversal controlled gates (Figure 10.28,
Exercises 10.69/10.70), exactly as Exercise 10.73 does for the Steane code.

## What is formalised

The construction reuses the general Figure-10.13 measurement block `syndromeMeasureCircuit`
(Exercise 10.60) — the block whose fault-tolerant cat-state realisation is the subject of
Exercises 10.69–10.71 — applied to the five-operator family `Concrete.fiveQubitZeroGenIdx`
(`g₁,…,g₄` in blocks `0,…,3`, and `Z̄` in block `4`):

* `IsFiveEncodedZero` — the **stabilizer definition of the encoded `|0⟩`**: a `+1`-eigenstate of all
  five operators. It is *nonempty and unique*: the joint `+1`-eigenspace of the five independent
  commuting operators is exactly a line, `Concrete.fiveQubitZeroGen_stabilizedSubspace_finrank`
  (Proposition 10.5 with `k = 0`).
* `fiveEncodedZeroPrep` — the **encoded-`|0⟩` preparation circuit**, `Fin 5 → Evolution`: one
  measurement block per operator of `Concrete.fiveQubitZeroGenIdx`.
* `fiveEncodedZeroPrep_measures` — **each block measures its operator**: block `i` records the
  eigenvalue `(−1)ᵇ` of the `i`-th operator (a generator, or `Z̄` for `i = 4`) as its ancilla bit
  `b`, leaving the register in the eigenstate (Figure 10.13 working as described).
* `fiveEncodedZeroPrep_stabilized_zero` — **on the encoded `|0⟩` every block reads `0`**: an
  `IsFiveEncodedZero` state is left invariant with the all-zero syndrome, confirming successful
  preparation.
* `fiveEncodedZero_exists` — **the construction prepares a state (existence)**: there **is** an
  `IsFiveEncodedZero` state, so the circuit's target is nonempty (and hence
  `fiveEncodedZeroPrep_stabilized_zero` is not vacuous).
* `fiveEncodedZero_unique` — **it prepares exactly the encoded `|0⟩` (uniqueness)**: any two
  `IsFiveEncodedZero` states are equal up to a global phase (`ψ.toState = φ.toState`), so the five
  measurements pin the prepared state to a single codeword.

The last two lift the dimension count `Concrete.fiveQubitZeroGen_stabilizedSubspace_finrank`
(`finrank = 1`) to states through the reusable
`exists_hasEigenstate_one_of_stabilizedSubspace_finrank_eq_one` /
`hasEigenstate_one_toState_eq_of_stabilizedSubspace_finrank_eq_one`
(`AxQM/Postulates/API/StabilizedState.lean`) — turning "a full independent set of commuting Pauli
operators has a one-dimensional code space" into existence and uniqueness of the prepared
`PureState`.

The supporting Pauli-string algebra is in `AxQM/Concrete/FiveQubitCode.lean`: the five operators
pairwise commute so are jointly measurable (`Concrete.fiveQubitZeroGenIdx_commute`); they are
independent (`Concrete.fiveQubitZeroGenIdx_checkRow_linearIndependent`, so `Z̄ ∉ ⟨g₁,…,g₄⟩`); and
the encoded Pauli algebra `Z̄, X̄ ∈ N(S)` with `{X̄, Z̄} = 0`
(`Concrete.fiveQubitGen_commute_logicalZBar`, `_logicalXBar`,
`Concrete.fiveQubitLogicalXBar_not_commute_logicalZBar`) is what makes `Z̄` a genuine logical
operator distinguishing `|0⟩` (its `+1`-eigenstate) from `|1⟩ = X̄|0⟩` (its `−1`-eigenstate).

## Design and fidelity

* **The `Z̄` measurement is the whole point of the exercise.** Exercise 10.60 already measures the
  four *stabilizer* generators; a codeword is then any state in the two-dimensional code space. What
  turns "a codeword" into "the encoded `|0⟩`" is the extra `Z̄` measurement — the content N&C adds
  on p. 492 over plain syndrome measurement — which cuts the code space to the single `|0⟩` line
  (`finrank = 1`). Formalising the augmented five-block circuit and characterising its fixed encoded
  `|0⟩` is exactly that added content, not a restatement of Exercise 10.60.
* **Generic-eigenstate correctness, with existence and uniqueness proved.** As in Exercise 10.60,
  the measurement guarantees are stated for an arbitrary eigenstate, and `IsFiveEncodedZero`
  characterises the encoded `|0⟩` abstractly as the joint `+1`-eigenstate; the (entangled)
  five-qubit codeword vector need not be *exhibited*. But its existence and its uniqueness up to
  global phase are proved outright as `PureState`-level theorems (`fiveEncodedZero_exists` /
  `fiveEncodedZero_unique`, from the `finrank = 1` dimension count), matching the
  soundness+completeness standard of the Steane analogue (Exercise 10.73). No content is weakened:
  the circuit measures exactly `⟨g₁,…,g₄, Z̄⟩`, and its unique fixed point is the encoded `|0⟩`.
* **What is deliberately not formalised** (as in Exercises 10.69–10.71):
  (i) the *stochastic* fault-tolerance guarantee — a single component failure yields
  at most one encoded error and an incorrect result with probability `O(p²)` — needs a fault/cost
  model the axiom library does not express; and (ii) the explicit Proposition-10.4 *sign-correction*
  Pauli operators applied conditionally on the outcomes. The library-expressible
  operator/measurement core — the augmented circuit, its per-block measurement action, joint
  measurability, and the existence and uniqueness of the fixed encoded `|0⟩` — is what is captured
  here.

## Statements

The result is the preparation *circuit* (an `Evolution`) and its measurement action, stated
through `Evolution.evolvePure`, `PureState.tmul`, `qubitBasis` and the `Observable.HasEigenstate`
relation (as in Exercise 10.60). The Pauli-string and check-matrix algebra (`fiveQubitZeroGenIdx`
and its commutation, independence, and dimension facts) is in
`AxQM/Concrete/FiveQubitCode.lean`.
-/

namespace AxQM

/-- **The five-qubit code encoded `|0⟩` (stabilizer definition).** A pure state `ψ` on the
five-qubit register `qudit (2⁵)` is the encoded `|0⟩` when it is a simultaneous `+1`-eigenstate of
all five operators of `Concrete.fiveQubitZeroGenIdx` — the four Figure-10.12 stabilizer generators
`g₁,…,g₄` **and** the logical `Z̄ = Z⊗Z⊗Z⊗Z⊗Z`. By
`Concrete.fiveQubitZeroGen_stabilizedSubspace_finrank` this pins `ψ` to a one-dimensional line: the
`+1`-eigenstate of `Z̄` is the encoded `|0⟩`, its `−1`-eigenstate the encoded `|1⟩`. -/
def IsFiveEncodedZero (ψ : PureState (qudit (2 ^ 5))) : Prop :=
  ∀ i : Fin 5, (pauliStringHamiltonian (Concrete.fiveQubitZeroGenIdx i) 1).HasEigenstate 1 ψ

/-- **The five-qubit code encoded-`|0⟩` preparation circuit**, `Fin 5 → Evolution (qubit ⊗ qudit
32)`: one Figure-10.13 measurement block (`syndromeMeasureCircuit`) per operator of
`Concrete.fiveQubitZeroGenIdx` — the four stabilizer generators (blocks `0,…,3`, as in the syndrome
circuit `fiveSyndromeCircuit` of Exercise 10.60) plus a fifth block measuring the logical
`Z̄ = Z⊗⁵`. Measuring all five commuting operators and applying the Proposition-10.4 sign
corrections lands in the encoded `|0⟩`; fault tolerance comes from realising each block's
measurement with a verified cat-state ancilla (Figure 10.28, Exercises 10.69/10.70), as in the
Steane-code case of Exercise 10.73. -/
noncomputable def fiveEncodedZeroPrep (i : Fin 5) :
    Evolution (qubit.compose (qudit (2 ^ 5))) :=
  syndromeMeasureCircuit (Concrete.fiveQubitZeroGenIdx i)

/-- **Each block measures its operator.** Block `i` records the eigenvalue `(−1)ᵇ` of the `i`-th
operator of `Concrete.fiveQubitZeroGenIdx` (a stabilizer generator, or the logical `Z̄` for
`i = 4`) as its ancilla's measurement bit `b`, leaving the register in the eigenstate `ψ`. -/
theorem fiveEncodedZeroPrep_measures (i : Fin 5) (ψ : PureState (qudit (2 ^ 5))) (b : Fin 2)
    (hψ : (pauliStringHamiltonian (Concrete.fiveQubitZeroGenIdx i) 1).HasEigenstate
      ((-1 : ℝ) ^ (b : ℕ)) ψ) :
    (fiveEncodedZeroPrep i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis b).tmul ψ :=
  syndromeMeasureCircuit_measures _ ψ b hψ

/-- **The encoded `|0⟩` gives the all-zero syndrome.** An encoded-`|0⟩` state `ψ`
(`IsFiveEncodedZero`: a `+1`-eigenstate of every generator and of `Z̄`) is left invariant by every
block of the preparation circuit, each ancilla reading `0`: the circuit verifies (and, after the
Proposition-10.4 sign corrections, produces) the encoded `|0⟩`. -/
theorem fiveEncodedZeroPrep_stabilized_zero (ψ : PureState (qudit (2 ^ 5)))
    (hψ : IsFiveEncodedZero ψ) (i : Fin 5) :
    (fiveEncodedZeroPrep i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis 0).tmul ψ :=
  syndromeMeasureCircuit_stabilized_zero _ ψ (hψ i)

/-- **The construction prepares a state (existence).** There **is** an encoded-`|0⟩` state: a pure
state `ψ` that is a common `+1`-eigenstate of all five operators `⟨g₁,…,g₄, Z̄⟩`
(`IsFiveEncodedZero`). Physically, the five-block circuit `fiveEncodedZeroPrep` — measuring the four
stabilizer generators and the logical `Z̄` and fixing every sign to `+1` — has a nonempty target:
its joint `+1`-eigenspace is nonzero.

This lifts the dimension count `Concrete.fiveQubitZeroGen_stabilizedSubspace_finrank`
(`finrank = 1 ≠ 0`, Proposition 10.5 with `k = 0`) to states via
`exists_hasEigenstate_one_of_stabilizedSubspace_finrank_eq_one`. Without it,
`fiveEncodedZeroPrep_stabilized_zero` would be vacuous — this is what makes it a genuine preparation
guarantee. -/
theorem fiveEncodedZero_exists : ∃ ψ, IsFiveEncodedZero ψ :=
  exists_hasEigenstate_one_of_stabilizedSubspace_finrank_eq_one _
    Concrete.fiveQubitZeroGen_stabilizedSubspace_finrank

/-- **The construction prepares exactly the encoded `|0⟩` (uniqueness).** Any two encoded-`|0⟩`
states `ψ`, `φ` (each `IsFiveEncodedZero`: a common `+1`-eigenstate of all five operators
`⟨g₁,…,g₄, Z̄⟩`) have the same density operator, `ψ.toState = φ.toState` — they are equal up to a
global phase. So post-selecting the all-`+1` outcome of the five measurements pins the prepared
state down to a *single* encoded `|0⟩`: the extra `Z̄` measurement (over the four stabilizer
generators
alone, whose code space is two-dimensional) is exactly what cuts the codeword down to the unique
`|0⟩` line.

This lifts `Concrete.fiveQubitZeroGen_stabilizedSubspace_finrank` (`finrank = 1`, the code space is
a line) to states via
`hasEigenstate_one_toState_eq_of_stabilizedSubspace_finrank_eq_one`. "Up to a global phase" is the
equality of density operators `PureState.toState` (which erases the phase), as in Exercise 10.73. -/
theorem fiveEncodedZero_unique {ψ φ : PureState (qudit (2 ^ 5))}
    (hψ : IsFiveEncodedZero ψ) (hφ : IsFiveEncodedZero φ) :
    ψ.toState = φ.toState :=
  hasEigenstate_one_toState_eq_of_stabilizedSubspace_finrank_eq_one _
    Concrete.fiveQubitZeroGen_stabilizedSubspace_finrank hψ hφ

end AxQM
