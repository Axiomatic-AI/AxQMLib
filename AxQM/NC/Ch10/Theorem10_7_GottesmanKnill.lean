/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StabilizerMeasurement
import AxQM.Postulates.API.StabilizerEvolution
import AxQM.Concrete.CliffordStabilizerTracking
import AxQM.Concrete.StabilizerSimulationCost
import AxQM.Concrete.StabilizerSimulator
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Theorem 10.7 — the Gottesman–Knill theorem

*(N&C §10.5.4, p. 464.)*

Gottesman-Knill: stabilizer computations (prep, H, S, CNOT, Pauli, Pauli-group measurements) are
classically efficiently simulable.

## What the theorem claims, and how it is formalised

The theorem's substantive content is a **complexity claim**: the listed stabiliser computation "may
be *efficiently* simulated on a classical computer" — N&C's `O(n²m)` classical operations for `m`
operations on `n` qubits. Stripped of efficiency, "simulable on a classical computer" is trivially
true of every finite quantum computation, so the efficiency bound is exactly what carries the
theorem's force. That bound is a formalisable proposition of a kind this library already expresses:
the sibling **Theorem 10.6** (same chapter) proves "`O(n²)` normaliser gates" as
`Concrete.isPauliNormalizer_eq_smul_cliffordCircuit_bigO` (`List.length C ≤ K · n²`), in the
`ℕ`-valued-count-with-a-uniform-polynomial-ceiling idiom used throughout
(`mcNotGateBound_isBigO_sq`, `qftControlledRkCount_isTheta_sq`).

Accordingly this item's **formalisation is a collection of definitions and theorems** — not a single
"pinnacle" statement — with three pillars, each a genuine `def`/`theorem` (the parts are listed with
their locations below):

1. **A classical simulator** over an inductive stabiliser-computation type enumerating exactly N&C's
   allowed operations — `Concrete.StabilizerOp` (`prep`, `clifford`, `pauli`, `measure`) folded into
   `Concrete.StabilizerComputation`, tracking the `O(n²)`-cell check-matrix/sign tableau
   `Concrete.StabilizerTableau` by the per-operation update `Concrete.StabilizerOp.stepTableau`
   (folded to `Concrete.StabilizerTableau.run`).
2. **The efficiency bound**, the `O(n²m)` bound: a defined `ℕ`-valued cost
   `Concrete.StabilizerComputation.simCost` with
   `Concrete.exists_simCost_le_mul_sq_length : ∃ K, ∀ n prog, simCost prog ≤ K · n² · prog.length`
   (a *universal* `K`, uniform in both `n` and `m = prog.length`).
3. **The correctness theorem** — the simulator's tracked stabiliser genuinely describes the actual
   quantum state, discharged per operation by the update rules N&C's "we have already *implicitly*
   proved … keep[s] track of the generators" refers to. Its **unitary fragment** (prep + Clifford /
   Pauli gates) is `Concrete.StabilizerTableau.run_stabilizes`; the **measurement** part is the
   §10.5.3 measurement analysis in `AxQM/Postulates/API/StabilizerMeasurement.lean`.

These three pillars, together with the Eq. (10.87) stabiliser-under-unitary law and the preparation
facts they use, make up the formalisation. The sections below present the pillars in the order
prep → gates → measurement → efficiency; the module docstrings of the cited files carry the proof
detail, and the closing section lists the declarations.

## 1. State preparation, and the unitary correctness fragment

*(`AxQM/Concrete/StabilizerSimulator.lean`.)*

The classically-tracked description is a `Concrete.StabilizerTableau` (`n` signed generators
`gen i`, `sign i`); its correctness invariant `Concrete.StabilizerTableau.Stabilizes v` asserts each
signed generator `sign i • pauliString (gen i)` fixes the state vector `v`. The simulator's
per-operation tableau update `Concrete.StabilizerOp.stepTableau` runs *in lockstep* with the actual
raw-state evolution `Concrete.StabilizerOp.stepState`, and the invariant is **preserved** by every
unitary operation:

* **Preparation.** A computational-basis state `|0…0⟩` is the simultaneous `+1` eigenstate of the
  single-qubit `Z` observables — the trivial stabiliser `⟨Z₁, …, Zₙ⟩`. The simulator fact is
  `Concrete.zGenPauli_mulVec_compBasisZero` (`Zⱼ` fixes the all-zeros vector
  `Concrete.compBasisZero`) assembled into `Concrete.StabilizerTableau.prep_stabilizes` (the trivial
  tableau
  `Concrete.StabilizerTableau.prep` stabilises `|0…0⟩`). Its physics counterparts —
  `|0⟩` / `|1⟩` are the `±1` eigenstates of `Z` — are `qubitKet0_hasEigenstate_pauliZ` /
  `qubitBasis_one_hasEigenstate_pauliZ` (`AxQM/NC/Ch4/Exercise4_1.lean`), with
  `Concrete.mem_stabilizedSubspace` characterising the stabilised subspace.
* **Hadamard / phase / controlled-`NOT` gates (Clifford dynamics).** The updated signed generator
  `(c · g.sign a) • P_{g.act a}` fixes the evolved vector `g.toMatrix ·ᵥ v`:
  `Concrete.CliffordGate.smul_pauliString_mulVec_stabilizes` — Eq. (10.87) at the level of one
  generator, via `Concrete.conj_mulVec_toMatrix_mulVec` and the conjugation identity
  `Concrete.CliffordGate.conj`.
* **Pauli gates.** Conjugation by a Pauli string flips only the sign
  (`Concrete.pauliString_conj`), leaving the check row fixed:
  `Concrete.pauli_smul_pauliString_mulVec_stabilizes` (the `act = id` case of Eq. (10.87)).
* **Composed.** `Concrete.StabilizerOp.step_stabilizes` assembles the three into one preservation
  step, and the **main result** `Concrete.StabilizerTableau.run_stabilizes` folds it over a whole
  **measurement-free** computation: if the tableau `T` stabilises `v`, the tableau
  `Concrete.StabilizerTableau.run prog T` obtained by running `prog` stabilises the evolved state
  `Concrete.runState prog v`.
  Started from `prep_stabilizes`/`compBasisZero` this propagates the invariant along any prefix of
  unitary operations — "the classical computer keeps track of the generators of the stabiliser"
  (N&C §10.5.4) is a proved theorem for the whole unitary fragment.

**The stabiliser-under-unitary law (N&C Eq. 10.87).** N&C's §10.5.2 opens
with the equation that makes the simulation work: if `g|ψ⟩ = |ψ⟩` and a unitary `U` is applied then
`U|ψ⟩` is stabilised by `U g U†`, "so to compute the change in the stabiliser we need only compute
how it affects the generators". Formalised for states, observables and evolutions in
`AxQM/Postulates/API/StabilizerEvolution.lean`:

* `Observable.conjByEvolution` — the conjugated observable `U A U†`;
* `Observable.HasEigenstate.conjByEvolution_evolvePure` / `…_evolvePure_one` — Eq. (10.87): if
  `A|ψ⟩ = μ|ψ⟩` then `(U A U†)(U|ψ⟩) = μ (U|ψ⟩)`; in the stabiliser case `μ = 1`, "`U|ψ⟩` is
  stabilised by `U g U†`".

Its check-matrix instance — that the *classically-updated* generator is a genuine stabiliser of the
evolved state — is `AxQM/Concrete/CliffordStabilizerTracking.lean`:
`Concrete.conj_mulVec_toMatrix_mulVec` (Eq. (10.87), matrix form) and
`Concrete.CliffordCircuit.updatedGenerator_mulVec_toMatrix_mulVec(_of_mem)` (the classically-updated
signed generator `U.sign g • P_{U.act g}` fixes `U ·ᵥ v`, for a single generator and for a whole
stabilised subspace `V_S`). The allowed unitaries are **Clifford gates**
(`Concrete.CliffordGate` — `had`/`phase`/`cnot`, with `act`/`sign`/`conj`/`mul_conjTranspose`, and
their circuit form `Concrete.CliffordCircuit`/`conj_pauliString`): conjugation carries each Pauli
string to a Pauli string, so the generators are updated by a classically-computable map on the
check-matrix rows together with a `±1` sign.

## 2. Measurement of a Pauli-group observable (N&C §10.5.3)

*(`AxQM/Postulates/API/StabilizerMeasurement.lean`.)*

A Pauli-group element is a self-adjoint involution, hence a `±1` observable measured by
`Observable.signMeasurement`. Measuring it on a stabiliser state updates the stabiliser classically,
per N&C's two cases:

* **Deterministic**, both sub-cases N&C states:
  - `g ∈ S` (observable stabilises `|ψ⟩`):
    `Observable.bornProb_signMeasurement_plus_of_hasEigenstate_one` (`p(+1) = 1`),
    `…_minus_of_hasEigenstate_one` (`p(−1) = 0`),
    `Observable.postMeasPlus_eq_of_hasEigenstate_one` (state undisturbed);
  - `−g ∈ S` (`g|ψ⟩ = −|ψ⟩`), the mirror:
    `Observable.bornProb_signMeasurement_minus_of_hasEigenstate_neg_one` (`p(−1) = 1`),
    `…_plus_of_hasEigenstate_neg_one` (`p(+1) = 0`),
    `Observable.postMeasMinus_eq_of_hasEigenstate_neg_one` (state undisturbed).
* **Random** (the observable anticommutes with a stabiliser generator): the engine
  `Observable.expectation_eq_zero_of_anticomm_stabilizer` (N&C eqs. 10.96–10.100, with the general
  `…_eigenstate` form) gives `Observable.bornProb_signMeasurement_plus_of_anticomm` /
  `…_minus_of_anticomm` (`p(+1) = p(−1) = 1/2`). The posterior is a `±1` eigenstate of the measured
  observable (`Observable.postMeasPlus_hasEigenstate` / `postMeasMinus_hasEigenstate`): the leading
  generator is replaced by `±g`.
* **Stabiliser preservation** (`Observable.hasEigenstate_one_postMeasPlus_of_commute`,
  `…_postMeasMinus_of_commute`): a generator that commutes with the measured observable and
  stabilised `|ψ⟩` still stabilises the collapse, so the tail `g₂, …, gₙ` survives — the new
  stabiliser is `⟨±g, g₂, …, gₙ⟩`. The commutativity hypothesis is N&C's WLOG generator-set
  normalisation (replace any anticommuting `gₖ` by `g₁ gₖ` so only `g₁` anticommutes).

## 3. The efficiency bound (N&C's `O(n²m)`) — `AxQM/Concrete/StabilizerSimulationCost.lean`

The `O(n²m)` cost bound is the theorem's substantive content, in the library's resource-bound idiom:

* `Concrete.StabilizerOp` — the inductive operation type enumerating N&C's allowed elements
  (`prep`, `clifford g`, `pauli p`, `measure p`); `Concrete.StabilizerComputation n := List (…)` is
  a computation of `m` operations.
* `Concrete.StabilizerOp.tableauCost` — the per-operation count of elementary tableau updates
  (`n · (n+1)` for prep/Clifford/Pauli, `2 · n · (n+1)` for measurement), with
  `Concrete.StabilizerOp.tableauCost_le : tableauCost ≤ 4 · n²` (N&C's uniform `O(n²)` per op).
* `Concrete.StabilizerComputation.simCost` — the total simulation cost (`∑` of the per-op costs),
  and the bound
  `Concrete.exists_simCost_le_mul_sq_length : ∃ K, ∀ n prog, simCost prog ≤ K · n² · prog.length` —
  a universal `K` (here `4`) uniform in both `n` and `m`, the faithful reading of
  N&C's "`O(n²m)` operations on a classical computer" (a per-`n` existential `K` would be vacuous).

## Classical control conditioned on measurement outcomes

N&C's statement also permits "classical control conditioned on the outcome of such measurements".
This is subsumed rather than modelled as extra apparatus: in a *classical* simulation each
measurement outcome is computed by the simulator itself, so an adaptively-controlled computation is,
once its outcomes are fixed, an ordinary fixed operation list of the same length. The cost model
counts `m` operations each costing `O(n²)` regardless of how the operations were selected
(`StabilizerOp.tableauCost` and `simCost` are outcome-independent), and the unitary-fragment
correctness `run_stabilizes` applies to whichever prefix of unitary operations actually executes —
so branching on outcomes changes neither the `O(n²m)` bound nor the per-operation correctness.

## Split of the correctness theorem into unitary and measurement parts

The unitary fragment (`run_stabilizes`) is stated for raw state vectors in
`AxQM/Concrete/StabilizerSimulator.lean`, while the measurement rules are stated for states and
observables in `AxQM/Postulates/API/StabilizerMeasurement.lean`. This is a decomposition, not a
weakening: measurement's effect on the state is a projective (Born-rule) collapse, which is not a
matrix acting on a raw vector, and the split matches N&C's own two-part treatment (§10.5.2 unitary
dynamics; §10.5.3 measurement).

## Declarations

**Simulator + unitary-fragment correctness** (`AxQM/Concrete/StabilizerSimulator.lean`):
`Concrete.compBasisZero`, `Concrete.zGenPauli_mulVec_compBasisZero`, `Concrete.StabilizerTableau`,
`Concrete.StabilizerTableau.Stabilizes`, `Concrete.StabilizerTableau.prep`,
`Concrete.StabilizerTableau.prep_stabilizes`,
`Concrete.CliffordGate.smul_pauliString_mulVec_stabilizes`,
`Concrete.pauli_smul_pauliString_mulVec_stabilizes`, `Concrete.StabilizerOp.IsMeasurement`,
`Concrete.StabilizerOp.stepState`, `Concrete.StabilizerOp.stepTableau`,
`Concrete.StabilizerOp.step_stabilizes`, `Concrete.StabilizerTableau.run`, `Concrete.runState`,
`Concrete.StabilizerTableau.run_stabilizes`.

**Efficiency `O(n²m)` bound** (`AxQM/Concrete/StabilizerSimulationCost.lean`):
`Concrete.StabilizerOp`,
`Concrete.StabilizerComputation`, `Concrete.StabilizerOp.tableauCost`,
`Concrete.StabilizerOp.tableauCost_le`, `Concrete.StabilizerComputation.simCost`,
`Concrete.exists_simCost_le_mul_sq_length`.

**Eq. (10.87) stabiliser-under-unitary law** (`AxQM/Postulates/API/StabilizerEvolution.lean`):
`Observable.conjByEvolution`, `Observable.HasEigenstate.conjByEvolution_evolvePure`,
`Observable.HasEigenstate.conjByEvolution_evolvePure_one`. Its check-matrix instance
(`AxQM/Concrete/CliffordStabilizerTracking.lean`): `Concrete.conj_mulVec_toMatrix_mulVec`,
`Concrete.CliffordCircuit.updatedGenerator_mulVec_toMatrix_mulVec`,
`Concrete.CliffordCircuit.updatedGenerator_mulVec_toMatrix_mulVec_of_mem`.

**§10.5.3 measurement update rules** (`AxQM/Postulates/API/StabilizerMeasurement.lean`):
`Observable.bornProb_signMeasurement_plus_of_hasEigenstate_one`,
`Observable.bornProb_signMeasurement_minus_of_hasEigenstate_one`,
`Observable.postMeasPlus_eq_of_hasEigenstate_one`,
`Observable.bornProb_signMeasurement_minus_of_hasEigenstate_neg_one`,
`Observable.bornProb_signMeasurement_plus_of_hasEigenstate_neg_one`,
`Observable.postMeasMinus_eq_of_hasEigenstate_neg_one`,
`Observable.expectation_eq_zero_of_anticomm_eigenstate`,
`Observable.expectation_eq_zero_of_anticomm_stabilizer`,
`Observable.bornProb_signMeasurement_plus_of_anticomm_eigenstate`,
`Observable.bornProb_signMeasurement_minus_of_anticomm_eigenstate`,
`Observable.bornProb_signMeasurement_plus_of_anticomm`,
`Observable.bornProb_signMeasurement_minus_of_anticomm`,
`Observable.hasEigenstate_one_postMeasPlus_of_commute`,
`Observable.hasEigenstate_one_postMeasMinus_of_commute`.

**Preparation facts** (`AxQM/NC/Ch4/Exercise4_1.lean`, `AxQM/Concrete/`):
`qubitKet0_hasEigenstate_pauliZ`,
`qubitBasis_one_hasEigenstate_pauliZ`, `Concrete.zGenPauli`, `Concrete.mem_stabilizedSubspace`.
Clifford data (`AxQM/Concrete/PauliStringCliffordCircuit.lean`): `Concrete.CliffordGate`,
`Concrete.CliffordGate.act`, `Concrete.CliffordGate.sign`, `Concrete.CliffordGate.conj`,
`Concrete.CliffordGate.mul_conjTranspose`, `Concrete.CliffordCircuit`,
`Concrete.CliffordCircuit.conj_pauliString`.
-/
