/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.FredkinTwoQubitCircuit
import AxQM.Core.FredkinFiveGateSwapIdentity
import AxQM.Postulates.API.ToffoliHadamard

/-!
# Nielsen & Chuang, Exercise 4.25 (Fredkin gate construction)

*(N&C p. 182.)*

Construct the Fredkin (controlled-swap) gate from Toffoli/CNOT; minimize gates.

The Fredkin, Toffoli and `CNOT` gates are closed-system evolutions (Postulate 5 / `Evolution`);
the answer is a set of *gate identities* — equalities of `Evolution` objects — expressing the
Fredkin gate as a product of Toffoli / `CNOT` / two-qubit gates, using `fredkinGate`,
`toffoliGate`, `middleToffoliGate`, `cnotGate`, `Evolution.comp`, `Evolution.onRight` and
`twoQubitCircuit`.

## The formalisation

* **The gate itself** is `fredkinGate = C(SWAP)` (`AxQM/Postulates/API/Fredkin.lean`); the transform
  (4.30) is its defining action, the two control branches
  `fredkinGate_evolvePure_ketZero_left` (identity block) and `fredkinGate_evolvePure_ketOne_left`
  (swap block).
* `fredkinGate_eq_toffoli_comp_middleToffoli_comp_toffoli` — **Part 1**: the Fredkin gate is the
  product of three Toffoli gates, `Fredkin = Toffoli · middleToffoli · Toffoli`. The two outer
  Toffolis (`toffoliGate`, controls 1, 2 and target 3) and the middle one (`middleToffoliGate`,
  controls 1, 3 and target 2) are exactly the controlled versions of the three `CNOT`s in the swap
  identity `SWAP = CNOT · reversedCNOT · CNOT`, controlled on qubit 1 "one at a time" per the hint.
* `fredkinGate_eq_cnot_comp_middleToffoli_comp_cnot` — **Part 2**: the first and last Toffoli gates
  may be replaced by (uncontrolled) `CNOT` gates on the target pair,
  `Fredkin = (I ⊗ CNOT) · middleToffoli · (I ⊗ CNOT)`. Dropping the control on the outer two gates
  is valid because when the control qubit is `|0⟩` the two `CNOT`s cancel (`CNOT² = I`), and when it
  is `|1⟩` all three gates fire, reproducing `SWAP = CNOT · reversedCNOT · CNOT`.
* `fredkinSixGates` / `twoQubitCircuit_fredkinSixGates` /
  `exists_twoQubitCircuit_eq_fredkinGate_six` — **Part 3**: replacing the middle Toffoli by its
  Figure 4.8 decomposition and merging one outer `CNOT` into the adjacent gate gives a Fredkin
  construction using only **six two-qubit gates**,
  `∃ gs, twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 6`.
* `fredkinFiveGates` / `twoQubitCircuit_fredkinFiveGates` /
  `exists_twoQubitCircuit_eq_fredkinGate_five` — **Part 4**: the even simpler
  Smolin–DiVincenzo construction using only **five two-qubit gates**,
  `∃ gs, twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 5`. The five gates are two entangling
  `pair` gates `B†`, `B` on the target pair (`B = swapDiagonalizingGate`) sandwiching three
  controlled-single-qubit `ctrl` gates `S`, `Z`, `X`.

## Design notes

* **Two-qubit-gate cost model (Part 3, N&C fidelity).** Part 3 counts *two-qubit gates* — a
  controlled single-qubit gate `C(V)` is **one** gate, the convention that makes Figure 4.8's
  `C²(U)` "five two-qubit gates". To make "using only six two-qubit gates" a *genuine proposition*
  (not a tally the reader does by eye), the circuit is a `List TwoQubitGate3` in the cost model
  `Core.TwoQubitGateCircuit`, and the claim is the honest existential
  `∃ gs, twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 6` — `twoQubitCount` is the list
  length, and every element of the alphabet *is* a two-qubit gate.
* **The six-gate circuit.** Start from Part 2, `Fredkin = (I ⊗ CNOT) · middleToffoli · (I ⊗ CNOT)`
  (seven two-qubit gates once the middle Toffoli is expanded), and substitute the
  five-two-qubit-gate Figure 4.8 decomposition `middleToffoliTwoQubitGates`
  (`Core.FredkinTwoQubitCircuit`, the middle Toffoli as `C²(V²)` with `V² = X`). Its first
  Figure-4.8 gate is a `pair` (a `C(V)` on the swapped target pair `{1, 2}`), so the adjacent outer
  `CNOT` — itself a `pair` on `{1, 2}` — **merges** into it:
  `pair (revC V) · pair CNOT = pair (revC V · CNOT)`, one two-qubit gate. That drops the count
  `7 → 6`. The merge is the monoid homomorphism `Evolution.onRight_comp`
  (`(A ⊗ 1)(B ⊗ 1) = (A · B) ⊗ 1` on the idle control wire).
* **Proof route (Part 3).** `twoQubitCircuit_fredkinSixGates` unfolds the six gates, rewrites the
  combined tail back through `Evolution.onRight_comp` into the two-gate form, and normalises the
  `Evolution`-monoid expression (`comp_assoc`/`comp_id`) so that the six-gate circuit is literally
  `(I ⊗ CNOT) · twoQubitCircuit (middleToffoliTwoQubitGates V) · (I ⊗ CNOT)`; then the middle
  identity (`… _eq_middleToffoliGate`, `V² = X`) and Part 2 close it. No basis casework is redone —
  it is inherited from the already-proven Figure 4.8 identity.
* **Statement shape (N&C fidelity, Parts 1–2).** Parts 1 and 2 ask for *circuits* implementing the
  Fredkin gate; the verifiable content is that each circuit *equals* the Fredkin gate. We state
  these as full `Evolution` equalities (not "on basis states" surrogates): `fredkinGate = …`,
  discharged by `threeQubit_evolution_ext` (agreement on the eight computational-basis states).
* **Five two-qubit gates (Part 4, N&C's final question) needs a genuinely entangling gate.** Part 3
  combined gates as far as a controlled-single-qubit (`ctrl`) alphabet allows; five is *not*
  reachable by merging further (the same obstruction as Problem 3.5 — classical reversible 2-bit
  gates cannot
  build the Fredkin gate). The five-gate construction must spend one of its gates on a genuinely
  **entangling** two-qubit gate. The clean Smolin–DiVincenzo choice puts the two entangling gates on
  the *target* pair as `pair B†`, `pair B` (`B = swapDiagonalizingGate`, the Fourier-type gate
  diagonalising the four-cycle `(I ⊗ X) · SWAP`), sandwiching three `ctrl` gates:
  `fredkinFiveGates = [pair B†, ctrl 0 S, ctrl 1 Z, pair B, ctrl 0 X]`. This uses the SAME
  `TwoQubitGate3` cost model as Part 3, so "five two-qubit gates" compares like-for-like with "six".
* **Proof route (Part 4).** On control `|0⟩` the two `pair` gates cancel (`B† B = 1`) and the `ctrl`
  gates idle, so the branch is the identity; on control `|1⟩` all gates fire and the branch operator
  must implement `SWAP`. This split is discharged once and for all by the
  control-branch reduction `twoQubitCircuit_pair_ctrl_eq_fredkinGate`
  (`Core.FredkinFiveGateCircuit`), which reduces the whole three-qubit claim to the single two-qubit
  identity `B† · S_a · Z_b · B · X_a = SWAP`. That identity is
  `swapDiagonalizingGate_swapConjugation` (`Core.FredkinFiveGateSwapIdentity`): `B` maps
  computational basis states to `|±⟩`/`|±i⟩` products, so it is proved by two-qubit basis
  extensionality plus the single-qubit `S`/`Z` truth tables of
  `Postulates.API.PhaseGateEigenbasis`. No three-qubit basis casework is redone here — the theorem
  for Part 4 just names the five-gate list and applies the reduction.
-/

noncomputable section

namespace AxQM

/-! ### Parts 1 & 2: the three-Toffoli and Toffoli + two-`CNOT` constructions -/

/-- **Nielsen & Chuang Exercise 4.25, Part 1 (three-Toffoli construction).** The Fredkin
(controlled-swap) gate is the product of three Toffoli gates,
`Fredkin = Toffoli · middleToffoli · Toffoli`: controlling the swap identity
`SWAP = CNOT · reversedCNOT · CNOT` on qubit 1 "one gate at a time" turns each `CNOT` into a
Toffoli. The two outer gates are the ordinary Toffoli `toffoliGate` (controls 1, 2; target 3) and
the middle gate is `middleToffoliGate` (controls 1, 3; target 2). Proved by verifying both sides on
the eight computational-basis states. -/
theorem fredkinGate_eq_toffoli_comp_middleToffoli_comp_toffoli :
    fredkinGate = toffoliGate.comp (middleToffoliGate.comp toffoliGate) := by
  refine threeQubit_evolution_ext (fun q1 q2 q3 => ?_)
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp, toffoliGate_evolvePure_qubitBasis,
    middleToffoliGate_evolvePure_qubitBasis, toffoliGate_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
    simp only [Fin.mk_zero, Fin.mk_one, fredkinGate_evolvePure_ketZero_left,
      fredkinGate_evolvePure_ketOne_left, Fin.reduceAdd, Fin.reduceMul]

/-- **Nielsen & Chuang Exercise 4.25, Part 2 (first and last Toffoli replaced by `CNOT`).** In the
three-Toffoli construction the two outer Toffoli gates may be replaced by (uncontrolled) `CNOT`
gates on the target pair, `Fredkin = (I ⊗ CNOT) · middleToffoli · (I ⊗ CNOT)`. Dropping the control
on the outer gates is valid because with control `|0⟩` the two `CNOT`s cancel (`CNOT² = I`) and with
control `|1⟩` all three gates fire, reproducing the swap identity `SWAP = CNOT · reversedCNOT ·
CNOT`. Here `cnotGate.onRight qubit` is `I ⊗ CNOT`, the `CNOT` on qubits 2, 3 with no control on
qubit 1. Proved by verifying both sides on the eight computational-basis states. -/
theorem fredkinGate_eq_cnot_comp_middleToffoli_comp_cnot :
    fredkinGate
      = (cnotGate.onRight qubit).comp (middleToffoliGate.comp (cnotGate.onRight qubit)) := by
  refine threeQubit_evolution_ext (fun q1 q2 q3 => ?_)
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp, Evolution.onRight_evolvePure,
    cnotGate_evolvePure_qubitBasis, middleToffoliGate_evolvePure_qubitBasis,
    Evolution.onRight_evolvePure, cnotGate_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
    simp only [Fin.mk_zero, Fin.mk_one, fredkinGate_evolvePure_ketZero_left,
      fredkinGate_evolvePure_ketOne_left, Fin.reduceAdd, Fin.reduceMul]

/-! ### Part 3: the six-two-qubit-gate construction (Figure 4.8 for the middle Toffoli) -/

/-- **The six two-qubit gates of the Fredkin construction** (Exercise 4.25 part 3). Take the Part-2
circuit `Fredkin = (I ⊗ CNOT) · middleToffoli · (I ⊗ CNOT)` and expand the middle Toffoli by its
Figure 4.8 decomposition `middleToffoliTwoQubitGates V` (for a square root `V` of `X`), giving seven
two-qubit gates; the innermost gate of Figure 4.8 is a `pair` on the swapped target pair `{1, 2}`,
so the adjacent outer `CNOT` (also a `pair` on `{1, 2}`) merges into it,
`pair (reversedControlledUnitary V) · pair CNOT = pair ((reversedControlledUnitary V) · CNOT)`.
The result is the length-`6` list: an outer `I ⊗ CNOT`, then the four remaining Figure 4.8 gates,
then the single combined two-qubit gate. In *list order* the leftmost element is applied last. -/
def fredkinSixGates (V : Evolution qubit) : List TwoQubitGate3 :=
  [TwoQubitGate3.pair cnotGate,
   TwoQubitGate3.ctrl 0 V,
   TwoQubitGate3.ctrl 1 pauliXGate,
   TwoQubitGate3.pair (reversedControlledUnitary V.adjoint),
   TwoQubitGate3.ctrl 1 pauliXGate,
   TwoQubitGate3.pair ((reversedControlledUnitary V).comp cnotGate)]

/-- **Nielsen & Chuang Exercise 4.25, Part 3 (six-two-qubit-gate construction).** Whenever `V` is a
square root of `X` (`V.comp V = pauliXGate`), the six-gate circuit `fredkinSixGates V` equals the
Fredkin gate. Proof: the last gate is the merge
`pair ((reversedControlledUnitary V).comp cnotGate)`; rewriting it back through
`Evolution.onRight_comp` and normalising the `Evolution`-monoid product
exhibits the six-gate circuit as `(I ⊗ CNOT) · twoQubitCircuit (middleToffoliTwoQubitGates V) ·
(I ⊗ CNOT)`, which by the middle-Toffoli Figure 4.8 identity
(`twoQubitCircuit_middleToffoliTwoQubitGates_eq_middleToffoliGate`) and Part 2 is `fredkinGate`. No
basis casework is redone. -/
theorem twoQubitCircuit_fredkinSixGates (V : Evolution qubit) (hV : V.comp V = pauliXGate) :
    twoQubitCircuit (fredkinSixGates V) = fredkinGate := by
  have key : twoQubitCircuit (fredkinSixGates V)
      = (cnotGate.onRight qubit).comp
          ((twoQubitCircuit (middleToffoliTwoQubitGates V)).comp (cnotGate.onRight qubit)) := by
    simp only [fredkinSixGates, middleToffoliTwoQubitGates, twoQubitCircuit_cons,
      twoQubitCircuit_nil, TwoQubitGate3.denote_pair, TwoQubitGate3.denote_ctrl_zero,
      TwoQubitGate3.denote_ctrl_one]
    rw [← Evolution.onRight_comp]
    simp only [Evolution.one_def, Evolution.comp_id, Evolution.comp_assoc]
  rw [key, twoQubitCircuit_middleToffoliTwoQubitGates_eq_middleToffoliGate V hV,
    ← fredkinGate_eq_cnot_comp_middleToffoli_comp_cnot]

/-- **The Fredkin construction of Part 3 uses six two-qubit gates.** The list has length `6`, so its
`twoQubitCount` is `6` — every element is a genuine two-qubit gate. -/
theorem twoQubitCount_fredkinSixGates (V : Evolution qubit) :
    twoQubitCount (fredkinSixGates V) = 6 := rfl

/-- **The Fredkin gate is implementable by six two-qubit gates** (Exercise 4.25 part 3, existence
form). There is a `TwoQubitGate3` circuit whose evolution is `fredkinGate` and whose `twoQubitCount`
is `6`. The square root `V` of `X` is supplied by `Evolution.exists_comp_self_eq`, so no concrete √X
gate is named. This is the honest "the Fredkin gate can be built from six two-qubit gates"
proposition N&C part 3 asks for. -/
theorem exists_twoQubitCircuit_eq_fredkinGate_six :
    ∃ gs : List TwoQubitGate3,
      twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 6 := by
  obtain ⟨V, hV⟩ := Evolution.exists_comp_self_eq pauliXGate
  exact ⟨fredkinSixGates V, twoQubitCircuit_fredkinSixGates V hV,
    twoQubitCount_fredkinSixGates V⟩

/-! ### Part 4: the five-two-qubit-gate construction (Smolin–DiVincenzo) -/

/-- **The five two-qubit gates of the Fredkin construction** (Exercise 4.25 part 4). Reading the
list right to left (leftmost applied last): a controlled-`X`, the entangling gate `B` on the target
pair, a controlled-`Z`, a controlled-`S`, then the entangling gate `B†` on the target pair, where
`B = swapDiagonalizingGate`. Unlike Part 3's six gates — all merges of a controlled-single-qubit
alphabet — this construction spends two of its five gates on the genuinely entangling `pair B`,
`pair B†`; that is what buys the drop from six to five (a controlled-single-qubit alphabet provably
cannot, Smolin–DiVincenzo). -/
def fredkinFiveGates : List TwoQubitGate3 :=
  [TwoQubitGate3.pair swapDiagonalizingGate.adjoint,
   TwoQubitGate3.ctrl 0 sGate,
   TwoQubitGate3.ctrl 1 pauliZGate,
   TwoQubitGate3.pair swapDiagonalizingGate,
   TwoQubitGate3.ctrl 0 pauliXGate]

/-- **Nielsen & Chuang Exercise 4.25, Part 4 (five-two-qubit-gate construction).** The five-gate
circuit `fredkinFiveGates` equals the Fredkin gate. Proof: this is exactly the shape of the
control-branch reduction `twoQubitCircuit_pair_ctrl_eq_fredkinGate` with
`B = swapDiagonalizingGate`, `W₁ = X`, `W₂ = Z`, `W₃ = S`, whose two-qubit `SWAP`-conjugation is
`swapDiagonalizingGate_swapConjugation`; no three-qubit basis casework is redone here. -/
theorem twoQubitCircuit_fredkinFiveGates :
    twoQubitCircuit fredkinFiveGates = fredkinGate :=
  twoQubitCircuit_pair_ctrl_eq_fredkinGate swapDiagonalizingGate pauliXGate pauliZGate sGate
    swapDiagonalizingGate_swapConjugation

/-- **The Fredkin construction of Part 4 uses five two-qubit gates.** The list has length `5`, so
its `twoQubitCount` is `5` — every element is a genuine two-qubit gate. -/
theorem twoQubitCount_fredkinFiveGates : twoQubitCount fredkinFiveGates = 5 := rfl

/-- **The Fredkin gate is implementable by five two-qubit gates** (Exercise 4.25 part 4, existence
form). There is a `TwoQubitGate3` circuit whose evolution is `fredkinGate` and whose `twoQubitCount`
is `5`. This is the honest "the Fredkin gate can be built from five two-qubit gates" proposition
N&C part 4 asks for — the strongest of the four constructions in the exercise. -/
theorem exists_twoQubitCircuit_eq_fredkinGate_five :
    ∃ gs : List TwoQubitGate3,
      twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs = 5 :=
  ⟨fredkinFiveGates, twoQubitCircuit_fredkinFiveGates, twoQubitCount_fredkinFiveGates⟩

end AxQM
