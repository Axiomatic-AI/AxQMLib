/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCatVerification
import AxQM.Postulates.API.ShorStabilizer
import AxQM.Postulates.API.CatVerification
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Concrete.NegOnePowFinTwo

/-!
# Nielsen & Chuang, Exercise 10.69 (a single fault gives at most one bit-flip error)

*(N&C §10.6.3, p. 491.)*

Show a single failure in ancilla prep/verification causes at most one X or Y error in the ancilla
output.

## Setting — the fault-tolerant cat-state measurement (N&C Figure 10.28)

To measure an encoded observable `M` fault-tolerantly, N&C use an **ancilla in a cat state**
`|00…0⟩ + |11…1⟩`, prepared by a (non-fault-tolerant) CNOT circuit and then **verified** by parity
checks `ZᵢZⱼ`; controlled-`M′` gates then couple the ancilla to the data, one ancilla qubit per data
qubit. Because the coupling is one-to-one, an `X` (or `Y`) *bit-flip* error on the ancilla output
propagates into a bit-flip error on the encoded data — so fault-tolerance requires that a single
component failure produce **at most one** such error. (Phase-`Z` errors are the subject of the
companion Exercise 10.70: they do not propagate to the data, only spoil the measurement outcome.)

Figure 10.28 draws the cat encoded in **three qubits** "for simplicity"; that is the model
formalised here, on the block register `bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` carrying the
`+`-signed cat ancilla `catBlockState 0 = (|000⟩ + |111⟩)/√2` (the shared Shor-code cat block,
`Postulates/API/ShorCodeBlock.lean`).

## The mechanism, and how it is formalised

A single fault has to survive *two* stages before it can reach the data as a bit-flip error:

1. **Preparation (propagation).** The cat is built by a chain of CNOTs (`H` on the first qubit, then
   copy it along the register). Each CNOT copies an `X` on its control onto its target, so a single
   `X` fault *fans out* over a set of qubits: the residue that reaches the ancilla output is some
   **bit-flip pattern** `p : Fin 3 → Fin 2` (`p i = 1` flips qubit `i`), realised by the gate
   `blockBitFlipPattern p`. (The fan-out is the standard control→target `X`-propagation identity
   `cnotGate_pauliXGate_control_propagates`, N&C eq. 4.32; the pattern is its residue.)

2. **Verification (detection).** N&C then *verify* the cat by measuring the adjacent parities
   `Z₁Z₂ = zzIObservable` and `Z₂Z₃ = izzObservable` (`Postulates/API/BitFlipSyndromeMeasurement`):
   a genuine cat has even parity across every pair, so a `−1` outcome flags an error and the ancilla
   is discarded. This is the fault-tolerance workhorse, and the content newly formalised here.

**Status — the complete formalisation.** This file assembles the exercise's stated conclusion,
`catAncilla_single_fault_at_most_one_error`: *a single failure anywhere in the ancilla preparation
and verification leaves at most one `X` or `Y` error in the accepted ancilla output*, quantified —
via a `Sum` over the two fault locations N&C name — over a fault *anywhere in preparation or
verification* (see "The assembled count bound" at the foot of the file). It rests on the two
*mechanisms*, each formalised as its own per-location count bound: (i) the **preparation-side
detection** — a preparation fault fans out to a bit-flip pattern that verification catches unless it
is harmless — **at general qubit count** (`catState_bitFlip_accepted_at_most_one_error`; see
"General-`n` verification" below) and, as the concrete Figure 10.28 instance, on three qubits; and
(ii) the **verification-side fault model** — a single fault at *any* time-slice of the `ZᵢZⱼ`
verification gadget (including a faulty `CNOT`) leaves at most one `X` on the ancilla output
(`catVerifyGate_anywhere_fault_ancilla_weight_le_one`, ranging over `CatVerifyFaultSlice`; see "A
single fault at any gadget time-slice" below). The three-qubit detection theorems here
formalise:

* **`catBlockState_zero_hasEigenstate_zzIObservable` / `_izzObservable`** — the ideal cat *passes*
  verification: `catBlockState 0` is a `+1` eigenstate of both parity checks (the `σ = 0` instances
  of the general `zzIObservable_hasEigenstate_one_catBlockState` / `izz…` in
  `Postulates/API/ShorStabilizer`).
* **`blockBitFlipPattern_evolvePure_catBlockState_hasEigenstate_zzI` / `_izz`** — the **syndrome of
  a patterned error**: the errored cat is an eigenstate of `Z₁Z₂` with eigenvalue `(−1)^{p₀+p₁}` and
  of `Z₂Z₃` with eigenvalue `(−1)^{p₁+p₂}`. The `+1` (accept) outcome occurs iff `p₀ = p₁` (resp.
  `p₁ = p₂`).
* **`blockBitFlipPattern_caught_or_trivial`** — the **detection dichotomy**: for **every** bit-flip
  residue `p`, either the errored cat is **rejected by verification** (a `−1` eigenstate of `Z₁Z₂`
  or `Z₂Z₃`), or `p` is *constant* and the error acts trivially on the cat. This is the detection
  mechanism the fault-tolerance argument turns on; its general-`n` form
  `catState_bitFlip_accepted_at_most_one_error` supplies the preparation branch of the assembled
  count bound.

The `+`-cat's symmetry `X⊗X⊗X = 1` still underlies the trivial branch and is recorded on its own:

* **`blockXGate_fixes_catBlockState`** — a bit flip on *all three* qubits is not an error:
  `(X⊗X⊗X)|cat⟩ = |cat⟩`.
* **`blockBitFlip_double_collapses_to_single`** — the concrete weight-2 case: `Xᵢ Xⱼ |cat⟩ =
  X_k |cat⟩`.
* **`bitFlipError_collapses_to_at_most_one`** — on three qubits the symmetry alone already forces
  every pattern into a weight-`≤ 1` class; a supporting fact, subsumed by the verification dichotomy
  above (which is what makes the argument work for a larger code).

## Design notes

* **What "`X` or `Y`" means.** A `Y` error is a bit flip *and* a phase (`Y = iXZ`); its bit-flip
  part is exactly an `X`, so the analysis of `X` errors governs `X` and `Y` alike. The extra `Z`
  phase a `Y` carries is a harmless sign on the cat (`blockPhaseFlip_evolvePure_catBlockState`,
  Exercise 10.6) and is precisely what does *not* propagate to the data (Exercise 10.70). The bound
  is tight — a single `X`/`Y` genuinely occurs
  (`catBlockState_inner_blockSinglePauli_self_eq_zero`), so "at most one" cannot be strengthened to
  "none".

* **Why the assembly quantifies over two locations, and why general `n` matters.** The `ZᵢZⱼ`
  verification is the true fault-tolerance workhorse: for the seven-qubit Steane cat a single
  preparation fault can fan out to a weight-3 residue that the `X⊗X⊗X` symmetry does *not* collapse,
  and it is verification — not the symmetry — that rejects it. **On the three-qubit figure alone the
  detection dichotomy coincides with the symmetry bound** — "accepted ⟺ constant ⟹ zero residual"
  is exactly what the `X⊗X⊗X` symmetry already gives — so `n = 3` does not by itself *exhibit* the
  fidelity improvement; that requires the register where the two diverge. The preparation branch of
  the assembled bound is therefore stated **at general qubit count** (the "General-`n` verification"
  section below, built on `Postulates/API/CatVerification`): for an arbitrary index type `ι`, every
  non-constant bit-flip residue is caught by a parity check `ZᵢZⱼ`
  (`catState_bitFlip_caught_or_trivial`, in count form
  `catState_bitFlip_accepted_at_most_one_error`) — now genuinely the verification doing what the
  symmetry cannot. The **verification** branch is the atomic `ZᵢZⱼ` gadget `catVerifyGate` (two
  `CNOT`s from the ancilla controls into a fresh extra qubit), with the fault quantified over
  *every* gadget time-slice `CatVerifyFaultSlice` (input / between / output) and an arbitrary
  ancilla-weight-`≤ 1` residue: `catVerifyGate_anywhere_fault_ancilla_weight_le_one` proves a fault
  anywhere in the gadget — including a faulty `CNOT`'s two-qubit residue — leaves at most one `X` on
  the ancilla, because no ancilla qubit is a `CNOT` target (see the "single fault at any gadget
  time-slice" section).

  The two branches act on *different registers* — a preparation fault fans out across the whole
  `n`-qubit cat ancilla, whereas a verification fault is localised to one `ZᵢZⱼ` gadget's two
  ancilla qubits plus its fresh syndrome qubit — which is exactly why the exercise's "a single
  failure *anywhere*" is rendered as a `Sum` over the two locations
  (`catAncilla_single_fault_at_most_one_error`) rather than a single register model. The CNOT-chain
  preparation fan-out is invoked via the eq. 4.32 propagation identity rather than modelled as a
  full spacetime circuit; the residue is taken as an arbitrary pattern (a single fault fans out to
  *some* pattern, and the bound holds for every pattern).

* **Statements.** The headlines are stated for the unitary `Evolution`s `blockBitFlipPattern` /
  `blockXGate`, the parity `Observable`s `zzIObservable` / `izzObservable`, and
  `Evolution.evolvePure`, `Observable.HasEigenstate` applied to the cat state `catBlockState`.
  The operator identities on the raw cat vectors are in
  `AxQM/Postulates/API/ShorCatVerification.lean` (parity syndromes) and
  `AxQM/Postulates/API/ShorCodeBitFlip.lean` (bit-flip gates).
-/

noncomputable section

namespace AxQM

/-! ### The `X⊗X⊗X` symmetry of the cat ancilla -/

/-- **A bit flip on all three qubits is not an error.** The all-qubit bit-flip gate `X ⊗ X ⊗ X`
fixes the `+`-signed cat ancilla `catBlockState 0 = (|000⟩ + |111⟩)/√2`: `(X⊗X⊗X)|cat⟩ = |cat⟩`.
This is the cat's bit-flip symmetry `X⊗X⊗X = 1`; three simultaneous `X` errors collapse to no error
at all. Lifted from the operator identity `blockXGate_op_catBlockVec` (eigenvalue `(−1)^0 = 1`) via
the unitary-normalisation bridge `Evolution.evolvePure_normalize_of_op_eq`. -/
theorem blockXGate_fixes_catBlockState :
    blockXGate.evolvePure (catBlockState 0) = catBlockState 0 :=
  blockXGate.evolvePure_normalize_of_op_eq (catBlockVec_ne_zero 0) (catBlockVec_ne_zero 0)
    (by simpa using blockXGate_op_catBlockVec 0)

/-- **Two bit-flip errors collapse to one.** On the cat ancilla `catBlockState 0`, a bit flip on two
*distinct* qubits `i ≠ j` acts exactly as a single bit flip on the remaining qubit `thirdQubit i j`:
`Xᵢ (Xⱼ |cat⟩) = X_{thirdQubit i j} |cat⟩`. The concrete weight-2 instance of the collapse: two `X`
errors are indistinguishable from one. The `X⊗X⊗X = 1` symmetry (`blockXGate_fixes_catBlockState`)
read as `Xᵢ Xⱼ = X_k` on the cat; proved at the state level from the operator collapse
`blockBitFlip_op_op_catBlockVec_zero` through `Evolution.evolvePure_vec` and
`PureState.normalize_vec`. -/
theorem blockBitFlip_double_collapses_to_single (i j : Fin 3) (h : i ≠ j) :
    (blockBitFlip i).evolvePure ((blockBitFlip j).evolvePure (catBlockState 0))
      = (blockBitFlip (thirdQubit i j)).evolvePure (catBlockState 0) := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, catBlockState, PureState.normalize_vec, map_smul]
  congr 1
  exact blockBitFlip_op_op_catBlockVec_zero i j h

/-- **A bit-flip pattern and its complement act identically on the cat ancilla.** Flipping the
pattern `p` and flipping its bitwise complement `p + 1` (all three bits toggled) send
`catBlockState 0` to the *same* state, because they differ by `blockXGate = X⊗X⊗X`, which fixes the
`+` cat (`blockXGate_fixes_catBlockState`). Immediate from `blockBitFlipPattern_add_one`
(`blockBitFlipPattern (p+1) = blockBitFlipPattern p · blockXGate`) through
`Evolution.evolvePure_comp`. -/
theorem blockBitFlipPattern_add_one_evolvePure_catBlockState (p : Fin 3 → Fin 2) :
    (blockBitFlipPattern (fun i => p i + 1)).evolvePure (catBlockState 0)
      = (blockBitFlipPattern p).evolvePure (catBlockState 0) := by
  rw [blockBitFlipPattern_add_one, Evolution.evolvePure_comp, blockXGate_fixes_catBlockState]

/-! ### Verification accepts the ideal cat ancilla -/

/-- **The ideal cat ancilla passes the `Z₁Z₂` verification check:** `catBlockState 0` is a `+1`
eigenstate of `zzIObservable = Z₁Z₂`. Measuring the first parity of the genuine cat yields `+1`
(even parity) with certainty — the ancilla is accepted. The `σ = 0` instance of the general
stabilizer fact `zzIObservable_hasEigenstate_one_catBlockState` (in `ShorStabilizer`). -/
theorem catBlockState_zero_hasEigenstate_zzIObservable :
    zzIObservable.HasEigenstate 1 (catBlockState 0) :=
  zzIObservable_hasEigenstate_one_catBlockState 0

/-- **The ideal cat ancilla passes the `Z₂Z₃` verification check:** `catBlockState 0` is a `+1`
eigenstate of `izzObservable = Z₂Z₃`. The `σ = 0` instance of
`izzObservable_hasEigenstate_one_catBlockState`. -/
theorem catBlockState_zero_hasEigenstate_izzObservable :
    izzObservable.HasEigenstate 1 (catBlockState 0) :=
  izzObservable_hasEigenstate_one_catBlockState 0

/-! ### The parity syndrome of a patterned bit-flip error -/

/-- **The `Z₁Z₂` syndrome of a bit-flip residue.** For every bit-flip pattern `p : Fin 3 → Fin 2`,
the errored cat `blockBitFlipPattern p |cat⟩` is an eigenstate of the parity check `Z₁Z₂` with
eigenvalue `(−1)^{p₀+p₁}`: measuring `Z₁Z₂` gives `+1` (accept) iff `p₀ = p₁`, and `−1` (reject) iff
`p₀ ≠ p₁`. Transported from the syndrome identity for vectors,
`zzIObservable_op_blockBitFlipPattern_catBlockVec` through `Observable.hasEigenstate_of_smul`. -/
theorem blockBitFlipPattern_evolvePure_catBlockState_hasEigenstate_zzI (p : Fin 3 → Fin 2) :
    zzIObservable.HasEigenstate ((-1 : ℝ) ^ ((p 0 : ℕ) + (p 1 : ℕ)))
      ((blockBitFlipPattern p).evolvePure (catBlockState 0)) := by
  refine Observable.hasEigenstate_of_smul (c := ((‖catBlockVec 0‖ : ℝ) : ℂ)⁻¹)
    (v := (blockBitFlipPattern p).op (catBlockVec 0)) ?_ ?_
  · rw [Evolution.evolvePure_vec, catBlockState, PureState.normalize_vec, map_smul]
  · rw [zzIObservable_op_blockBitFlipPattern_catBlockVec]
    congr 1
    rw [pow_add]
    push_cast
    ring

/-- **The `Z₂Z₃` syndrome of a bit-flip residue.** The errored cat is an eigenstate of `Z₂Z₃` with
eigenvalue `(−1)^{p₁+p₂}`; `+1` (accept) iff `p₁ = p₂`. The `Z₂Z₃` analogue of
`blockBitFlipPattern_evolvePure_catBlockState_hasEigenstate_zzI`. -/
theorem blockBitFlipPattern_evolvePure_catBlockState_hasEigenstate_izz (p : Fin 3 → Fin 2) :
    izzObservable.HasEigenstate ((-1 : ℝ) ^ ((p 1 : ℕ) + (p 2 : ℕ)))
      ((blockBitFlipPattern p).evolvePure (catBlockState 0)) := by
  refine Observable.hasEigenstate_of_smul (c := ((‖catBlockVec 0‖ : ℝ) : ℂ)⁻¹)
    (v := (blockBitFlipPattern p).op (catBlockVec 0)) ?_ ?_
  · rw [Evolution.evolvePure_vec, catBlockState, PureState.normalize_vec, map_smul]
  · rw [izzObservable_op_blockBitFlipPattern_catBlockVec]
    congr 1
    rw [pow_add]
    push_cast
    ring

/-! ### Constant patterns act trivially on the cat -/

/-- **A constant bit-flip pattern acts trivially on the cat ancilla.** For `a : Fin 2` the pattern
that flips every qubit the same amount, `blockBitFlipPattern (fun _ => a)`, fixes `catBlockState 0`:
`a = 0` is the identity, and `a = 1` is `X⊗X⊗X = blockXGate`, the cat's symmetry
(`blockXGate_fixes_catBlockState`). These are the only bit-flip residues that survive verification,
and they are exactly the ones that leave the ancilla error-free. -/
theorem blockBitFlipPattern_const_evolvePure_catBlockState (a : Fin 2) :
    (blockBitFlipPattern (fun _ => a)).evolvePure (catBlockState 0) = catBlockState 0 := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
  · apply PureState.ext
    simp [Evolution.evolvePure_vec, catBlockState, PureState.normalize_vec, catBlockVec,
      blockBitFlipPattern_op_qubitThreeBasis]
  · exact blockXGate_fixes_catBlockState

/-! ### The detection dichotomy — a residue is caught by verification or is harmless -/

/-- **The verification detection dichotomy** (the detection half of Exercise 10.69). For **every**
bit-flip residue `p : Fin 3 → Fin 2` a single preparation fault can leave on the cat ancilla, one of
two things happens:

* the errored cat `blockBitFlipPattern p |cat⟩` is **rejected by verification** — it is a `−1`
  eigenstate of a parity check (`Z₁Z₂` when `p₀ ≠ p₁`, `Z₂Z₃` when `p₁ ≠ p₂`), so the `ZᵢZⱼ`
  measurement discards it; or
* `p` is **constant** and the error **acts trivially** on the cat
  (`blockBitFlipPattern p |cat⟩ = catBlockState 0`).

So no propagated fault can leave the *accepted* ancilla in a multi-qubit bit-flip state: whatever
survives verification is error-free. To reach the exercise's full "at most one `X`/`Y` error" bound
one still needs the verification-stage fault (the location where the single surviving error
originates) and the general-`n` register (on `n = 3` this dichotomy coincides with the `X⊗X⊗X`
symmetry bound `bitFlipError_collapses_to_at_most_one`); those are supplied further below (see the
module docstring). The proof splits on whether `p₀ = p₁` and `p₁ = p₂`: a mismatch
gives eigenvalue `(−1)^{odd} = −1` on the corresponding check
(`blockBitFlipPattern_evolvePure_catBlockState_hasEigenstate_zzI` / `_izz`), and `p₀ = p₁ = p₂` is a
constant pattern (`blockBitFlipPattern_const_evolvePure_catBlockState`). -/
theorem blockBitFlipPattern_caught_or_trivial (p : Fin 3 → Fin 2) :
    zzIObservable.HasEigenstate (-1) ((blockBitFlipPattern p).evolvePure (catBlockState 0))
      ∨ izzObservable.HasEigenstate (-1) ((blockBitFlipPattern p).evolvePure (catBlockState 0))
      ∨ (blockBitFlipPattern p).evolvePure (catBlockState 0) = catBlockState 0 := by
  by_cases h01 : p 0 = p 1
  · by_cases h12 : p 1 = p 2
    · refine Or.inr (Or.inr ?_)
      obtain ⟨v, hv⟩ : ∃ v, p = fun _ => v := by
        refine ⟨p 0, ?_⟩
        funext i
        fin_cases i
        · rfl
        · exact h01.symm
        · exact h12.symm.trans h01.symm
      rw [hv]
      exact blockBitFlipPattern_const_evolvePure_catBlockState v
    · refine Or.inr (Or.inl ?_)
      rw [← Concrete.neg_one_pow_add_fin_two_of_ne h12]
      exact blockBitFlipPattern_evolvePure_catBlockState_hasEigenstate_izz p
  · refine Or.inl ?_
    rw [← Concrete.neg_one_pow_add_fin_two_of_ne h01]
    exact blockBitFlipPattern_evolvePure_catBlockState_hasEigenstate_zzI p

/-! ### The symmetry bound (three-qubit register) -/

/-- **On three qubits the `X⊗X⊗X` symmetry already collapses every pattern to weight `≤ 1`.** For
every bit-flip pattern `p`, its action on the cat equals that of some pattern `q` of weight `≤ 1`
(`∑ i, q i ≤ 1`). A supporting fact special to the figure's three-qubit register — for a larger code
it is the verification dichotomy `blockBitFlipPattern_caught_or_trivial`, not this symmetry, that
does the work. Proof: if `p` already has weight `≤ 1`, take `q = p`; otherwise take the complement
`q = p + 1`, which has weight `3 − |p| ≤ 1` and acts identically on the cat
(`blockBitFlipPattern_add_one_evolvePure_catBlockState`). -/
theorem bitFlipError_collapses_to_at_most_one (p : Fin 3 → Fin 2) :
    ∃ q : Fin 3 → Fin 2, (∑ i, (q i : ℕ)) ≤ 1 ∧
      (blockBitFlipPattern p).evolvePure (catBlockState 0)
        = (blockBitFlipPattern q).evolvePure (catBlockState 0) := by
  by_cases hp : (∑ i, (p i : ℕ)) ≤ 1
  · exact ⟨p, hp, rfl⟩
  · refine ⟨fun i => p i + 1, ?_, (blockBitFlipPattern_add_one_evolvePure_catBlockState p).symm⟩
    change (∑ i : Fin 3, ((p i + 1 : Fin 2) : ℕ)) ≤ 1
    have key : ∀ x : Fin 2, (x : ℕ) + ((x + 1 : Fin 2) : ℕ) = 1 := by decide
    have hsum : (∑ i : Fin 3, (p i : ℕ)) + (∑ i : Fin 3, ((p i + 1 : Fin 2) : ℕ)) = 3 := by
      rw [← Finset.sum_add_distrib]
      simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega

/-! ### General-`n` verification (the mechanism, not the `n = 3` coincidence)

On the three-qubit figure the detection dichotomy above coincides with the `X⊗X⊗X` symmetry bound.
To see that it is *verification* — not the symmetry — that does the fault-tolerance work, we
formalise the same detection at **general qubit count**: an arbitrary index type `ι` (the register
`bitReg ι`), the cat ancilla `catState ι = (|0…0⟩ + |1…1⟩)/√2`, and the two-qubit parity checks
`zPairObservable i j = ZᵢZⱼ` (`Postulates/API/CatVerification`). Already on four qubits there are
residues (e.g. `1100`, complement `0011`, both weight `2`) that `X^{⊗n}` symmetry cannot collapse to
weight `≤ 1` but a parity check still catches, so
here the dichotomy genuinely says more than the symmetry. -/

section GeneralN

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The ideal `n`-qubit cat ancilla passes every verification check:** `catState ι` is a `+1`
eigenstate of every two-qubit parity `ZᵢZⱼ`. Every pair of qubits in the genuine cat has even
parity, so verification accepts it. The statement for states of the vector identity
`zPairObservable_op_catVec`. -/
theorem catState_hasEigenstate_zPairObservable (i j : ι) :
    (zPairObservable i j).HasEigenstate 1 (catState ι) := by
  refine Observable.hasEigenstate_of_smul (c := ((‖catVec ι‖ : ℝ) : ℂ)⁻¹) (v := catVec ι) ?_ ?_
  · simp only [catState, PureState.normalize_vec]
  · rw [zPairObservable_op_catVec, Complex.ofReal_one, one_smul]

/-- **The parity syndrome of a patterned bit-flip error, at general `n`.** For every bit-flip
residue `p : ι → ZMod 2`, the errored cat `X^{p} |cat⟩` is an eigenstate of the parity check `ZᵢZⱼ`
with eigenvalue `(−1)^{pᵢ + pⱼ}`: measuring `ZᵢZⱼ` gives `+1` (accept) iff `pᵢ = pⱼ`, and `−1`
(reject) iff `pᵢ ≠ pⱼ`. Transported from the vector identity
`zPairObservable_op_bitString_op_catVec` through `Observable.hasEigenstate_of_smul`. -/
theorem catState_bitFlip_hasEigenstate_zPairObservable (i j : ι) (p : ι → ZMod 2) :
    (zPairObservable i j).HasEigenstate ((-1 : ℝ) ^ (p i + p j : ZMod 2).val)
      ((bitString p).evolvePure (catState ι)) := by
  refine Observable.hasEigenstate_of_smul (c := ((‖catVec ι‖ : ℝ) : ℂ)⁻¹)
    (v := (bitString p).op (catVec ι)) ?_ ?_
  · rw [Evolution.evolvePure_vec]
    simp only [catState, PureState.normalize_vec, map_smul]
  · rw [zPairObservable_op_bitString_op_catVec, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one]

/-- **A bit flip on all `n` qubits is not an error:** `X^{⊗n} |cat⟩ = |cat⟩`. Flipping every qubit
swaps the two corners `|0…0⟩ ↔ |1…1⟩`, so it fixes the `+` cat — the cat's bit-flip symmetry
`X^{⊗n} = 1`, the `n`-qubit analogue of `blockXGate_fixes_catBlockState`. -/
theorem bitString_one_evolvePure_catState :
    (bitString (1 : ι → ZMod 2)).evolvePure (catState ι) = catState ι := by
  rw [catState]
  exact (bitString (1 : ι → ZMod 2)).evolvePure_normalize_of_op_eq catVec_ne_zero catVec_ne_zero
    bitString_one_op_catVec

/-- **A constant bit-flip pattern acts trivially on the cat ancilla.** For `a : ZMod 2` the pattern
flipping every qubit the same amount, `bitString (fun _ => a)`, fixes `catState ι`: `a = 0` is the
identity, `a = 1` is `X^{⊗n}` (`bitString_one_evolvePure_catState`). These constant residues are the
only bit-flip errors that survive verification, and they leave the ancilla error-free. -/
theorem bitString_const_evolvePure_catState (a : ZMod 2) :
    (bitString (fun _ : ι => a)).evolvePure (catState ι) = catState ι := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with rfl | rfl
  · rw [catState]
    exact (bitString (0 : ι → ZMod 2)).evolvePure_normalize_of_op_eq catVec_ne_zero catVec_ne_zero
      bitString_zero_op_catVec
  · exact bitString_one_evolvePure_catState

/-- **The verification detection dichotomy, at general `n`** (the detection half of Exercise 10.69,
now with verification genuinely doing the work). For **every** bit-flip residue `p : ι → ZMod 2` a
single preparation fault can leave on the `n`-qubit cat ancilla, one of two things happens:

* the errored cat `X^{p} |cat⟩` is **rejected by verification** — it is a `−1` eigenstate of some
  parity check `ZᵢZⱼ` (whenever `pᵢ ≠ pⱼ`), so the `ZᵢZⱼ` measurement discards it; or
* `p` is **constant** and the error **acts trivially** on the cat
  (`(bitString p).evolvePure (catState ι) = catState ι`).

So no propagated fault can leave the *accepted* ancilla in a multi-qubit bit-flip state: whatever
survives verification is error-free. Unlike the three-qubit `blockBitFlipPattern_caught_or_trivial`,
here (already at four qubits) the caught branch removes residues the `X^{⊗n}` symmetry cannot — this
is the verification mechanism, not the symmetry. The proof splits on whether `p` is constant: a
mismatch
`pᵢ ≠ pⱼ` gives eigenvalue `(−1)^{1} = −1` on `ZᵢZⱼ`
(`catState_bitFlip_hasEigenstate_zPairObservable`), and a constant `p` acts trivially
(`bitString_const_evolvePure_catState`). Assembling this with the verification-stage fault location
and the "at most one `X`/`Y`" count is the remaining work (see the module design note). -/
theorem catState_bitFlip_caught_or_trivial (p : ι → ZMod 2) :
    (∃ i j, (zPairObservable i j).HasEigenstate (-1) ((bitString p).evolvePure (catState ι)))
      ∨ (bitString p).evolvePure (catState ι) = catState ι := by
  by_cases hconst : ∀ i j, p i = p j
  · refine Or.inr ?_
    have hp : p = fun _ => p (Classical.arbitrary ι) := by
      funext k; exact hconst k (Classical.arbitrary ι)
    rw [hp]
    exact bitString_const_evolvePure_catState _
  · refine Or.inl ?_
    simp only [not_forall] at hconst
    obtain ⟨i, j, hij⟩ := hconst
    refine ⟨i, j, ?_⟩
    have hval : (p i + p j : ZMod 2).val = 1 := by
      have hpair : ∀ a b : ZMod 2, a ≠ b → (a + b).val = 1 := by decide
      exact hpair (p i) (p j) hij
    have h := catState_bitFlip_hasEigenstate_zPairObservable i j p
    rwa [hval, pow_one] at h

/-- **Preparation-side count bound (general `n`): a preparation fault leaves at most one `X`/`Y`
error in the *accepted* ancilla output.** For every bit-flip residue `p : ι → ZMod 2` a single
preparation fault can fan out to, one of two things happens: either verification **rejects** the
ancilla (`X^{p}|cat⟩` is a `−1` eigenstate of some parity check `ZᵢZⱼ`, so the measurement discards
it), or the accepted output is `X^{r}|cat⟩` for a residue `r` flipping **at most one** ancilla qubit
(`∑ i, (r i).val ≤ 1`) — in fact the *zero* residue, so an accepted preparation fault leaves the cat
error-free. This is the exercise's "at most one `X`/`Y` error" bound for a fault located in
*preparation*, recast into the same weight-`≤ 1` count form as the verification-stage bound
`catVerifyGate_single_fault_ancilla_weight_le_one`, so the two fault locations deliver a uniform
conclusion. Immediate from the detection dichotomy `catState_bitFlip_caught_or_trivial`: a caught
residue is the reject branch; a trivial (constant) residue acts as the identity, i.e. equals
`X^{0}|cat⟩` (`bitString_const_evolvePure_catState`), a residue of weight `0`. -/
theorem catState_bitFlip_accepted_at_most_one_error (p : ι → ZMod 2) :
    (∃ i j, (zPairObservable i j).HasEigenstate (-1) ((bitString p).evolvePure (catState ι)))
      ∨ (∃ r : ι → ZMod 2, (∑ i, (r i).val) ≤ 1 ∧
          (bitString p).evolvePure (catState ι) = (bitString r).evolvePure (catState ι)) := by
  rcases catState_bitFlip_caught_or_trivial p with hcaught | htriv
  · exact Or.inl hcaught
  · refine Or.inr ⟨fun _ => 0, by simp, ?_⟩
    rw [htriv]
    exact (bitString_const_evolvePure_catState 0).symm

end GeneralN

/-! ### The verification-stage single-fault model (Figure 10.28's `ZᵢZⱼ` parity gadget)

The detection dichotomy above governs a fault during **preparation**: it fans out to a bit-flip
pattern that verification then catches (or which is harmless). Exercise 10.69 also demands the other
fault location — a fault during the **verification** step itself. N&C verify a parity `ZᵢZⱼ`
(Figure 10.28 draws `Z₂Z₃`) by introducing a fresh `|0⟩` *extra* qubit and applying **two `CNOT`s**,
the two ancilla qubits as **controls** and the extra qubit as the shared **target**, before
measuring the extra qubit. We model this atomic gadget on `bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`
with **qubits `0, 1` the two ancilla qubits under test and qubit `2` the extra (syndrome) qubit**:

`catVerifyGate = CNOT₁₂ ∘ CNOT₀₂` (both `CNOT`s target qubit `2`), which computes the parity
`q₀ + q₁` of the two ancilla qubits onto the extra qubit (`catVerifyGate_computes_parity`).

The verification half of the exercise turns on a structural fact: **no ancilla qubit is ever a
`CNOT` target**. So a single `X` fault never fans *into* the ancilla — an `X` on an ancilla control
copies only onto the (discarded) extra qubit, and an `X` on the extra target does not propagate back
to the ancilla at all. Hence verification **never increases the ancilla's bit-flip weight**:

* **`catVerifyGate_comp_blockBitFlipPattern`** — the input-fault propagation identity, for *every*
  bit-flip residue `p`: `catVerifyGate · X^{p} = X^{(p₀, p₁, p₂ + p₀ + p₁)} · catVerifyGate`. The
  residue's **ancilla part `(p₀, p₁)` is unchanged** — only the extra qubit `q₂` accumulates the
  copies `p₀ + p₁`.
* **`cnotVerifyStep_comp_blockBitFlipPattern`** — the same for the trailing single check `CNOT₁₂`
  (residue `(p₀, p₁, p₂ + p₁)`), the fault position *between* the two `CNOT`s.
* **`catVerifyGate_single_fault_ancilla_weight_le_one`** — a single `X` fault `blockBitFlip f` on
  any qubit `f` at the gadget *input* propagates to a residue whose weight on the ancilla qubits
  `{0, 1}` is `≤ 1` (the extra qubit `q₂` may carry an extra `X`, but it is measured and discarded).

**Fault position ("anywhere") — formalised.** A single fault sits at one of the gadget's time
slices — before `CNOT₀₂` (input), between the two `CNOT`s, or after `CNOT₁₂` (output) — and
propagates through the gates that *follow* it. This is captured as the enumeration
`CatVerifyFaultSlice` together with `catVerifyFaultCircuit` (the gadget with a residue `X^{e}`
injected at a chosen slice), and the "anywhere" bound
`catVerifyGate_anywhere_fault_ancilla_weight_le_one`: for a residue `e` at *any* slice whose ancilla
weight is `≤ 1`, the propagated output residue has ancilla weight `≤ 1`. A fault after `CNOT₁₂` is
the residue itself; one between the two `CNOT`s propagates through `CNOT₁₂` only
(`cnotVerifyStep_comp_blockBitFlipPattern`); one at the input propagates through both
(`catVerifyGate_comp_blockBitFlipPattern`) — in every case the ancilla weight is preserved
(propagation only adds `X`s onto the extra qubit). A **faulty `CNOT`** (the perfect gate followed by
a two-qubit Pauli on its control/target, as N&C model gate failures) injects a *two*-qubit residue
at that gate's output slice touching only its one ancilla control, hence still ancilla weight `≤ 1`:
`catVerifyGate_faulty_cnotFirst_ancilla_weight_le_one` (`CNOT₀₂`, `between`) and
`catVerifyGate_faulty_cnotSecond_ancilla_weight_le_one` (`CNOT₁₂`, `output`). (`Y = iXZ` shares its
bit-flip part with `X`, and the extra `Z` phase is a harmless cat sign, so the count governs `X` and
`Y` alike; see the "What `X` or `Y` means" design note.)
-/

/-- **The verification gadget for one parity check `ZᵢZⱼ`** (Figure 10.28's `Z₂Z₃` step), on
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` with qubits `0, 1` the two ancilla qubits under test and
qubit `2` the fresh extra (syndrome) qubit: two `CNOT`s from the ancilla qubits (controls) into the
extra qubit (shared target), `catVerifyGate = CNOT₁₂ ∘ CNOT₀₂`. On the `|0⟩`-initialised extra
qubit it deposits the parity `q₀ + q₁` there (`catVerifyGate_computes_parity`); reading the extra
qubit is the verification measurement. Its defining structural property — no ancilla qubit is a
`CNOT` target — is what bounds the ancilla error to weight `≤ 1` under a single fault. -/
def catVerifyGate : Evolution bitFlipReg :=
  (cnotGate.onRight qubit).comp cnotFirstThirdGate

/-- **The action of the verification gadget on a computational basis ket:**
`catVerifyGate |q₀ q₁ q₂⟩ = |q₀, q₁, q₂ + q₀ + q₁⟩`. `CNOT₀₂` XORs `q₀` onto the extra qubit, then
`CNOT₁₂` XORs `q₁` — leaving the two ancilla qubits fixed and the extra qubit holding the running
parity. From the factored `CNOT` actions (`cnotFirstThirdGate_evolvePure`,
`cnotSecondThirdGate_evolvePure`). -/
theorem catVerifyGate_evolvePure_tmul (q0 q1 q2 : Fin 2) :
    catVerifyGate.evolvePure (qubitBasis q0 ⊗ (qubitBasis q1 ⊗ qubitBasis q2))
      = qubitBasis q0 ⊗ (qubitBasis q1 ⊗ qubitBasis (q2 + q0 + q1)) := by
  rw [catVerifyGate, Evolution.evolvePure_comp, cnotFirstThirdGate_evolvePure,
    targetXPow_evolvePure_qubitBasis, cnotSecondThirdGate_evolvePure,
    targetXPow_evolvePure_qubitBasis]

/-- **The verification gadget computes the parity onto the extra qubit:**
`catVerifyGate |q₀ q₁ 0⟩ = |q₀, q₁, q₀ + q₁⟩`. This is why the gadget verifies `Z₀Z₁`: measuring the
extra qubit returns the parity `q₀ + q₁` of the two ancilla qubits (even ⇒ accept). The `q₂ = 0`
instance of `catVerifyGate_evolvePure_tmul`. -/
theorem catVerifyGate_computes_parity (q0 q1 : Fin 2) :
    catVerifyGate.evolvePure (qubitBasis q0 ⊗ (qubitBasis q1 ⊗ qubitBasis 0))
      = qubitBasis q0 ⊗ (qubitBasis q1 ⊗ qubitBasis (q0 + q1)) := by
  rw [catVerifyGate_evolvePure_tmul, zero_add]

/-- **Verification propagates an input bit-flip fault to a residue with the *same* ancilla weight.**
For every bit-flip residue `p : Fin 3 → Fin 2` an input fault leaves,
`catVerifyGate · X^{p} = X^{(p₀, p₁, p₂ + p₀ + p₁)} · catVerifyGate`: pushing the fault past the
verification gadget copies the ancilla flips `p₀, p₁` onto the extra qubit `q₂` (which becomes
`p₂ + p₀ + p₁`) but **leaves the ancilla bits `(p₀, p₁)` untouched**. So verification never turns a
weight-`k` ancilla fault into anything heavier on the ancilla — the reason a single `X` fault stays
a single `X` on the ancilla output. Proved on the computational basis (`threeQubit_evolution_ext`):
both sides send `|q₀ q₁ q₂⟩` to `|q₀+p₀, q₁+p₁, q₀+q₁+q₂+p₀+p₁+p₂⟩`. -/
theorem catVerifyGate_comp_blockBitFlipPattern (p : Fin 3 → Fin 2) :
    catVerifyGate.comp (blockBitFlipPattern p)
      = (blockBitFlipPattern ![p 0, p 1, p 2 + p 0 + p 1]).comp catVerifyGate := by
  apply threeQubit_evolution_ext
  intro q0 q1 q2
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp, blockBitFlipPattern_evolvePure_tmul,
    catVerifyGate_evolvePure_tmul, catVerifyGate_evolvePure_tmul,
    blockBitFlipPattern_evolvePure_tmul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  abel_nf

/-- **The trailing single check `CNOT₁₂` propagates a bit-flip fault to a residue with the same
ancilla weight** (the fault position *between* the two verification `CNOT`s):
`CNOT₁₂ · X^{p} = X^{(p₀, p₁, p₂ + p₁)} · CNOT₁₂`. Only the control bit `p₁` copies onto the extra
qubit `q₂`; the ancilla bits `(p₀, p₁)` are unchanged. Together with the full-gadget identity this
covers a single fault at any position in the gadget. -/
theorem cnotVerifyStep_comp_blockBitFlipPattern (p : Fin 3 → Fin 2) :
    (cnotGate.onRight qubit).comp (blockBitFlipPattern p)
      = (blockBitFlipPattern ![p 0, p 1, p 2 + p 1]).comp (cnotGate.onRight qubit) := by
  apply threeQubit_evolution_ext
  intro q0 q1 q2
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp, blockBitFlipPattern_evolvePure_tmul,
    cnotSecondThirdGate_evolvePure, targetXPow_evolvePure_qubitBasis,
    cnotSecondThirdGate_evolvePure, targetXPow_evolvePure_qubitBasis,
    blockBitFlipPattern_evolvePure_tmul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  abel_nf

/-- **A single `X` fault during verification leaves at most one `X` on the ancilla output** (the
verification half of Exercise 10.69). For a single-qubit bit-flip fault `blockBitFlip f` on **any**
qubit `f : Fin 3` of the verification gadget, the propagated residue `X^{r}` on the gadget's output
has weight **`≤ 1` on the ancilla qubits `{0, 1}`** (`(r 0 : ℕ) + r 1 ≤ 1`), and is `blockBitFlip f`
pushed past the gadget: `catVerifyGate · X^{f} = X^{r} · catVerifyGate`. Because no ancilla qubit is
a `CNOT` target, the fault's copies land only on the (discarded) extra qubit — a fault on an ancilla
qubit stays a single ancilla `X` (weight `1`), a fault on the extra qubit leaves the ancilla
error-free (weight `0`). This is the fault-tolerance property of the verification stage; assembling
it with the preparation-side detection dichotomy (`catState_bitFlip_caught_or_trivial`) into the
exercise's overall "at most one `X` or `Y`" count is done at the foot of the file. From
`blockBitFlip_eq_blockBitFlipPattern` and `catVerifyGate_comp_blockBitFlipPattern`, whose residue's
ancilla part `(eᶠ₀, eᶠ₁)` is the input's — of weight `≤ 1` since `eᶠ` flips one qubit. -/
theorem catVerifyGate_single_fault_ancilla_weight_le_one (f : Fin 3) :
    ∃ r : Fin 3 → Fin 2, (r 0 : ℕ) + (r 1 : ℕ) ≤ 1 ∧
      catVerifyGate.comp (blockBitFlip f)
        = (blockBitFlipPattern r).comp catVerifyGate := by
  rw [blockBitFlip_eq_blockBitFlipPattern]
  refine ⟨_, ?_, catVerifyGate_comp_blockBitFlipPattern _⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases f <;> simp

/-! ### A single fault at *any* gadget time-slice (N&C's "anywhere")

`catVerifyGate_single_fault_ancilla_weight_le_one` bounds a single-qubit fault at the gadget
*input*. Exercise 10.69 requires "a single failure **anywhere** … in the verification", and N&C
(p. 490) call out the fault *between* the two `CNOT`s as a physically distinct position. A single
fault strikes the gadget `catVerifyGate = CNOT₁₂ ∘ CNOT₀₂` at one of three time-slices — before
`CNOT₀₂` (`input`), between the two `CNOT`s (`between`), or after `CNOT₁₂` (`output`) — and
propagates only through the gates that *follow* it (`input` through both, `between` through
`CNOT₁₂`, `output` through none). We model the fault's bit-flip part as an arbitrary residue
`e : Fin 3 → Fin 2` subject to the **single-fault** constraint that it touches at most one *ancilla*
qubit,
`(e 0 : ℕ) + (e 1 : ℕ) ≤ 1`. That constraint is exactly what every single failure satisfies, because
no gate of the gadget has more than one ancilla qubit in its support: a single-qubit `X` fault has
total weight `≤ 1`; and a *faulty* `CNOT` (N&C model a gate failure as the ideal gate followed by a
Pauli on its two wires) acts on one ancilla control and the shared extra target, so its `X`-part
touches only the one ancilla control (weight `≤ 1` even though it is a *two*-qubit residue). Under
this constraint the output residue's ancilla weight is preserved at `e₀ + e₁ ≤ 1` from every slice —
verification never raises the ancilla bit-flip weight. -/

/-- **The three time-slices at which a single fault can strike the `ZᵢZⱼ` verification gadget**
`catVerifyGate = CNOT₁₂ ∘ CNOT₀₂`: before `CNOT₀₂`, between the two `CNOT`s, or after `CNOT₁₂`.
Together they exhaust "a single failure anywhere in the verification" (N&C §10.6.3, p. 490). -/
inductive CatVerifyFaultSlice
  /-- A fault before `CNOT₀₂` — the gadget input. -/
  | input
  /-- A fault between `CNOT₀₂` and `CNOT₁₂` (the position N&C single out on p. 490). -/
  | between
  /-- A fault after `CNOT₁₂` — the gadget output. -/
  | output

/-- **The verification gadget with a bit-flip fault `X^{e}` injected at time-slice `s`.** The
remaining gates act on the fault: `input` places it before the whole gadget
(`catVerifyGate ∘ X^{e}`), `between` between the two `CNOT`s (`CNOT₁₂ ∘ X^{e} ∘ CNOT₀₂`), and
`output` after the gadget (`X^{e} ∘ catVerifyGate`). -/
def catVerifyFaultCircuit : CatVerifyFaultSlice → (Fin 3 → Fin 2) → Evolution bitFlipReg
  | .input, e => catVerifyGate.comp (blockBitFlipPattern e)
  | .between, e => ((cnotGate.onRight qubit).comp (blockBitFlipPattern e)).comp cnotFirstThirdGate
  | .output, e => (blockBitFlipPattern e).comp catVerifyGate

/-- **A single fault anywhere in the verification gadget leaves at most one `X` on the ancilla
output** (the verification half of Exercise 10.69, now quantified over *every* time-slice). For a
bit-flip fault `X^{e}` injected at any slice `s`, whose `X`-part touches at most one ancilla qubit
(`(e 0 : ℕ) + (e 1 : ℕ) ≤ 1` — the defining property of a *single* failure; see the section note),
the faulty gadget equals `X^{r} ∘ catVerifyGate` for a residue `r` of ancilla weight `≤ 1`: pushing
the fault to the output only ever deposits copies onto the discarded extra qubit `q₂`, so the
ancilla weight is preserved. Each slice reduces to a propagation identity —
`catVerifyGate_comp_blockBitFlipPattern` (`input`), `cnotVerifyStep_comp_blockBitFlipPattern`
(`between`), the identity (`output`) — whose residue `r` has ancilla part `(e₀, e₁)`, hence
`r₀ + r₁ = e₀ + e₁ ≤ 1`. This covers every single fault: single-qubit `X` at any slice, and a faulty
`CNOT`'s two-qubit residue at that gate's output slice (`catVerifyGate_faulty_cnotFirst_…` /
`_cnotSecond_…`). -/
theorem catVerifyGate_anywhere_fault_ancilla_weight_le_one (s : CatVerifyFaultSlice)
    (e : Fin 3 → Fin 2) (he : (e 0 : ℕ) + (e 1 : ℕ) ≤ 1) :
    ∃ r : Fin 3 → Fin 2, (r 0 : ℕ) + (r 1 : ℕ) ≤ 1 ∧
      catVerifyFaultCircuit s e = (blockBitFlipPattern r).comp catVerifyGate := by
  cases s with
  | input =>
      refine ⟨![e 0, e 1, e 2 + e 0 + e 1], ?_, ?_⟩
      · simpa using he
      · exact catVerifyGate_comp_blockBitFlipPattern e
  | between =>
      refine ⟨![e 0, e 1, e 2 + e 1], by simpa using he, ?_⟩
      simp only [catVerifyFaultCircuit, catVerifyGate]
      rw [cnotVerifyStep_comp_blockBitFlipPattern e, Evolution.comp_assoc]
  | output => exact ⟨e, he, rfl⟩

/-- **A faulty verification `CNOT₀₂` leaves at most one `X` on the ancilla output.** N&C model a
gate failure as the ideal gate followed by a Pauli on its two wires; `CNOT₀₂`'s wires are the
ancilla control `0` and the extra target `2`, so the injected residue `e` is supported on `{0, 2}`
(`e 1 = 0`) and enters at the `between` slice. Its ancilla weight is `e₀ + e₁ = e₀ ≤ 1`, so this is
a covered single fault — a `between`-slice instance of
`catVerifyGate_anywhere_fault_ancilla_weight_le_one` with a genuine *two*-qubit residue. -/
theorem catVerifyGate_faulty_cnotFirst_ancilla_weight_le_one (e : Fin 3 → Fin 2) (he : e 1 = 0) :
    ∃ r : Fin 3 → Fin 2, (r 0 : ℕ) + (r 1 : ℕ) ≤ 1 ∧
      catVerifyFaultCircuit .between e = (blockBitFlipPattern r).comp catVerifyGate := by
  refine catVerifyGate_anywhere_fault_ancilla_weight_le_one .between e ?_
  omega

/-- **A faulty verification `CNOT₁₂` leaves at most one `X` on the ancilla output.** The `CNOT₁₂`
wires are the ancilla control `1` and the extra target `2`, so the injected residue `e` is supported
on `{1, 2}` (`e 0 = 0`) and enters at the `output` slice (after both `CNOT`s). Its ancilla weight is
`e₀ + e₁ = e₁ ≤ 1` — an `output`-slice instance of the general bound with a two-qubit residue. -/
theorem catVerifyGate_faulty_cnotSecond_ancilla_weight_le_one (e : Fin 3 → Fin 2) (he : e 0 = 0) :
    ∃ r : Fin 3 → Fin 2, (r 0 : ℕ) + (r 1 : ℕ) ≤ 1 ∧
      catVerifyFaultCircuit .output e = (blockBitFlipPattern r).comp catVerifyGate := by
  refine catVerifyGate_anywhere_fault_ancilla_weight_le_one .output e ?_
  omega

/-! ### The assembled count bound — Exercise 10.69's stated conclusion

Exercise 10.69 asks to show that *a single failure anywhere in the ancilla preparation and
verification can lead to at most one `X` or `Y` error in the ancilla output*. A single fault sits in
exactly one of the two stages N&C name — **preparation** or **verification** — and the two are
genuinely different circuit fragments acting on different registers: a preparation fault fans out
across the whole `n`-qubit cat ancilla (`bitReg ι`), whereas a verification fault is localised to
the atomic `ZᵢZⱼ` gadget on its two ancilla qubits plus one fresh syndrome qubit
(`bitFlipReg`, `catVerifyGate`). We therefore encode "a fault anywhere in prep *or* verify" as a
`Sum` over the two locations and assemble, for each, the strongest faithful per-location bound —
both delivering the same uniform conclusion, *the accepted ancilla output carries bit-flip weight
`≤ 1`*:

* a **preparation** fault (`Sum.inl p`) fans out to an arbitrary bit-flip residue `p` on the
  ancilla; by `catState_bitFlip_accepted_at_most_one_error` (**general `n`**, so it is
  verification — not the `X^{⊗n}` symmetry — that does the work) it is either rejected by
  verification or leaves the accepted ancilla with a residue of weight `≤ 1` (indeed `0`);
* a **verification** fault (`Sum.inr (s, e)`) — a bit-flip residue `e` injected at **any** gadget
  time-slice `s ∈ {input, between, output}`, subject to the single-fault constraint that it touches
  at most one ancilla qubit (`e₀ + e₁ ≤ 1`); by `catVerifyGate_anywhere_fault_ancilla_weight_le_one`
  it leaves the ancilla output with a residue of weight `≤ 1`, because no ancilla qubit is a `CNOT`
  target. This genuinely quantifies over N&C's "anywhere" — a fault before, between, or after the
  two `CNOT`s, and a faulty-`CNOT` two-qubit residue (`catVerifyGate_faulty_cnotFirst_…` /
  `_cnotSecond_…`) — not just one position.

In both cases the accepted ancilla carries **at most one** bit flip — i.e. at most one `X` error,
hence at most one `X` or `Y` error: `Y = iXZ` shares its bit-flip part with `X`, and the extra `Z`
phase a `Y` carries is a harmless sign on the `+` cat (`blockPhaseFlip_evolvePure_catBlockState`,
Ex 10.6) that does not propagate to the data (Ex 10.70); see the "What `X` or `Y` means" design
note. The bound is tight — a genuine single `X`/`Y` does occur — so "at most one" cannot be
strengthened to "none". -/
theorem catAncilla_single_fault_at_most_one_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (fault : (ι → ZMod 2) ⊕ CatVerifyFaultSlice × (Fin 3 → Fin 2)) :
    fault.elim
      (fun p => (∃ i j, (zPairObservable i j).HasEigenstate (-1)
                    ((bitString p).evolvePure (catState ι)))
                  ∨ (∃ r : ι → ZMod 2, (∑ i, (r i).val) ≤ 1 ∧
                      (bitString p).evolvePure (catState ι)
                        = (bitString r).evolvePure (catState ι)))
      (fun se => (se.2 0 : ℕ) + (se.2 1 : ℕ) ≤ 1 →
                  ∃ r : Fin 3 → Fin 2, (r 0 : ℕ) + (r 1 : ℕ) ≤ 1 ∧
                    catVerifyFaultCircuit se.1 se.2
                      = (blockBitFlipPattern r).comp catVerifyGate) := by
  cases fault with
  | inl p => exact catState_bitFlip_accepted_at_most_one_error p
  | inr se => exact catVerifyGate_anywhere_fault_ancilla_weight_le_one se.1 se.2

end AxQM
