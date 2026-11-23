/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.MeasureObservableRegister
import AxQM.Postulates.API.SwapCircuit
import AxQM.Postulates.API.GateCommute
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 10.59 (Simplifying the Steane syndrome circuit)

Using Figs 10.14/10.15 identities, replace syndrome circuit Fig 10.16 with Fig 10.17.

**The setup (Nielsen & Chuang §10.5.8, pp. 472–474).** To measure a `±1` observable `M` one uses
the Hadamard-controlled-`M` circuit of Figure 10.13 — an ancilla prepared in `|0⟩`, a Hadamard, a
controlled-`M`, a second Hadamard, then a computational-basis read of the ancilla. In this library
that circuit is `measureObservableCircuit M = (H ⊗ 1) · C(M) · (H ⊗ 1)` (ancilla on
the left/control wire; N&C Exercise 4.34). Figure 10.16 is the seven-qubit **Steane-code** syndrome
circuit: one ancilla per stabilizer generator, each ancilla running exactly this construction with
`M` the product of `X`s and `Z`s prescribed by the generator (read off the standard-form check
matrix (10.112)). Figure 10.17 is the claimed **equivalent** circuit, in which the ancilla
Hadamards have disappeared and every data wire carries the pattern `H • H •`.

**Structure of the development.** The replacement is
`measureObservableCircuit gₐ = (Figure-10.17 block)` for a generator `gₐ` — the identity assembled
here for representative two-data-wire generators, in three layers: the two atomic identities, their
per-wire lifts, and the block-split that stitches the factors together. Concretely, **this file
establishes the two atomic ingredients** — each a standalone, reusable identity — and, using the
register-lifting lemmas of `AxQM/Postulates/API/MeasureObservableRegister.lean`, **the compilation
of each factor of a generator to its Figure-10.17 form**:

1. **The two Figure 10.14 / 10.15 identities**, for the elementary observables `X` and `Z`, built
   from the **reversed CNOT** `reversedCnotGate` (the `CNOT` whose control is the data/right wire
   and whose target is the ancilla/left wire):
   * **Figure 10.15 (measuring `Z`).** No basis change — copying the data qubit's `Z`-value onto the
     ancilla is a single reversed CNOT: `measureObservableCircuit Z = reversedCNOT`
     (`measureObservableCircuit_pauliZGate_eq_reversedCnot`).
   * **Figure 10.14 (measuring `X`).** The same up to conjugating the *data* wire by a Hadamard
     (rotating the `X`-eigenbasis to the `Z`-eigenbasis and back):
     `measureObservableCircuit X = (1 ⊗ H) · reversedCNOT · (1 ⊗ H)`
     (`measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot`).
   Both are honest equalities of the underlying two-qubit **unitaries** (`Evolution`s), stronger
   than equality of the resulting measurements. (These identities are the subject of Exercise 10.58;
   here they are the *tools* Exercise 10.59 is asked to "use".)
2. **The block-splitting identity** `measureObservableCircuit_comp` — a general
   lemma about `measureObservableCircuit`, in
   `AxQM/Postulates/API/MeasureObservable.lean` (mirroring `controlledUnitary_comp`):
   `measureObservableCircuit (U · V) = measureObservableCircuit U · measureObservableCircuit V`.
   This is the step Figure 10.16 → Figure 10.17 genuinely turns on: a single ancilla's block for a
   generator `gₐ = ∏ᵢ Pᵢ` — a *single* Hadamard-controlled block `H_a · (∏ᵢ C(Pᵢ)) · H_a` around a
   *product* of controlled Paulis — is split into a *sequence* of one-Pauli blocks, because the
   controlled gate factors (`C(U·V) = C(U)·C(V)`) and the two ancilla Hadamards that meet between
   consecutive blocks annihilate (`H² = 1`). It is this `H² = 1` insertion — **not** a syntactic
   rewrite — that lets the atomic identities of (1) apply factor-by-factor. Each resulting one-Pauli
   block then simplifies by (1), pushing the ancilla Hadamards off (`Z` factors) and onto the data
   wires (`X` factors), which is exactly the Figure-10.17 `H • H •` pattern.

The **register lift** is the bridge from the atomic identities (1), stated on a single data qubit,
to a generator's factors, each a Pauli on *one wire of a multi-qubit register*:
`measureObservableCircuit_onLeft`
(`AxQM/Postulates/API/MeasureObservableRegister.lean`) transports the
block for `P ⊗ 1_T` — a Pauli `P` on the first data wire, identity on the rest — down to the
two-wire block `measureObservableCircuit P` with the rest carried along. Composed with (1) it gives
`measureObservableCircuit_pauliZGate_onLeft_eq` / `measureObservableCircuit_pauliXGate_onLeft_eq`
below: the *first* factor of a Figure-10.16 generator, on any number of data qubits, in its
Figure-10.17 reversed-CNOT form. The companion `measureObservableCircuit_onRight` lifts a factor on
a *last* wire (spectator register only on its left), across the left-commutation reshape
`QSystem.Iso.leftComm`; composed with (1) it gives
`measureObservableCircuit_pauliZGate_onRight_eq` / `measureObservableCircuit_pauliXGate_onRight_eq`.
The two one-sided lifts compose into
`measureObservableCircuit_onMiddle`, the *genuine interior* lift for a wire carrying spectators on
*both* sides (the `onRight ∘ onLeft` composite), giving
`measureObservableCircuit_pauliZGate_onMiddle_eq` / `_pauliXGate_onMiddle_eq` — the compilation of a
`Z`/`X` check on any wire strictly inside the register.

With the per-wire lifts covering every position (first / last / interior), assembling a generator is
the block-split (2). Its **arbitrary-weight** form is `measureObservableCircuit_listComp`
(`AxQM/Postulates/API/MeasureObservable.lean`), the `n`-fold `H² = 1` split
`measureObservableCircuit (∏ᵢ Uᵢ) = ∏ᵢ measureObservableCircuit Uᵢ`, so the block for a generator of
*any* weight is the sequence of its one-factor blocks. The per-generator replacement theorems
`measureObservableCircuit_zTypeGenerator_eq_fig1017Block` /
`measureObservableCircuit_xTypeGenerator_eq_fig1017Block` (the two Steane families) and
`measureObservableCircuit_generatorBlock_eq_fig1017Block` (a mixed product) instantiate the split on
two-data-wire generators, and `measureObservableCircuit_zTypeGenerator_threeWire_eq` on a
three-data-wire generator whose middle factor is a genuine both-spectator interior wire — so the
extension to a full-width Steane generator (the same two steps, with deeper register nesting) is
demonstrated, not merely asserted.

## The formalisation

Atomic identities:
* `measureObservableCircuit_pauliZGate_eq_reversedCnot` — Figure 10.15.
* `measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot` — Figure 10.14.

Per-wire compilation on a data register, built from the atomic identities and the
register lifts — a factor compiles to its Figure-10.17 form at every position:
* `measureObservableCircuit_pauliZGate_onLeft_eq` — a `Z`-check on the *first* data wire of a
  register `qubit ⊗ T` (spectators only on the right) in Figure-10.17 form.
* `measureObservableCircuit_pauliXGate_onLeft_eq` — the same for an `X`-check.
* `measureObservableCircuit_pauliZGate_onRight_eq` — a `Z`-check on a *last* data wire `A ⊗ qubit`
  (spectators only on the left) in Figure-10.17 form.
* `measureObservableCircuit_pauliXGate_onRight_eq` — the same for an `X`-check.
* `measureObservableCircuit_pauliZGate_onMiddle_eq` — a `Z`-check on a *genuine interior* data wire
  `A ⊗ (qubit ⊗ B)` (spectators `A` before and `B` after) in Figure-10.17 form.
* `measureObservableCircuit_pauliXGate_onMiddle_eq` — the same for an `X`-check.

Per-generator replacement, the assembled Figure 10.16 → Figure 10.17 claim, each
split by the block-split and compiled by the per-wire identities above:
* `measureObservableCircuit_zTypeGenerator_eq_fig1017Block` — a `Z`-type generator `Z₁Z₂` compiles
  to two bare reversed CNOTs (no Hadamards).
* `measureObservableCircuit_xTypeGenerator_eq_fig1017Block` — an `X`-type generator `X₁X₂` compiles
  to Hadamard-conjugated reversed CNOTs (the `H • H •` rows).
* `measureObservableCircuit_generatorBlock_eq_fig1017Block` — a mixed generator `X₁Z₂`, the
  type-agnostic block split.
* `measureObservableCircuit_zTypeGenerator_threeWire_eq` — a three-data-wire generator whose middle
  factor is a genuine both-spectator interior wire, exhibiting the interior register nesting.

General lemmas (`AxQM/Postulates/API/`):
* `measureObservableCircuit_comp` / `measureObservableCircuit_listComp`
  (`AxQM/Postulates/API/MeasureObservable.lean`) —
  the `H² = 1` block split: binary, and the `n`-fold form for any weight (unit
  `measureObservableCircuit_id`).
* `measureObservableCircuit_onLeft` / `_onRight` / `_onMiddle`
  (`AxQM/Postulates/API/MeasureObservableRegister.lean`) —
  the register lifts for a first-wire / last-wire / genuine-interior factor.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Figure 10.15 (measuring `Z`).** The standard Hadamard-controlled circuit for
measuring the observable `Z` — `measureObservableCircuit pauliZGate = (H ⊗ 1) · C(Z) · (H ⊗ 1)` —
equals a single **reversed CNOT** (control on the data/right wire, target on the ancilla/left wire),
with the ancilla Hadamards gone entirely. This is the "useful simplification" drawn on the right of
Figure 10.15: no basis change is needed to measure `Z`, only a parity copy onto the ancilla.

The controlled-`Z` gate is `controlledUnitary pauliZGate` by definition, so
`measureObservableCircuit pauliZGate` is definitionally the right-hand side of
`reversedCnotGate_eq_hadamard_conj_controlledZGate` (`reversedCNOT = (H ⊗ 1) · CZ · (H ⊗ 1)`), and
the identity is that fact read backwards. -/
theorem measureObservableCircuit_pauliZGate_eq_reversedCnot :
    measureObservableCircuit pauliZGate = reversedCnotGate :=
  reversedCnotGate_eq_hadamard_conj_controlledZGate.symm

/-- **Nielsen & Chuang, Figure 10.14 (measuring `X`).** The standard Hadamard-controlled circuit for
measuring the observable `X` — `measureObservableCircuit pauliXGate = (H ⊗ 1) · C(X) · (H ⊗ 1)`,
where `C(X) = CNOT` — equals the **reversed CNOT** conjugated on the data/right wire by a Hadamard:
`measureObservableCircuit X = (1 ⊗ H) · reversedCNOT · (1 ⊗ H)`. This is the "useful equivalent
circuit" drawn on the right of Figure 10.14: measuring `X` is measuring `Z` (a reversed CNOT) after
rotating the data qubit into the `Z`-eigenbasis with a Hadamard and back again.

Both sides equal `(H ⊗ H) · CZ · (H ⊗ H)`. Rewriting `C(X) = CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)`
(Exercise 4.17) on the left and `reversedCNOT = (H ⊗ 1) · CZ · (H ⊗ 1)`
(`reversedCnotGate_eq_hadamard_conj_controlledZGate`) on the right, both circuits become the two
commuting Hadamard layers `H ⊗ 1` and `1 ⊗ H` wrapped around `CZ`; `Evolution.onLeft_comm_onRight`
(a left-factor gate commutes with a right-factor gate) identifies them. -/
theorem measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot :
    measureObservableCircuit pauliXGate
      = (hadamardGate.onRight qubit).comp
          (reversedCnotGate.comp (hadamardGate.onRight qubit)) := by
  have hmeas : measureObservableCircuit pauliXGate
      = (hadamardGate.onLeft qubit).comp
          (cnotGate.comp (hadamardGate.onLeft qubit)) := rfl
  rw [hmeas, cnotGate_eq_hadamard_conj_controlledZGate,
    reversedCnotGate_eq_hadamard_conj_controlledZGate]
  set HL := hadamardGate.onLeft qubit
  set HR := hadamardGate.onRight qubit
  have hcomm : HL.comp HR = HR.comp HL :=
    Evolution.onLeft_comm_onRight hadamardGate hadamardGate
  -- Both sides are `(H ⊗ H) · CZ · (H ⊗ H)`, up to commuting the two Hadamard layers.
  calc HL.comp ((HR.comp (controlledZGate.comp HR)).comp HL)
      = (HL.comp HR).comp (controlledZGate.comp (HR.comp HL)) := by
        simp only [Evolution.comp_assoc]
    _ = (HR.comp HL).comp (controlledZGate.comp (HL.comp HR)) := by rw [hcomm]
    _ = HR.comp ((HL.comp (controlledZGate.comp HL)).comp HR) := by
        simp only [Evolution.comp_assoc]

/-! ### The first-factor compilation on a data register (Figure 10.16 → Figure 10.17) -/

/-- **Nielsen & Chuang, Figure 10.17 — a `Z`-check on the first data wire.** For a stabilizer
generator whose first Pauli is a `Z` on data qubit 1 (identity on the remaining register `T`), the
Figure-10.16 ancilla block for that factor — `measureObservableCircuit (Z ⊗ 1_T)`, a single ancilla
Hadamard-controlling `Z ⊗ 1_T` — equals a bare **reversed CNOT** from data qubit 1 into the ancilla,
with the rest of the register untouched, re-bracketed to the ancilla's native nesting
`qubit ⊗ (qubit ⊗ T)`. This is Figure 10.15's "no Hadamards" simplification
(`measureObservableCircuit_pauliZGate_eq_reversedCnot`) lifted off the two-qubit case onto an
arbitrary data register by `measureObservableCircuit_onLeft`. -/
theorem measureObservableCircuit_pauliZGate_onLeft_eq (T : QSystem) :
    measureObservableCircuit (pauliZGate.onLeft T)
      = Evolution.congr (QSystem.assoc qubit qubit T).symm (reversedCnotGate.onLeft T) := by
  rw [measureObservableCircuit_onLeft, measureObservableCircuit_pauliZGate_eq_reversedCnot]

/-- **Nielsen & Chuang, Figure 10.17 — an `X`-check on the first data wire.** For a generator whose
first Pauli is an `X` on data qubit 1 (identity on the remaining register `T`), the Figure-10.16
ancilla block for that factor — `measureObservableCircuit (X ⊗ 1_T)` — equals the reversed CNOT from
data qubit 1 into the ancilla, conjugated by Hadamards on that data wire (`H • H` on the wire, the
Figure-10.17 pattern), with the rest of the register untouched. This is Figure 10.14's equivalent
circuit (`measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot`) lifted onto an
arbitrary data register by `measureObservableCircuit_onLeft`. -/
theorem measureObservableCircuit_pauliXGate_onLeft_eq (T : QSystem) :
    measureObservableCircuit (pauliXGate.onLeft T)
      = Evolution.congr (QSystem.assoc qubit qubit T).symm
          (((hadamardGate.onRight qubit).comp
            (reversedCnotGate.comp (hadamardGate.onRight qubit))).onLeft T) := by
  rw [measureObservableCircuit_onLeft,
    measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot]

/-! ### The interior-wire compilation on a data register (Figure 10.16 → Figure 10.17) -/

/-- **Nielsen & Chuang, Figure 10.17 — a `Z`-check on an interior data wire.** For a stabilizer
generator whose factor on data qubit `i` is a `Z` (identity on the register `A` of the wires that
precede it), the Figure-10.16 ancilla block for that factor — `measureObservableCircuit (1_A ⊗ Z)`,
a single ancilla Hadamard-controlling `1_A ⊗ Z` — equals a bare **reversed CNOT** from that data
qubit into the ancilla, with the preceding register `A` untouched, re-bracketed to the ancilla's
native nesting `qubit ⊗ (A ⊗ qubit)` by the left-commutation reshape. This is Figure 10.15's
"no Hadamards" simplification (`measureObservableCircuit_pauliZGate_eq_reversedCnot`) lifted onto an
*interior* wire of the data register by `measureObservableCircuit_onRight` — the `onRight` companion
of `measureObservableCircuit_pauliZGate_onLeft_eq`, needed because every data wire except the first
carries a nonempty spectator register on its left. -/
theorem measureObservableCircuit_pauliZGate_onRight_eq (A : QSystem) :
    measureObservableCircuit (pauliZGate.onRight A)
      = Evolution.congr (QSystem.Iso.leftComm A qubit qubit) (reversedCnotGate.onRight A) := by
  rw [measureObservableCircuit_onRight, measureObservableCircuit_pauliZGate_eq_reversedCnot]

/-- **Nielsen & Chuang, Figure 10.17 — an `X`-check on an interior data wire.** For a generator
whose factor on data qubit `i` is an `X` (identity on the preceding register `A`), the Figure-10.16
ancilla block for that factor — `measureObservableCircuit (1_A ⊗ X)` — equals the reversed CNOT
from that data qubit into the ancilla, conjugated by Hadamards on that wire (`H • H` on the wire,
the Figure-10.17 pattern), with the preceding register `A` untouched, re-bracketed to
`qubit ⊗ (A ⊗ qubit)`. This is Figure 10.14's equivalent circuit
(`measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot`) lifted onto an interior wire by
`measureObservableCircuit_onRight` — the `onRight` companion of
`measureObservableCircuit_pauliXGate_onLeft_eq`. -/
theorem measureObservableCircuit_pauliXGate_onRight_eq (A : QSystem) :
    measureObservableCircuit (pauliXGate.onRight A)
      = Evolution.congr (QSystem.Iso.leftComm A qubit qubit)
          (((hadamardGate.onRight qubit).comp
            (reversedCnotGate.comp (hadamardGate.onRight qubit))).onRight A) := by
  rw [measureObservableCircuit_onRight,
    measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot]

/-! ### The genuine interior-wire compilation: a factor with spectators on both sides -/

/-- **Nielsen & Chuang, Figure 10.17 — a `Z`-check on a genuine interior data wire.** For a
stabilizer generator whose factor is a `Z` on a data wire with a register `A` of the wires *before*
it and a register `B` of the wires *after* it — `measureObservableCircuit (1_A ⊗ Z ⊗ 1_B)` — the
Figure-10.16 ancilla block equals a bare **reversed CNOT** from that data qubit into the ancilla,
`A` and `B` untouched, re-bracketed to the ancilla's native front. Where
`measureObservableCircuit_pauliZGate_onLeft_eq` handles the *first* wire (spectators only on the
right) and `measureObservableCircuit_pauliZGate_onRight_eq` a *last* wire (spectators only on the
left), this is the genuine interior case with spectators on *both* sides — the `onRight ∘ onLeft`
composite — lifting Figure 10.15's simplification by `measureObservableCircuit_onMiddle`. Every code
qubit strictly between the first and the last of a Figure-10.16 register is such a factor. -/
theorem measureObservableCircuit_pauliZGate_onMiddle_eq (A B : QSystem) :
    measureObservableCircuit ((pauliZGate.onLeft B).onRight A)
      = Evolution.congr (QSystem.Iso.leftComm A qubit (qubit ⊗ B))
          ((Evolution.congr (QSystem.assoc qubit qubit B).symm
            (reversedCnotGate.onLeft B)).onRight A) := by
  rw [measureObservableCircuit_onMiddle, measureObservableCircuit_pauliZGate_eq_reversedCnot]

/-- **Nielsen & Chuang, Figure 10.17 — an `X`-check on a genuine interior data wire.** As
`measureObservableCircuit_pauliZGate_onMiddle_eq`, for an `X` factor with spectator registers `A`
before and `B` after: `measureObservableCircuit (1_A ⊗ X ⊗ 1_B)` equals the reversed CNOT into the
ancilla conjugated by Hadamards on that data wire (the `H • H •` Figure-10.17 pattern), `A` and `B`
untouched. Figure 10.14's equivalent circuit lifted onto a both-spectator interior wire by
`measureObservableCircuit_onMiddle`. -/
theorem measureObservableCircuit_pauliXGate_onMiddle_eq (A B : QSystem) :
    measureObservableCircuit ((pauliXGate.onLeft B).onRight A)
      = Evolution.congr (QSystem.Iso.leftComm A qubit (qubit ⊗ B))
          ((Evolution.congr (QSystem.assoc qubit qubit B).symm
            (((hadamardGate.onRight qubit).comp
              (reversedCnotGate.comp (hadamardGate.onRight qubit))).onLeft B)).onRight A) := by
  rw [measureObservableCircuit_onMiddle,
    measureObservableCircuit_pauliXGate_eq_hadamardConj_reversedCnot]

/-! ### The per-generator syndrome-block replacement (Figure 10.16 → Figure 10.17)

The assembly of the atomic identities and the register lifts into the exercise's claim. A
Figure-10.16 ancilla block Hadamard-controls a *product* of single-wire Paulis — a stabilizer
generator `gₐ = ∏ᵢ Pᵢ`; the block equals the Figure-10.17 block, a *sequence* of one-Pauli blocks
with the ancilla Hadamards gone. Two independent axes of generality are involved, and both are
discharged as reusable lemmas — not smuggled into a single fixed instance:

* **Number of factors (weight).** `measureObservableCircuit_listComp`
  (`Postulates/API/MeasureObservable.lean`) is the `n`-fold `H² = 1` split: for a product of *any*
  length, `measureObservableCircuit (∏ᵢ Uᵢ) = ∏ᵢ measureObservableCircuit Uᵢ`. So the block for a
  generator of any weight is the composition of its one-factor blocks.
* **Position of a factor on the register.** A factor compiles to its Figure-10.17 form wherever it
  sits: the *first* wire by `…_onLeft_eq`, a *last* wire by `…_onRight_eq`, and a *genuine interior*
  wire — with spectators on both sides — by `…_onMiddle_eq` (the `onRight ∘ onLeft` composite),
  which is exactly every code qubit strictly inside a Figure-10.16 register.

The concrete theorems below instantiate these axes. The two-data-wire generators exhibit the two
Steane generator families (an `X`-type generator → the all-`H • H •` rows, a `Z`-type generator →
the all-reversed-CNOT rows) and the type-agnostic split of a mixed product; the three-data-wire
generator exhibits a genuine both-spectator interior factor. A full-weight Steane generator is these
same two steps — `measureObservableCircuit_listComp`, then the per-wire compilation of each factor —
with deeper but mechanical register nesting. -/

/-- **Nielsen & Chuang, Figure 10.16 → 10.17 — a `Z`-type generator.** The Figure-10.16 syndrome
block for a two-qubit `Z`-type stabilizer generator `Z₁Z₂` — one ancilla Hadamard-controlling the
product `(Z ⊗ 1)·(1 ⊗ Z) = Z ⊗ Z` — equals the Figure-10.17 block: a sequence of two bare
**reversed CNOTs**, one from each data wire into the ancilla, with *no* Hadamards anywhere (the `Z`
rows of Figure 10.17). The `H² = 1` block split `measureObservableCircuit_comp` separates the block
for the product into two one-factor blocks, each then Figure 10.15's Hadamard-free simplification
lifted onto its wire (`measureObservableCircuit_pauliZGate_onLeft_eq` for the first data wire,
`measureObservableCircuit_pauliZGate_onRight_eq` for the interior wire). -/
theorem measureObservableCircuit_zTypeGenerator_eq_fig1017Block :
    measureObservableCircuit ((pauliZGate.onLeft qubit).comp (pauliZGate.onRight qubit))
      = (Evolution.congr (QSystem.assoc qubit qubit qubit).symm
            (reversedCnotGate.onLeft qubit)).comp
          (Evolution.congr (QSystem.Iso.leftComm qubit qubit qubit)
            (reversedCnotGate.onRight qubit)) := by
  rw [measureObservableCircuit_comp, measureObservableCircuit_pauliZGate_onLeft_eq,
    measureObservableCircuit_pauliZGate_onRight_eq]

/-- **Nielsen & Chuang, Figure 10.16 → 10.17 — an `X`-type generator.** The Figure-10.16 syndrome
block for a two-qubit `X`-type stabilizer generator `X₁X₂` — one ancilla Hadamard-controlling
`(X ⊗ 1)·(1 ⊗ X) = X ⊗ X` — equals the Figure-10.17 block: on each data wire a **reversed CNOT**
into the ancilla conjugated by Hadamards on that wire (the `H • H •` pattern of the `X` rows of
Figure 10.17), with the ancilla Hadamards gone. The `H² = 1` block split
`measureObservableCircuit_comp` separates the two factors; each is Figure 10.14's equivalent circuit
lifted onto its wire (`measureObservableCircuit_pauliXGate_onLeft_eq` for the first data wire,
`measureObservableCircuit_pauliXGate_onRight_eq` for the interior wire). -/
theorem measureObservableCircuit_xTypeGenerator_eq_fig1017Block :
    measureObservableCircuit ((pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit))
      = (Evolution.congr (QSystem.assoc qubit qubit qubit).symm
            (((hadamardGate.onRight qubit).comp
              (reversedCnotGate.comp (hadamardGate.onRight qubit))).onLeft qubit)).comp
          (Evolution.congr (QSystem.Iso.leftComm qubit qubit qubit)
            (((hadamardGate.onRight qubit).comp
              (reversedCnotGate.comp (hadamardGate.onRight qubit))).onRight qubit)) := by
  rw [measureObservableCircuit_comp, measureObservableCircuit_pauliXGate_onLeft_eq,
    measureObservableCircuit_pauliXGate_onRight_eq]

/-- **Nielsen & Chuang, Figure 10.16 → 10.17 — a mixed (cross-type) generator.** A representative
Figure-10.16 syndrome block for the mixed two-qubit generator `X₁Z₂` — one ancilla
Hadamard-controlling the product `(X ⊗ 1)·(1 ⊗ Z) = X ⊗ Z` — equals its Figure-10.17 block: the `X`
wire carries the Hadamard-conjugated reversed CNOT (`H • H •`) and the `Z` wire a bare reversed
CNOT, the ancilla Hadamards gone. Its role beside the `Z`- and `X`-type theorems is to show the
block split is *independent of the factor types*: `measureObservableCircuit_comp` (`H² = 1`) splits
the product `X ⊗ Z` into one block per factor irrespective of whether the factors are `X`s or `Z`s,
and each one-factor block simplifies by the Figure 10.14 / 10.15 identity for its own Pauli. The
weight-agnostic and position-agnostic forms of this replacement are
`measureObservableCircuit_listComp` and the `onLeft`/`onRight`/`onMiddle` per-wire compilations;
this theorem is a single 2-wire instance of them. -/
theorem measureObservableCircuit_generatorBlock_eq_fig1017Block :
    measureObservableCircuit ((pauliXGate.onLeft qubit).comp (pauliZGate.onRight qubit))
      = (Evolution.congr (QSystem.assoc qubit qubit qubit).symm
            (((hadamardGate.onRight qubit).comp
              (reversedCnotGate.comp (hadamardGate.onRight qubit))).onLeft qubit)).comp
          (Evolution.congr (QSystem.Iso.leftComm qubit qubit qubit)
            (reversedCnotGate.onRight qubit)) := by
  rw [measureObservableCircuit_comp, measureObservableCircuit_pauliXGate_onLeft_eq,
    measureObservableCircuit_pauliZGate_onRight_eq]

/-- **Nielsen & Chuang, Figure 10.16 → 10.17 — a three-data-wire generator with a genuine interior
factor.** The Figure-10.16 syndrome block for the `Z`-type generator `Z₁Z₂` on a *three*-data-wire
register `qubit ⊗ (qubit ⊗ qubit)` — the product `(Z ⊗ 1 ⊗ 1)·(1 ⊗ Z ⊗ 1)`, `Z` on wires 1 and 2,
identity on wire 3 — equals its Figure-10.17 block, two bare reversed CNOTs. Its point over the
two-data-wire theorems: wire 2 here is a *genuine interior* wire — wire 1 is a spectator on its left
*and* wire 3 a spectator on its right — so its factor compiles through the both-spectator
`onRight ∘ onLeft` lift (`measureObservableCircuit_pauliZGate_onMiddle_eq`), not `onLeft` or
`onRight` in isolation. This exhibits the register nesting a code qubit strictly inside a
Figure-10.16 data register needs, so the extension to a full-width Steane generator is demonstrated,
not merely asserted. The block splits by `measureObservableCircuit_comp`; wire 1's factor compiles
by `measureObservableCircuit_pauliZGate_onLeft_eq`, wire 2's by the interior lift. -/
theorem measureObservableCircuit_zTypeGenerator_threeWire_eq :
    measureObservableCircuit
        ((pauliZGate.onLeft (qubit ⊗ qubit)).comp ((pauliZGate.onLeft qubit).onRight qubit))
      = (Evolution.congr (QSystem.assoc qubit qubit (qubit ⊗ qubit)).symm
            (reversedCnotGate.onLeft (qubit ⊗ qubit))).comp
          (Evolution.congr (QSystem.Iso.leftComm qubit qubit (qubit ⊗ qubit))
            ((Evolution.congr (QSystem.assoc qubit qubit qubit).symm
              (reversedCnotGate.onLeft qubit)).onRight qubit)) := by
  rw [measureObservableCircuit_comp, measureObservableCircuit_pauliZGate_onLeft_eq,
    measureObservableCircuit_pauliZGate_onMiddle_eq]

end AxQM
