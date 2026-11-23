/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.ControlPairGates

/-!
# A two-qubit-gate-count model for three-qubit circuits (Nielsen & Chuang §4.3)

Nielsen & Chuang **Exercise 4.25** (Fredkin gate construction) closes with two *gate-count* claims
phrased over **two-qubit gates**: part (3) builds the Fredkin gate "using only **six two-qubit
gates**", and part (4) asks for an even simpler construction with "only **five two-qubit gates**".
Here a *controlled single-qubit gate* `C(V)` counts as **one** two-qubit gate — the same convention
that makes Figure 4.8's `C²(U)` decomposition "five two-qubit gates" (`C(V)`, `CNOT`, `C(V†)`,
`CNOT`, `C(V)`). To state such a claim *faithfully* the count must be a genuine proposition about a
circuit, not a term the reader tallies by eye.

This is a **coarser** cost model than the one-qubit + `CNOT` model of `Core.GateCircuit` (`Gate3`,
`oneQubitCount`, `cnotCount`, Exercise 4.22): there a `C(V)` is *decomposed* into single-qubit gates
and `CNOT`s (the ABC decomposition), so it is not one gate. Both models are honest; they count
different alphabets for different exercises. This file provides the vehicle Exercise 4.25 parts 3–4
need: a typed **two-qubit-gate circuit** on `qubit ⊗ (qubit ⊗ qubit)` (wires `0, 1, 2`) as a `List`
of `TwoQubitGate3`s, each of which is a genuine **two-qubit** gate — it acts on at most two of the
three wires — together with

* `TwoQubitGate3.denote` / `twoQubitCircuit` — the `Evolution` a gate / gate list implements (the
  monoid product of the gate denotations), so a circuit *means* a concrete unitary; and
* `twoQubitCount` — the number of two-qubit gates, which is simply the list length (every element
  *is* a two-qubit gate),

turning "the Fredkin gate can be built from at most `n` two-qubit gates" into the honest existential
`∃ gs, twoQubitCircuit gs = fredkinGate ∧ twoQubitCount gs ≤ n`.

## What is formalised

* `TwoQubitGate3` — a two-qubit gate on `qubit ⊗ (qubit ⊗ qubit)`, in one of four forms. The
  parts-1–3 forms `pair`/`ctrl` are chosen so the placements those parts need are bare composites
  with no associator/SWAP bookkeeping (the placements in `ccontrolledUnitaryCircuit`, Exercise
  4.21); the part-4 forms `pairAB`/`pairAC` add an arbitrary gate on a *control* pair via
  associator/`leftComm` transport (see the design note below):
  * `pair U` — an **arbitrary** two-qubit gate `U : Evolution (qubit ⊗ qubit)` on the target pair
    `{1, 2}`, with the control wire `0` idle (`U.onRight qubit = 1 ⊗ U`);
  * `ctrl t g` — a **control-wire-`0`** gate: the single-qubit gate `g` on wire `1` (`t = 0`) or
    wire `2` (`t = 1`), conditioned on wire `0`, with the remaining wire idle
    (`controlledUnitary (g.onLeft/onRight qubit)`).
  * `pairAB U` / `pairAC U` — an **arbitrary** two-qubit gate `U` on a *control* pair, `{0,1}`
    (`leftPairGate U`, wire `2` idle) or `{0,2}` (`outerPairGate U`, wire `1` idle). Unlike `ctrl`
    these admit *entangling* gates on a control pair — the class Exercise 4.25 part 4's
    five-two-qubit-gate Fredkin construction provably needs (a controlled-single-qubit alphabet
    cannot reach five gates). Parts 1–3 use only `pair`/`ctrl`; these extend the *same* count model
    so "five two-qubit gates" is compared like-for-like with part 3's "six".
  Each form is a genuine two-qubit gate: `pair U` leaves wire `0` untouched
  (`TwoQubitGate3.pair_denote_evolvePure`), and `ctrl t g` acts on wire `0` and one target wire.
* `twoQubitCircuit gs = (gs.map TwoQubitGate3.denote).prod` — the composite `Evolution`, in operator
  order (leftmost gate is the leftmost `comp` factor, applied last).
* `twoQubitCount gs = gs.length` — the two-qubit-gate count.
* structural rewrites `twoQubitCircuit_nil/cons/append` and the denotation unfoldings
  `denote_pair`/`denote_ctrl_zero`/`denote_ctrl_one`/`denote_pairAB`/`denote_pairAC` — the API a
  circuit-assembly proof uses.

## Design notes

* **Statements.** Every declaration's statement names only gates (`Evolution` and its monoid
  `comp`/`1`, `controlledUnitary`, `Evolution.onLeft`/`onRight`) and plain `List`/`ℕ` data. The
  gates it composes are in `AxQM/Postulates/API/`; Exercise 4.25 itself is in
  `AxQM/NC/Ch4/Exercise4_25.lean`.
* **Why these constructors (an honest, non-ad-hoc alphabet).** Reading Figure 4.8 (Exercise 4.21,
  `ccontrolledUnitaryCircuit`) shows its five gates are *already* `pair`s and `ctrl`s:
  `(controlledUnitary V).onRight qubit` is a `pair`, and the `controlledUnitary (_.onLeft/onRight
  qubit)` gates are `ctrl`s. So `pair`/`ctrl` are the natural alphabet for the Chapter-4 controlled
  constructions (parts 1–3), not a Fredkin-specific gadget. Like `Gate3.cnotOn` — which realises the
  non-adjacent `(0,2)` `CNOT` as a control-wire-`0` gate rather than by SWAP conjugation — those two
  forms are *tailored* to the placements parts 1–3 use and need no associator transport. Part 4's
  five-two-qubit-gate construction *does* need a genuinely entangling gate on a *control* pair (not
  of `ctrl` form): `pairAB`/`pairAC` supply exactly the general `{0,1}` / `{0,2}` placements — an
  arbitrary two-qubit gate carried across `QSystem.assoc` / `QSystem.Iso.leftComm` with
  `Evolution.congr`.
* **Why the count is the list length.** In `Gate3` a list mixes one-qubit gates and `CNOT`s, so the
  count is a `List.countP`. Here *every* element is a two-qubit gate, so the number of two-qubit
  gates is exactly `gs.length`; `twoQubitCount` is a transparent alias for it, inheriting
  `List.length_cons`/`length_append`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A two-qubit gate in a three-qubit circuit** on `qubit ⊗ (qubit ⊗ qubit)` (wires `0, 1, 2`),
in one of four genuine two-qubit forms:

* `pair U` — an arbitrary two-qubit gate `U` on the target pair `{1, 2}`, control wire `0` idle;
* `ctrl t g` — the single-qubit gate `g` on wire `1` (`t = 0`) or wire `2` (`t = 1`), controlled on
  wire `0`, the remaining wire idle;
* `pairAB U` — an arbitrary two-qubit gate `U` on the left control pair `{0, 1}` (via
  `leftPairGate`, wire `2` idle);
* `pairAC U` — an arbitrary two-qubit gate `U` on the outer control pair `{0, 2}` (via
  `outerPairGate`, wire `1` idle).

`pairAB`/`pairAC` admit *entangling* gates on a control pair — the class Exercise 4.25 part 4's
five-two-qubit-gate Fredkin construction needs, which `ctrl` (controlled-single-qubit) cannot give.
Its `TwoQubitGate3.denote`ation is an `Evolution`; because every gate is a two-qubit gate, the
number of two-qubit gates in a list is just its `twoQubitCount` (= length), so "the Fredkin gate is
built from at most `n` two-qubit gates" becomes a genuine proposition. -/
inductive TwoQubitGate3 where
  | /-- An arbitrary two-qubit gate `U` on the target pair `{1, 2}` (control wire `0` idle). -/
    pair (U : Evolution (qubit ⊗ qubit))
  | /-- The single-qubit gate `g` controlled on wire `0`, targeting wire `1` (`target = 0`) or
      wire `2` (`target = 1`). -/
    ctrl (target : Fin 2) (g : Evolution qubit)
  | /-- An arbitrary two-qubit gate `U` on the left control pair `{0, 1}` (wire `2` idle), placed
      via `leftPairGate`. Needed for the five-two-qubit-gate Fredkin construction (Exercise 4.25
      part 4), whose entangling gate on a control pair is not of `ctrl` (controlled-single-qubit)
      form. -/
    pairAB (U : Evolution (qubit ⊗ qubit))
  | /-- An arbitrary two-qubit gate `U` on the outer control pair `{0, 2}` (wire `1` idle), placed
      via `outerPairGate`. -/
    pairAC (U : Evolution (qubit ⊗ qubit))

namespace TwoQubitGate3

/-- **The `Evolution` denoted by a single two-qubit gate** (all four forms): `pair U = 1 ⊗ U` places
`U` on the target pair `{1, 2}`; `ctrl 0 g` / `ctrl 1 g` place the control-wire-`0` gate `C(g)` on
wire `1` / wire `2` (via `g.onLeft qubit` / `g.onRight qubit` inside `controlledUnitary`);
`pairAB U = leftPairGate U` places `U` on the left control pair `{0, 1}` and
`pairAC U = outerPairGate U` places `U` on the outer control pair `{0, 2}`. -/
def denote : TwoQubitGate3 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | pair U => U.onRight qubit
  | ctrl 0 g => controlledUnitary (g.onLeft qubit)
  | ctrl _ g => controlledUnitary (g.onRight qubit)
  | pairAB U => leftPairGate U
  | pairAC U => outerPairGate U

@[simp] theorem denote_pair (U : Evolution (qubit ⊗ qubit)) :
    (pair U).denote = U.onRight qubit := rfl

@[simp] theorem denote_ctrl_zero (g : Evolution qubit) :
    (ctrl 0 g).denote = controlledUnitary (g.onLeft qubit) := rfl

@[simp] theorem denote_ctrl_one (g : Evolution qubit) :
    (ctrl 1 g).denote = controlledUnitary (g.onRight qubit) := rfl

@[simp] theorem denote_pairAB (U : Evolution (qubit ⊗ qubit)) :
    (pairAB U).denote = leftPairGate U := rfl

@[simp] theorem denote_pairAC (U : Evolution (qubit ⊗ qubit)) :
    (pairAC U).denote = outerPairGate U := rfl

/-- **A `pair` gate is a genuine two-qubit gate**: it leaves the control wire `0` untouched,
`(1 ⊗ U)(ψ ⊗ φ) = ψ ⊗ (U φ)`. -/
theorem pair_denote_evolvePure (U : Evolution (qubit ⊗ qubit)) (ψ : PureState qubit)
    (φ : PureState (qubit ⊗ qubit)) :
    (pair U).denote.evolvePure (ψ ⊗ φ) = ψ ⊗ (U.evolvePure φ) :=
  Evolution.onRight_evolvePure U qubit ψ φ

end TwoQubitGate3

/-- **The evolution implemented by a two-qubit-gate list**: the monoid product of the gate
denotations, `(gs.map TwoQubitGate3.denote).prod`, in operator order (the leftmost gate is the
leftmost `comp` factor, applied last). -/
def twoQubitCircuit (gs : List TwoQubitGate3) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (gs.map TwoQubitGate3.denote).prod

/-- **The number of two-qubit gates** in a two-qubit-gate circuit. Since every element of the list
is a two-qubit gate, this is simply the list length. -/
def twoQubitCount (gs : List TwoQubitGate3) : ℕ := gs.length

@[simp] theorem twoQubitCircuit_nil : twoQubitCircuit [] = 1 := rfl

/-- The circuit of `g :: gs` applies `g` last: its evolution is `g.denote ∘ (circuit of gs)`. -/
@[simp] theorem twoQubitCircuit_cons (g : TwoQubitGate3) (gs : List TwoQubitGate3) :
    twoQubitCircuit (g :: gs) = g.denote.comp (twoQubitCircuit gs) := by
  rw [twoQubitCircuit, List.map_cons, List.prod_cons, twoQubitCircuit, Evolution.mul_def]

/-- Concatenating circuits composes their evolutions: `twoQubitCircuit (gs ++ hs) = gs-circuit ∘
hs-circuit`, so `hs` acts first. -/
theorem twoQubitCircuit_append (gs hs : List TwoQubitGate3) :
    twoQubitCircuit (gs ++ hs) = (twoQubitCircuit gs).comp (twoQubitCircuit hs) := by
  rw [twoQubitCircuit, List.map_append, List.prod_append, twoQubitCircuit, twoQubitCircuit,
    Evolution.mul_def]

@[simp] theorem twoQubitCount_nil : twoQubitCount [] = 0 := rfl

/-- Each gate adds one to the two-qubit-gate count. -/
@[simp] theorem twoQubitCount_cons (g : TwoQubitGate3) (gs : List TwoQubitGate3) :
    twoQubitCount (g :: gs) = twoQubitCount gs + 1 := by
  rw [twoQubitCount, twoQubitCount, List.length_cons]

/-- Two-qubit-gate counts add over concatenation. -/
theorem twoQubitCount_append (gs hs : List TwoQubitGate3) :
    twoQubitCount (gs ++ hs) = twoQubitCount gs + twoQubitCount hs := by
  rw [twoQubitCount, twoQubitCount, twoQubitCount, List.length_append]

end AxQM
