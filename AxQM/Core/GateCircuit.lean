/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary

/-!
# A typed gate-count model for three-qubit circuits (Nielsen & Chuang §4.3)

Nielsen & Chuang's controlled-operation exercises make **gate-count** claims — "a `C²(U)` gate can
be built from at most eight one-qubit gates and six CNOTs" (Exercise 4.22), "reduce the number of
single-qubit gates from three to two" (Exercise 4.23), and so on. To state such a claim *faithfully*
the count must be a genuine proposition about a circuit, not a manifest term the reader tallies by
eye. This file provides the shared vehicle: a typed **circuit** on the three-qubit system
`qubit ⊗ (qubit ⊗ qubit)` (wires `0, 1, 2`) as a `List` of `Gate3`s, each either a one-qubit gate on
a chosen wire or a CNOT on a chosen control/target pair, together with

* `Gate3.denote` / `gateCircuit` — the `Evolution` a gate / gate list implements (the monoid product
  of the gate denotations), so a circuit *means* a concrete unitary; and
* `oneQubitCount` / `cnotCount` — the number of one-qubit / CNOT gates in a list,

turning "`C²(U)` uses at most `m` one-qubit gates and `n` CNOTs" into the honest existential
`∃ gs, gateCircuit gs = C²(U) ∧ oneQubitCount gs ≤ m ∧ cnotCount gs ≤ n` (assembled for `m = 8`,
`n = 6` in Exercise 4.22).

## What is formalised

* `Gate3` — a gate on `qubit ⊗ (qubit ⊗ qubit)`: `oneQubit (wire) (g)` or `cnot (control) (target)`.
* `Gate3.onWire` / `Gate3.cnotOn` — the `Evolution` embeddings of the two gate kinds; `Gate3.denote`
  packages them. `gateCircuit gs = (gs.map Gate3.denote).prod` composes a whole list.
* `oneQubitCount` / `cnotCount` — the two `List.countP` occurrence counts.
* structural rewrites `gateCircuit_nil/cons/append` and `oneQubitCount`/`cnotCount` on `nil`/`cons`/
  `append`, the API a circuit-assembly proof rewrites with.

## Design notes

* **Why `List.prod` over the `Evolution` monoid.** `Evolution` is a `Monoid` under `comp`
  (unit `1`), so `gateCircuit` is literally the list product and inherits `List.prod_cons` /
  `List.prod_append`; the list is read in **operator order** (leftmost gate is the leftmost factor,
  i.e. applied *last*), matching how `Evolution.comp` chains are written (`Exercise4_21`'s
  Figure 4.8 circuit).
* **The wire embeddings (resolving the non-adjacent-CNOT question).** A one-qubit gate reaches wire
  `0/1/2` by `onLeft`/`onRight` nesting. A CNOT reaches the three pairs that occur in the Chapter-4
  constructions without any SWAP conjugation: `(0,1) = C(X on wire 1) = controlledUnitary X.onLeft`
  and — the *non-adjacent* case — `(0,2) = C(X on wire 2) = controlledUnitary (X.onRight)`, because
  `controlledUnitary` controls on wire `0` and can target either sub-wire directly; `(1,2) =
  1 ⊗ CNOT = cnotGate.onRight`. Every other (reversed or diagonal) pair — none of which Chapter 4
  needs — is sent to `1`, keeping `cnotOn` total.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A gate in a three-qubit circuit** on `qubit ⊗ (qubit ⊗ qubit)` (wires `0, 1, 2`): either a
one-qubit gate `g` on a chosen `wire`, or a `CNOT` with a chosen `control` and `target` wire. This
is the syntactic alphabet whose `Gate3.denote`ation is an `Evolution` and whose one-qubit / CNOT
occurrences are counted by `oneQubitCount` / `cnotCount`, so "uses at most `m` one-qubit gates and
`n` CNOTs" becomes a genuine proposition. -/
inductive Gate3 where
  | /-- A one-qubit gate `g` acting on the wire `wire ∈ {0, 1, 2}`. -/
    oneQubit (wire : Fin 3) (g : Evolution qubit)
  | /-- A `CNOT` gate with control wire `control` and target wire `target`. -/
    cnot (control target : Fin 3)

namespace Gate3

/-- **A one-qubit gate on a chosen wire** of `qubit ⊗ (qubit ⊗ qubit)`: `g` is placed on wire `0`
(the left factor), wire `1` (the left sub-factor of the right factor), or wire `2` (the right
sub-factor), the rest idle, via `Evolution.onLeft`/`onRight` nesting. -/
def onWire : Fin 3 → Evolution qubit → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | 0, g => g.onLeft (qubit ⊗ qubit)
  | 1, g => (g.onLeft qubit).onRight qubit
  | _, g => (g.onRight qubit).onRight qubit

/-- **A CNOT on a chosen control/target pair** of `qubit ⊗ (qubit ⊗ qubit)`. The three pairs that
occur in Chapter 4 are realised without a SWAP: `(0,1)` and `(0,2)` control on wire `0` and target
wire `1`/`2` via `controlledUnitary (X.onLeft/onRight)`, and `(1,2) = 1 ⊗ CNOT` via
`cnotGate.onRight`. Every other pair (reversed or diagonal — unused) is sent to the identity `1`. -/
def cnotOn : Fin 3 → Fin 3 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | 0, 1 => controlledUnitary (pauliXGate.onLeft qubit)
  | 0, 2 => controlledUnitary (pauliXGate.onRight qubit)
  | 1, 2 => cnotGate.onRight qubit
  | _, _ => 1

/-- **The `Evolution` denoted by a single gate**: the wire embedding of a one-qubit gate, or the
control/target embedding of a CNOT. -/
def denote : Gate3 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | oneQubit w g => onWire w g
  | cnot c t => cnotOn c t

/-- Whether a gate is a one-qubit gate (used by `oneQubitCount`). -/
def isOneQubit : Gate3 → Bool
  | oneQubit .. => true
  | cnot .. => false

/-- Whether a gate is a CNOT gate (used by `cnotCount`). -/
def isCnot : Gate3 → Bool
  | oneQubit .. => false
  | cnot .. => true

end Gate3

/-- **The evolution implemented by a gate list**: the monoid product of the gate denotations,
`(gs.map Gate3.denote).prod`, in operator order (the leftmost gate is the leftmost `comp` factor,
applied last). -/
def gateCircuit (gs : List Gate3) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (gs.map Gate3.denote).prod

/-- **The number of one-qubit gates** in a circuit. -/
def oneQubitCount (gs : List Gate3) : ℕ := gs.countP Gate3.isOneQubit

/-- **The number of CNOT gates** in a circuit. -/
def cnotCount (gs : List Gate3) : ℕ := gs.countP Gate3.isCnot

@[simp] theorem gateCircuit_nil : gateCircuit [] = 1 := rfl

/-- The circuit of `g :: gs` applies `g` last: its evolution is `g.denote ∘ (circuit of gs)`. -/
@[simp] theorem gateCircuit_cons (g : Gate3) (gs : List Gate3) :
    gateCircuit (g :: gs) = g.denote.comp (gateCircuit gs) := by
  rw [gateCircuit, List.map_cons, List.prod_cons, gateCircuit, Evolution.mul_def]

/-- Concatenating circuits composes their evolutions: `gateCircuit (gs ++ hs) = gs-circuit ∘
hs-circuit`, so `hs` acts first. -/
theorem gateCircuit_append (gs hs : List Gate3) :
    gateCircuit (gs ++ hs) = (gateCircuit gs).comp (gateCircuit hs) := by
  rw [gateCircuit, List.map_append, List.prod_append, gateCircuit, gateCircuit, Evolution.mul_def]

@[simp] theorem oneQubitCount_nil : oneQubitCount [] = 0 := rfl

@[simp] theorem cnotCount_nil : cnotCount [] = 0 := rfl

/-- A one-qubit gate adds one to the one-qubit count. -/
@[simp] theorem oneQubitCount_cons_oneQubit (w : Fin 3) (g : Evolution qubit) (gs : List Gate3) :
    oneQubitCount (Gate3.oneQubit w g :: gs) = oneQubitCount gs + 1 := by
  simp [oneQubitCount, List.countP_cons, Gate3.isOneQubit]

/-- A CNOT gate does not change the one-qubit count. -/
@[simp] theorem oneQubitCount_cons_cnot (c t : Fin 3) (gs : List Gate3) :
    oneQubitCount (Gate3.cnot c t :: gs) = oneQubitCount gs := by
  simp [oneQubitCount, Gate3.isOneQubit]

/-- A CNOT gate adds one to the CNOT count. -/
@[simp] theorem cnotCount_cons_cnot (c t : Fin 3) (gs : List Gate3) :
    cnotCount (Gate3.cnot c t :: gs) = cnotCount gs + 1 := by
  simp [cnotCount, List.countP_cons, Gate3.isCnot]

/-- A one-qubit gate does not change the CNOT count. -/
@[simp] theorem cnotCount_cons_oneQubit (w : Fin 3) (g : Evolution qubit) (gs : List Gate3) :
    cnotCount (Gate3.oneQubit w g :: gs) = cnotCount gs := by
  simp [cnotCount, Gate3.isCnot]

/-- One-qubit counts add over concatenation. -/
theorem oneQubitCount_append (gs hs : List Gate3) :
    oneQubitCount (gs ++ hs) = oneQubitCount gs + oneQubitCount hs := by
  rw [oneQubitCount, oneQubitCount, oneQubitCount, List.countP_append]

/-- CNOT counts add over concatenation. -/
theorem cnotCount_append (gs hs : List Gate3) :
    cnotCount (gs ++ hs) = cnotCount gs + cnotCount hs := by
  rw [cnotCount, cnotCount, cnotCount, List.countP_append]

end AxQM
