/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.LeftPairGate

/-!
# AxQM.Postulates.API — a single-qubit/`CNOT` circuit for a two-level unitary (N&C Ex 4.39)

This file treats **Nielsen & Chuang, Exercise 4.39** (§4.5.2, p. 193): a circuit built from
single-qubit and `CNOT` gates that implements the three-qubit *two-level* unitary (eq. 4.60)

```
        ⎡ 1 0 0 0 0 0 0 0 ⎤
        ⎢ 0 1 0 0 0 0 0 0 ⎥
        ⎢ 0 0 a 0 0 0 0 c ⎥
        ⎢ 0 0 0 1 0 0 0 0 ⎥
   U =  ⎢ 0 0 0 0 1 0 0 0 ⎥
        ⎢ 0 0 0 0 0 1 0 0 ⎥
        ⎢ 0 0 0 0 0 0 1 0 ⎥
        ⎣ 0 0 b 0 0 0 0 d ⎦
```

acting non-trivially only on the two computational-basis states `|010⟩` (index `2`) and `|111⟩`
(index `7`), through the arbitrary `2 × 2` unitary `Ũ = !![a, c; b, d]`.

## The construction (Nielsen & Chuang's Gray-code method)

`U` couples the two basis states `s = 010` and `t = 111`, which differ in qubits 1 and 3. Following
N&C §4.5.2 we conjugate the standard doubly-controlled gate `C²(Ũ) = ccontrolledUnitary Ũ` — which
implements exactly this two-level action on the *adjacent* pair `{|110⟩, |111⟩}` (apply `Ũ` to
qubit 3 when qubits 1, 2 are `|1⟩`) — by a permutation `twoLevelRoute` that relabels
`{|110⟩, |111⟩}` to the target pair `{|010⟩, |111⟩}`:

```
   twoLevelUnitaryCircuit Ũ  =  W · C²(Ũ) · W,      W = twoLevelRoute.
```

`W` maps `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂ ⊕ q₃, q₂, q₃⟩` — it XORs `q₂ ⊕ q₃` into qubit 1 — and is an
involution, so no separate inverse is needed. In particular `W|010⟩ = |110⟩`, `W|110⟩ = |010⟩` and
`W` fixes `|111⟩`. Sandwiching `C²(Ũ)` between two copies of `W` therefore carries the coupled pair
from `{|110⟩, |111⟩}` back to `{|010⟩, |111⟩}`, giving exactly (4.60). `W` is realised as three
`CNOT`s (`reversedCNOT₃→₂ · reversedCNOT₂→₁ · reversedCNOT₃→₂`), and `C²(Ũ)` decomposes further into
single-qubit and `CNOT` gates by Exercise 4.22 — so the whole circuit is built from single-qubit and
`CNOT` gates, as the exercise asks.

## What is formalised

* `twoLevelRoute` — the routing permutation `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂ ⊕ q₃, q₂, q₃⟩`, a product of
  three `CNOT`s, with truth table `twoLevelRoute_evolvePure_qubitBasis`.
* `twoLevelUnitaryCircuit Ũ` — the circuit `W · C²(Ũ) · W` on `qubit ⊗ (qubit ⊗ qubit)`.
* `twoLevelUnitaryCircuit_evolvePure_inactive` — the six computational-basis states other than
  `|010⟩` and `|111⟩` are fixed (the identity blocks of (4.60)).
* `twoLevelUnitaryCircuit_evolvePure_active_ketZero` / `..._active_ketOne` — the coupled pair:
  `U|010⟩ = a • |010⟩ + b • |111⟩` and `U|111⟩ = c • |010⟩ + d • |111⟩`, where the entries
  `a, b, c, d` of `Ũ` are read off from its action `Ũ|0⟩ = a|0⟩ + b|1⟩`, `Ũ|1⟩ = c|0⟩ + d|1⟩` (the
  two columns of `Ũ`). These are exactly columns 2 and 7 of (4.60).

## Design notes

* **Statement shape / N&C fidelity.** (4.60) is the two-level unitary with `2 × 2` block `Ũ` on the
  pair `{|010⟩, |111⟩}`. We give its full action: the six inactive basis states are fixed and the
  two active ones acquire the amplitudes `a, b` / `c, d` of `Ũ`. This is the complete truth table of
  (4.60), not a weaker surrogate, for an *arbitrary* single-qubit gate `Ũ` (the entries constrained
  only through `Ũ`'s own action). Any circuit whose action equals (4.60) answers the exercise; ours
  is the Gray-code circuit of N&C's own universality construction.
* **Why `.vec`.** The active-state amplitudes `a • |010⟩ + b • |111⟩` are
  a genuine superposition, and `PureState` is a bare unit vector with no `+`/`•`; the honest way to
  state "amplitude `a` on `|010⟩`, `b` on `|111⟩`" is at the underlying-vector level (`.vec`).
  The statement of Exercise 4.39 is in `AxQM/NC/Ch4/Exercise4_39.lean`.
* **Proof route.** The routing truth table is the `threeQubit` unfold-and-`fin_cases` computation of
  the other circuit exercises. For the active states we use `twoLevelRoute`'s truth table as a black
  box: `W|010⟩ = |110⟩`, then `C²(Ũ)|110⟩ = |11⟩ ⊗ Ũ|0⟩` (the doubly-controlled action), then expand
  `Ũ|0⟩ = a|0⟩ + b|1⟩` at the `.vec` level so the final `W` — linear on vectors — distributes over
  the two basis components `a • |110⟩ + b • |111⟩`, landing on `a • |010⟩ + b • |111⟩` via
  `W|110⟩ = |010⟩`, `W|111⟩ = |111⟩`. The six inactive states use that `W` is an involution
  (`W(W s) = s`) and that `C²(Ũ)` fixes `W s` (its two controls are not both `|1⟩`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The routing permutation -/

/-- **The routing permutation** `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂ ⊕ q₃, q₂, q₃⟩` on
`qubit ⊗ (qubit ⊗ qubit)`, a product of three `CNOT`s
(`reversedCNOT₃→₂ · reversedCNOT₂→₁ · reversedCNOT₃→₂`) that XORs `q₂ ⊕ q₃` into qubit 1. It is an
involution and relabels the adjacent pair `{|110⟩, |111⟩}` (on which `C²(Ũ)` acts) to the target
pair `{|010⟩, |111⟩}` of (4.60): `|010⟩ ↔ |110⟩`, `|111⟩` fixed. -/
def twoLevelRoute : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (reversedCnotGate.onRight qubit).comp
    (reversedCnotLeftGate.comp (reversedCnotGate.onRight qubit))

/-- **Routing truth table:** `twoLevelRoute|q₁, q₂, q₃⟩ = |q₁ ⊕ q₂ ⊕ q₃, q₂, q₃⟩`. The two
`reversedCNOT₃→₂`s XOR `q₃` into qubit 2 and back, leaving qubit 1 flipped by `q₂ ⊕ q₃` via the
intervening `reversedCNOT₂→₁`. -/
theorem twoLevelRoute_evolvePure_qubitBasis (q1 q2 q3 : Fin 2) :
    twoLevelRoute.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis (q1 + q2 + q3)) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)) := by
  rw [twoLevelRoute, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.onRight_evolvePure, reversedCnotGate_evolvePure_qubitBasis,
    reversedCnotLeftGate_evolvePure_qubitBasis, Evolution.onRight_evolvePure,
    reversedCnotGate_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;> rfl

/-- **`twoLevelRoute` is an involution:** applying it twice is the identity, `W(W ψ) = ψ` on
computational-basis states. Used to fix the inactive basis states of the circuit. -/
theorem twoLevelRoute_evolvePure_twoLevelRoute_qubitBasis (q1 q2 q3 : Fin 2) :
    twoLevelRoute.evolvePure (twoLevelRoute.evolvePure
        ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3))))
      = (qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)) := by
  rw [twoLevelRoute_evolvePure_qubitBasis, twoLevelRoute_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;> rfl

/-! ### The circuit -/

/-- **The Exercise 4.39 circuit.** The two-level unitary (4.60) on `qubit ⊗ (qubit ⊗ qubit)`, built
as the doubly-controlled gate `C²(Ũ) = ccontrolledUnitary Ũ` conjugated by the routing permutation
`twoLevelRoute`: `twoLevelUnitaryCircuit Ũ = W · C²(Ũ) · W`. Built from single-qubit and `CNOT`
gates (three `CNOT`s in each `W`, and `C²(Ũ)` decomposes further, Exercise 4.22). -/
def twoLevelUnitaryCircuit (u : Evolution qubit) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  twoLevelRoute.comp ((ccontrolledUnitary u).comp twoLevelRoute)

/-- **The inactive block of (4.60).** Every computational-basis state other than the coupled pair
`|010⟩`, `|111⟩` is left unchanged by the circuit: for `(q₁, q₂, q₃) ≠ (0, 1, 0)` and `≠ (1, 1, 1)`,
`twoLevelUnitaryCircuit Ũ |q₁, q₂, q₃⟩ = |q₁, q₂, q₃⟩`. These are the six identity columns of
(4.60).
The routing sends such a state where `C²(Ũ)`'s two controls are not both `|1⟩`, so `C²(Ũ)` fixes it,
and the two `W`s cancel (`W` is an involution). -/
theorem twoLevelUnitaryCircuit_evolvePure_inactive (u : Evolution qubit) (q1 q2 q3 : Fin 2)
    (h : ¬ (q1 = 0 ∧ q2 = 1 ∧ q3 = 0) ∧ ¬ (q1 = 1 ∧ q2 = 1 ∧ q3 = 1)) :
    (twoLevelUnitaryCircuit u).evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)) := by
  obtain ⟨h1, h2⟩ := h
  rw [twoLevelUnitaryCircuit, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    twoLevelRoute_evolvePure_qubitBasis]
  -- `C²(Ũ)` fires only when both controls (qubits 1, 2 of the routed state) are `|1⟩`,
  -- i.e. `q₁ ⊕ q₂ ⊕ q₃ = 1` and `q₂ = 1`; the two inactive-excluded cases are exactly those.
  have hfix : (ccontrolledUnitary u).evolvePure
      ((qubitBasis (q1 + q2 + q3)) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis (q1 + q2 + q3)) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)) := by
    fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
      first
        | exact absurd ⟨rfl, rfl, rfl⟩ h1
        | exact absurd ⟨rfl, rfl, rfl⟩ h2
        | simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceAdd,
            ccontrolledUnitary_evolvePure_ketZero_left,
            ccontrolledUnitary_evolvePure_ketOne_left, controlledUnitary_evolvePure_ketZero]
  rw [hfix]
  have := twoLevelRoute_evolvePure_twoLevelRoute_qubitBasis q1 q2 q3
  rwa [twoLevelRoute_evolvePure_qubitBasis] at this

/-! ### The coupled pair (columns 2 and 7 of (4.60)) -/

/-- **Routing a `|1, 1, ·⟩` superposition** — the shared linear-algebra tail of the two
coupled-column proofs. Applied (through its operator) to `|1⟩ ⊗ |1⟩ ⊗ (s|0⟩ + t|1⟩)`, the routing
`W` lands on `s • |010⟩ + t • |111⟩`: on basis states it copies qubit 3 into qubit 1
(`W|110⟩ = |010⟩`, `W|111⟩ = |111⟩`), so by linearity the two components `s • |110⟩`, `t • |111⟩`
separate. Distribution is proved as the raw-headed `hvecdist` and the goal closed by rewriting its
right side back through `map_add`/`map_smul` and the two basis actions, so `.op` faces the sum
(`congrArg` then bridges the composite-vs-raw tensor head by defeq). -/
theorem twoLevelRoute_op_ketOneOne_superpos (s t : ℂ) :
    twoLevelRoute.op ((qubitBasis 1).vec ⊗ₜ[ℂ]
        ((qubitBasis 1).vec ⊗ₜ[ℂ] (s • (qubitBasis 0).vec + t • (qubitBasis 1).vec)))
      = s • ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0))).vec
        + t • ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1))).vec := by
  have hW110 : twoLevelRoute.evolvePure ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0)))
      = (qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0)) := by
    rw [twoLevelRoute_evolvePure_qubitBasis]; rfl
  have hW111 : twoLevelRoute.evolvePure ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1)))
      = (qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1)) := by
    rw [twoLevelRoute_evolvePure_qubitBasis]; rfl
  have hop110 : twoLevelRoute.op
        ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec))
      = ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0))).vec := by
    rw [← PureState.tmul_vec, ← PureState.tmul_vec, ← Evolution.evolvePure_vec, hW110]
  have hop111 : twoLevelRoute.op
        ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec))
      = ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1))).vec := by
    rw [← PureState.tmul_vec, ← PureState.tmul_vec, ← Evolution.evolvePure_vec, hW111]
  have hvecdist : (qubitBasis 1).vec ⊗ₜ[ℂ]
        ((qubitBasis 1).vec ⊗ₜ[ℂ] (s • (qubitBasis 0).vec + t • (qubitBasis 1).vec))
      = s • ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec))
        + t • ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec)) := by
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  calc twoLevelRoute.op ((qubitBasis 1).vec ⊗ₜ[ℂ]
          ((qubitBasis 1).vec ⊗ₜ[ℂ] (s • (qubitBasis 0).vec + t • (qubitBasis 1).vec)))
      = twoLevelRoute.op
          (s • ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec))
            + t • ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec))) :=
        congrArg twoLevelRoute.op hvecdist
    _ = twoLevelRoute.op
          (s • ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec)))
          + twoLevelRoute.op
              (t • ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec))) :=
        map_add _ _ _
    _ = s • twoLevelRoute.op ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
        0).vec))
          + t • twoLevelRoute.op
              ((qubitBasis 1).vec ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec)) :=
        congrArg₂ (· + ·) (map_smul twoLevelRoute.op s _) (map_smul twoLevelRoute.op t _)
    _ = s • ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0))).vec
          + t • ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1))).vec := by
        rw [hop110, hop111]

/-- **Column 2 of (4.60):** the circuit sends `|010⟩` to `a • |010⟩ + b • |111⟩`, where `a, b` are
the first column of `Ũ` (`Ũ|0⟩ = a|0⟩ + b|1⟩`). Routing sends `|010⟩ ↦ |110⟩`, then `C²(Ũ)` applies
`Ũ` to qubit 3 giving `|11⟩ ⊗ Ũ|0⟩`; expanding `Ũ|0⟩ = a|0⟩ + b|1⟩` and routing back (linearly)
lands on `a • |010⟩ + b • |111⟩`. -/
theorem twoLevelUnitaryCircuit_evolvePure_active_ketZero (u : Evolution qubit) (a b : ℂ)
    (hu0 : (u.evolvePure (qubitBasis 0)).vec
      = a • (qubitBasis 0).vec + b • (qubitBasis 1).vec) :
    ((twoLevelUnitaryCircuit u).evolvePure
        ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0)))).vec
      = a • ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0))).vec
        + b • ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1))).vec := by
  have hW010 : twoLevelRoute.evolvePure ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0)))
      = (qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0)) := by
    rw [twoLevelRoute_evolvePure_qubitBasis]; rfl
  rw [twoLevelUnitaryCircuit, Evolution.evolvePure_comp, Evolution.evolvePure_comp, hW010,
    ccontrolledUnitary_evolvePure_ketOne_left, controlledUnitary_evolvePure_ketOne,
    Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec, hu0]
  exact twoLevelRoute_op_ketOneOne_superpos a b

/-- **Column 7 of (4.60):** the circuit sends `|111⟩` to `c • |010⟩ + d • |111⟩`, where `c, d` are
the second column of `Ũ` (`Ũ|1⟩ = c|0⟩ + d|1⟩`). Routing fixes `|111⟩`, then `C²(Ũ)` applies `Ũ` to
qubit 3 giving `|11⟩ ⊗ Ũ|1⟩`; expanding `Ũ|1⟩ = c|0⟩ + d|1⟩` and routing back lands on
`c • |010⟩ + d • |111⟩`. -/
theorem twoLevelUnitaryCircuit_evolvePure_active_ketOne (u : Evolution qubit) (c d : ℂ)
    (hu1 : (u.evolvePure (qubitBasis 1)).vec
      = c • (qubitBasis 0).vec + d • (qubitBasis 1).vec) :
    ((twoLevelUnitaryCircuit u).evolvePure
        ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1)))).vec
      = c • ((qubitBasis 0) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 0))).vec
        + d • ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1))).vec := by
  have hW111 : twoLevelRoute.evolvePure ((qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1)))
      = (qubitBasis 1) ⊗ ((qubitBasis 1) ⊗ (qubitBasis 1)) := by
    rw [twoLevelRoute_evolvePure_qubitBasis]; rfl
  rw [twoLevelUnitaryCircuit, Evolution.evolvePure_comp, Evolution.evolvePure_comp, hW111,
    ccontrolledUnitary_evolvePure_ketOne_left, controlledUnitary_evolvePure_ketOne,
    Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec, hu1]
  exact twoLevelRoute_op_ketOneOne_superpos c d

end AxQM
