/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.GateCircuit
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.ControlledUnitaryScalar
import AxQM.Postulates.API.UnitarySquareRoot

/-!
# Nielsen & Chuang, Exercise 4.22 (a `C²(U)` gate needs ≤ 8 one-qubit gates and 6 CNOTs)

*(N&C p. 181.)*

Prove a C^2(U) gate needs at most eight one-qubit gates and six CNOTs.

## The formalisation

The content of the exercise *is* the gate count, so "at most eight
one-qubit gates and six CNOTs" must be a genuine proposition.
We use the typed gate-count circuit model of
`AxQM.Core.GateCircuit` — a `List Gate3` over `qubit ⊗ (qubit ⊗ qubit)` whose
one-qubit / CNOT occurrences are `oneQubitCount` / `cnotCount` and whose denotation is `gateCircuit`
— so the exercise becomes the honest existential

* `ccontrolledUnitary_gateCount_le` — for every single-qubit gate `U`, there is a circuit `gs` with
  `gateCircuit gs = ccontrolledUnitary U`, `oneQubitCount gs ≤ 8` and `cnotCount gs ≤ 6`.

## The construction and why the count is `8 / 6`, not `12 / 8`

Pick `V` with `V² = U` (`Evolution.exists_comp_self_eq`, N&C Fig 4.8's square root) and
ABC-decompose `V` (`Evolution.exists_abc_decomposition`, the gate-level Cor 4.2): `A B C = 1`,
`V.op = e^{iα}(A X B X C)`. The count-optimised circuit `ccontrolledUnitaryMergedCircuit A B C α` is
proved `= C²(V²)` by `ccontrolledUnitaryMergedCircuit_eq`. Naively expanding Figure 4.8's
three controlled-`V`s by Figure 4.6 gives `12` one-qubit gates and `8` CNOTs; because the three
controlled-`V`s target wire `2` while the two structural CNOTs miss it, the junction cancellations
`A A† = 1`, `C† C = 1` save four one-qubit gates (`12 → 8`) and the exposed three-CNOT blocks
collapse (`CNOT(1,2) CNOT(0,1) CNOT(1,2) = CNOT(0,1) CNOT(0,2)`, and mirror) to save two CNOTs
(`8 → 6`). See `ControlledUnitaryScalar` for the combined circuit and its proof.

## Design notes

* **Faithfulness.** `U` is an arbitrary single-qubit gate; `V` is a genuine square
  root, and the bound lives *in* the proposition (`≤ 8`, `≤ 6`), so this is an honest upper bound,
  not a manifest count. Every "one-qubit gate" in `gs` is genuinely a single-qubit unitary on one
  wire, and every CNOT a genuine `Gate3.cnot`.
* **Proof structure.** The circuit's correctness (the eight-basis casework) is proved once
  in `AxQM/Postulates/API/ControlledUnitaryScalar.lean` over a bare `Evolution` product. The
  theorem unfolds the count model's denotation to that product (a cheap `simp`) and applies the
  lemma.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap Matrix

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.22.** For every single-qubit gate `U`, the doubly-controlled gate
`C²(U)` (`ccontrolledUnitary U`) is implemented by a typed circuit `gs` over
`qubit ⊗ (qubit ⊗ qubit)` using **at most eight one-qubit gates and six CNOTs** — the count is a
genuine proposition (`oneQubitCount gs ≤ 8 ∧ cnotCount gs ≤ 6`), an honest upper bound on the number
of gates of each kind. See the module docstring for the construction. -/
theorem ccontrolledUnitary_gateCount_le (U : Evolution qubit) :
    ∃ gs : List Gate3, gateCircuit gs = ccontrolledUnitary U
      ∧ oneQubitCount gs ≤ 8 ∧ cnotCount gs ≤ 6 := by
  -- `V` a square root of `U`, and its gate-level ABC decomposition:
  -- `A B C = 1`, `V.op = e^{iα}(A X B X C)`.
  obtain ⟨V, hVU⟩ := Evolution.exists_comp_self_eq U
  obtain ⟨A, B, C, α, hABC, hVop⟩ := Evolution.exists_abc_decomposition V
  refine ⟨[Gate3.oneQubit 0 (phaseShiftGate α), Gate3.oneQubit 2 A, Gate3.cnot 0 2,
      Gate3.oneQubit 2 B, Gate3.cnot 1 2, Gate3.cnot 0 1,
      Gate3.oneQubit 1 (phaseShiftGate (-α)), Gate3.oneQubit 2 B.adjoint, Gate3.cnot 0 1,
      Gate3.cnot 0 2, Gate3.oneQubit 1 (phaseShiftGate α), Gate3.oneQubit 2 B,
      Gate3.cnot 1 2, Gate3.oneQubit 2 C], ?_, ?_, ?_⟩
  · -- The circuit denotes to the combined Figure-4.8 product, which implements `C²(V²) = C²(U)`.
    rw [← hVU, ← ccontrolledUnitaryMergedCircuit_eq A B C V α hABC hVop]
    simp only [gateCircuit_cons, gateCircuit_nil, Gate3.denote, Gate3.onWire, Gate3.cnotOn,
      cnotGate, ccontrolledUnitaryMergedCircuit]
  · simp
  · simp

end AxQM
