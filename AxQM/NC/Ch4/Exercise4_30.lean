/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction
import AxQM.Core.BarencoLayerBudget
import AxQM.Postulates.API.UnitarySquareRoot
import AxQM.Concrete.MultiControlledNotAsymptotics

/-!
# Nielsen & Chuang, Exercise 4.30 — a `Cⁿ(U)` circuit for general `n` using no work qubits

**Exercise 4.30.** *Suppose `U` is a single-qubit unitary operation. Find a circuit containing
`O(n²)` Toffoli, CNOT and single qubit gates which implements a `Cⁿ(U)` gate (for `n > 3`), using
no work qubits.*

This is the arbitrary-`n` generalisation of Exercise 4.28 (which assembled the `n = 5` case,
`barenco5Circuit`). Where 4.28 fixed the tower depth at four and supplied the four square roots
explicitly, here the construction is an honest recursion in `n`, and the whole square-root chain is
produced from `Evolution.exists_comp_self_eq` so the statement holds for *every* single-qubit `U`.

## The construction

The heart is again the Barenco reduction `mcCtrl_controlledUnitary_sq`
(`AxQM/Core/MultiControlledReduction.lean`), the no-work-qubit generalisation of Figure 4.8:
`Cᵏ⁺¹(W²) = Cᵏ(W) · Cᵏ(X) · C(W†) · Cᵏ(X) · C(W)`, split by
`barencoReductionCircuit_eq_mux_comp_tail` as a leading multiplexer `Cᵏ(W)` composed with a tail
`barencoTail k W = Cᵏ(X) · C(W†) · Cᵏ(X) · C(W)`. Applying it once peels one control off `Cⁿ(U)`
(with a fresh root `√U`); the surviving multiplexer `Cⁿ⁻¹(√U)` is again a square (of the *next*
root), so the reduction applies once more, and so on, until the innermost multiplexer is
single-controlled. The fully unfolded circuit `barencoNCircuit` is therefore a nested stack of
tails whose leading multiplexers have all been expanded — built only from single-qubit-controlled
gates (`C(Vⱼ)`, `C(Vⱼ†)`) and multiply-controlled `NOT`s (`Cᵏ(X)`), every gate acting on the
`(n+1)`-qubit register `qtower k (qubit ⊗ qubit)` with **no ancilla**.

## The `O(n²)` gate count

Beyond the circuit *identity*, the exercise names an `O(n²)` count of `Toffoli`, `CNOT` and
single-qubit gates. That count is proved here in full, on exactly the `n + 1`-wire register with
**no work qubit**, using the compositional gate accountant `CircuitBudget`
(`AxQM/Core/CircuitBudget.lean`):

* `barencoNCircuit_circuitBudget` — the whole-circuit fold, for **every** single-qubit square-root
  chain `V`: `CircuitBudget (barencoNCircuit V k d) (8·k·(k+1)+2) (2·k+3)`, i.e. the circuit is
  built from at most `8k(k+1)+2 = O(k²)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and at most
  `2k+3 = O(k)` single-qubit(-controlled) gates. It sums the per-layer budgets
  (`barencoTail_circuitBudget`, `barencoReductionCircuit_zero_circuitBudget` — both in
  `AxQM/Core/BarencoLayerBudget.lean`) across the `O(n)`-layer recursion via
  `CircuitBudget.comp`/`.cast_congr`,
  each internal `Cᵏ(X)` block already bottomed to a **classical `≤ 2`-control gate list** on the
  tight register (Exercise 4.29's linear `Cᵏ(X)` reduction — `O(k)` `Toffoli`s per block, summing
  to the `O(n²)` total).
* `mcCtrl_controlledUnitary_circuitBudget` — that budget transported onto `Cⁿ(U)` itself, for every
  single-qubit `U`: `CircuitBudget (Cⁿ(U)) (8k(k+1)+2) (2k+3)`.

The `O(n²)` read-off of the two counts is the physics-free `ℕ→ℝ` asymptotic
`Concrete.barencoGateBudget_isBigO_sq` (`(8k(k+1)+2)+(2k+3) =O[atTop] k²`, in
`AxQM/Concrete/MultiControlledNotAsymptotics.lean`). **Scope of the "single qubit gates" bucket
(honest, exactly as Exercise 4.29):** the `2k+3` gates it counts are the `√U`-chain *controlled*
gates `C(Vⱼ)`, `C(Vⱼ†)` and the base multiplexer `V₀`; a controlled-single-qubit gate is not
literally one of `{Toffoli, CNOT, single-qubit}` but is a **constant** number of `CNOT` +
single-qubit gates (Exercise 4.22 / Figure 4.6, the ABC decomposition — this is what §4.3 means by
building controlled gates from `CNOT` and single-qubit gates). As there are only `O(n)` of them, the
grand total in the exercise's own gate set stays `O(n²)`; bottoming those `O(n)` gates to the
literal three-gate basis is a cosmetic `O(1)`-per-gate expansion left un-inlined, exactly as
Exercise 4.28/4.29 leave their `C(Vⱼ)`, and the multiply-controlled `NOT`s stay `mcCtrl k
(pauliXGate.onLeft _)` inside the `block` leaves.

## The reassociation

For symbolic `n` the register bookkeeping is the only new difficulty over 4.28. Peeling a control
turns the target module `M` into `qubit ⊗ M`, so the recursive circuit lives on
`qtower k (qubit ⊗ (qubit ⊗ M))` while its parent lives on `qtower (k+1) (qubit ⊗ M)`. These are the
*same* register — `qtower m (qubit ⊗ S) = qtower (m+1) S` — but only propositionally
(`qtower_qubit_comm`), because `qtower` recurses on its first argument. The one honest cast this
forces is isolated in `mcCtrl_succ_inner` (moving a control from the outside of `mcCtrl` into a
`controlledUnitary`), proved by a short induction on top of `controlledUnitary_cast`; the `n = 5`
case avoided it only because its indices were numerals (the equality was then definitional). These
three reassociation lemmas are in `AxQM/Core/MultiControlledReduction.lean` alongside
`mcCtrl_succ`.

## Ingredients

The statements use `mcCtrl`, `unCtrl`, `controlledUnitary`, `pauliXGate`,
`Evolution.onRight`/`onLeft`/`comp`/`adjoint` and `ℕ`/`QSystem` data. The general circuit
`barencoNCircuit` is the Exercise 4.30 circuit itself, expressed via the helpers
`barencoReductionCircuit` / `barencoTail` (and the register-reassociation lemmas), all in
`AxQM/Core/MultiControlledReduction.lean`, giving it a transparent, layer-by-layer shape.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The general no-work-qubit circuit -/

/-- **The Exercise 4.30 circuit** for `C^(k+1)(U)`, `U = (V 1)²`, with no work qubits. Given the
single-qubit square-root chain `V : ℕ → Evolution qubit` (with `(V (j+1))² = V j`), `barencoNCircuit
V k d` is the fully unfolded `k`-level Barenco reduction on `qtower k (qubit ⊗ qtower d qubit)`,
where `d` is the current depth (the number of already-peeled controls now idle in the target
module). The recursion expands the leading multiplexer of each layer:

* depth `d`, level `0`: the single-controlled reduction
  `barencoReductionCircuit 0 (unCtrl d (V (d+1)))`;
* depth `d`, level `k+1`: the deeper circuit (at depth `d+1`, reassociated onto the parent register
  by `qtower_qubit_comm`) composed with this layer's tail `barencoTail (k+1) (unCtrl d (V (d+1)))`.

Every root `V (d+1)` is a single-qubit gate lifted `d` times by idle wraps (`unCtrl d`) so that it
targets the innermost qubit. The whole circuit is thus built only from single-qubit-controlled gates
`C(Vⱼ)`, `C(Vⱼ†)` and multiply-controlled `NOT`s `Cᵏ(X)` — no ancilla. -/
def barencoNCircuit (V : ℕ → Evolution qubit) :
    (k d : ℕ) → Evolution (qtower k (qubit ⊗ qtower d qubit))
  | 0, d => barencoReductionCircuit 0 (unCtrl d (V (d + 1)))
  | k + 1, d =>
      (cast (congrArg Evolution (qtower_qubit_comm k (qubit ⊗ qtower d qubit)))
          (barencoNCircuit V k (d + 1))).comp
        (barencoTail (k + 1) (unCtrl d (V (d + 1))))

/-- Definitional unfolding of `barencoNCircuit` at level `0`. -/
theorem barencoNCircuit_zero (V : ℕ → Evolution qubit) (d : ℕ) :
    barencoNCircuit V 0 d = barencoReductionCircuit 0 (unCtrl d (V (d + 1))) := rfl

/-- Definitional unfolding of `barencoNCircuit` at level `k+1`: the reassociated deeper circuit
composed with this layer's Barenco tail. -/
theorem barencoNCircuit_succ (V : ℕ → Evolution qubit) (k d : ℕ) :
    barencoNCircuit V (k + 1) d
      = (cast (congrArg Evolution (qtower_qubit_comm k (qubit ⊗ qtower d qubit)))
            (barencoNCircuit V k (d + 1))).comp
          (barencoTail (k + 1) (unCtrl d (V (d + 1)))) := rfl

/-! ### The `O(n²)` gate budget of the circuit -/

/-- **Nielsen & Chuang, Exercise 4.30 — the whole-circuit gate budget.** For **every** single-qubit
square-root chain `V`, the fully unfolded circuit `barencoNCircuit V k d` has

`CircuitBudget (barencoNCircuit V k d) (8·k·(k+1) + 2) (2·k + 3)`,

i.e. it is built — up to register isomorphism, on exactly the `n + 1`-wire tower with **no work
qubit** — from at most `8k(k+1) + 2 = O(k²)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and at
most `2k + 3 = O(k)` single-qubit(-controlled) gates. This is the fold that makes the per-layer
counts **add** across the recursion: by induction on the number of controls `k` (generalising
the depth `d`), the base (`barencoNCircuit V 0 d = barencoReductionCircuit 0 …`) costs `(2, 3)`
(`barencoReductionCircuit_zero_circuitBudget`), and each step layer `barencoTail (k+1) …` costs
`(16(k+1), 2)` (`barencoTail_circuitBudget`), glued to the reassociated deeper circuit through
`CircuitBudget.cast_congr` (the `qtower_qubit_comm` register cast of `barencoNCircuit_succ`) and
summed by `CircuitBudget.comp`; the running totals `2 + Σⱼ₌₁ᵏ 16j = 8k(k+1) + 2` and `3 + 2k` close
the induction (`ring`). No constructor of `CircuitBudget` lowers a count, so this is an honest
**upper** bound. (Together with `mcCtrl_controlledUnitary_circuitBudget` this supplies the
exercise's `O(n²)` count; the sibling Exercise 4.29 specialises it to `U = X`.) -/
theorem barencoNCircuit_circuitBudget (V : ℕ → Evolution qubit) :
    ∀ k d : ℕ,
      CircuitBudget (barencoNCircuit V k d) (8 * k * (k + 1) + 2) (2 * k + 3) := by
  intro k
  induction k with
  | zero => intro d; exact barencoReductionCircuit_zero_circuitBudget d (V (d + 1))
  | succ k ih =>
    intro d
    rw [barencoNCircuit_succ]
    refine ((CircuitBudget.cast_congr
          (qtower_qubit_comm k (qubit ⊗ qtower d qubit)) (ih (d + 1))).comp
        (barencoTail_circuitBudget (k + 1) d (by omega) (V (d + 1)))).mono
      (le_of_eq ?_) (le_of_eq ?_)
    · ring
    · ring

/-- **Nielsen & Chuang, Exercise 4.30 (the assembled construction, explicit chain).** For a
single-qubit square-root chain `V` with `(V (j+1))² = V j`, the multiplexer
`C^(k+1)((V (d+1))²)` on the register with `d` idle target qubits equals the explicit no-work-qubit
circuit `barencoNCircuit V k d`.

Proof: induction on the number of controls `k`, generalising the depth `d`. The base
(`k = 0`) is one Barenco reduction (`mcCtrl_controlledUnitary_sq 0`). The step reduces the top layer
(`mcCtrl_controlledUnitary_sq (k+1)`), splits off its tail
(`barencoReductionCircuit_eq_mux_comp_tail`), moves the surviving multiplexer's outer control inside
(`mcCtrl_succ_inner`) so it matches the reassociated recursive circuit, then rewrites the deeper
square `(unCtrl (d+1) (V (d+2)))²` to `(unCtrl d (V (d+1))).onRight qubit` via `unCtrl_comp`, the
chain hypothesis, and `unCtrl_succ`, closing on the inductive hypothesis at depth `d+1`. -/
theorem barencoNCircuit_eq_mcCtrl (V : ℕ → Evolution qubit)
    (hV : ∀ j, (V (j + 1)).comp (V (j + 1)) = V j) :
    ∀ (k d : ℕ),
      mcCtrl k (controlledUnitary ((unCtrl d (V (d + 1))).comp (unCtrl d (V (d + 1)))))
        = barencoNCircuit V k d := by
  intro k
  induction k with
  | zero =>
    intro d
    exact mcCtrl_controlledUnitary_sq 0 (unCtrl d (V (d + 1)))
  | succ k ih =>
    intro d
    -- The deeper multiplexer, after re-indexing its square via the chain, is the recursive circuit.
    have hinner : mcCtrl k (controlledUnitary ((unCtrl d (V (d + 1))).onRight qubit))
        = barencoNCircuit V k (d + 1) := by
      rw [← unCtrl_succ, ← hV (d + 1), ← unCtrl_comp]
      exact ih (d + 1)
    rw [mcCtrl_controlledUnitary_sq (k + 1) (unCtrl d (V (d + 1))),
      barencoReductionCircuit_eq_mux_comp_tail, barencoNCircuit_succ, mcCtrl_succ_inner, hinner]

/-- **Nielsen & Chuang, Exercise 4.30 (top level).** Specialising `barencoNCircuit_eq_mcCtrl` to
depth `d = 0`: for a single-qubit square-root chain `V`, the plain multiplexer `C^(k+1)(V 0)` equals
the no-work-qubit circuit `barencoNCircuit V k 0`. (Here `n = k + 1` is the control count.) -/
theorem barencoNCircuit_zero_eq_mcCtrl (V : ℕ → Evolution qubit)
    (hV : ∀ j, (V (j + 1)).comp (V (j + 1)) = V j) (k : ℕ) :
    mcCtrl k (controlledUnitary (V 0)) = barencoNCircuit V k 0 := by
  -- Rewrite the clean goal (`V 0` is `unCtrl`-free) and close by defeq (`unCtrl 0 X ≡ X`).
  rw [← hV 0]
  exact barencoNCircuit_eq_mcCtrl V hV k 0

/-- **The square-root chain** of a single-qubit gate `U`: `sqrtChain U 0 = U`, and each
`sqrtChain U (j+1)` is a chosen unitary square root of `sqrtChain U j` (from
`Evolution.exists_comp_self_eq`). Every single-qubit gate has a square root, so the chain is total;
it supplies the roots `V₁ = U`, `V₂ = √U`, `V₃ = √√U`, … that the Barenco unfolding of `Cⁿ(U)`
consumes, with no square-root hypotheses on `U`. -/
noncomputable def sqrtChain (U : Evolution qubit) : ℕ → Evolution qubit
  | 0 => U
  | j + 1 => (Evolution.exists_comp_self_eq (sqrtChain U j)).choose

@[simp] theorem sqrtChain_zero (U : Evolution qubit) : sqrtChain U 0 = U := rfl

/-- Each step of `sqrtChain` squares back to the previous:
`(sqrtChain U (j+1))² = sqrtChain U j`. -/
theorem sqrtChain_sq (U : Evolution qubit) (j : ℕ) :
    (sqrtChain U (j + 1)).comp (sqrtChain U (j + 1)) = sqrtChain U j :=
  (Evolution.exists_comp_self_eq (sqrtChain U j)).choose_spec

/-- **Nielsen & Chuang, Exercise 4.30 — the `O(n²)` gate count of `Cⁿ(U)`.** For *every*
single-qubit unitary `U` and every `k`, the multiplexer `Cⁿ(U) = mcCtrl k (controlledUnitary U)`
(`n = k + 1` controls) has

`CircuitBudget (Cⁿ(U)) (8·k·(k+1) + 2) (2·k + 3)`,

i.e. it is realised — on exactly the `n + 1`-qubit register, **no work qubit** — by a circuit built
from at most `8k(k+1) + 2 = O(n²)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and at most
`2k + 3 = O(n)` single-qubit(-controlled) gates. This transports the whole-circuit budget
`barencoNCircuit_circuitBudget` (of the *explicit* circuit `barencoNCircuit (sqrtChain U) k 0`,
which `exists_barencoNCircuit_eq_mcCtrl` proves equals `Cⁿ(U)`) onto `Cⁿ(U)` itself, using the
total chain `sqrtChain U` from `Evolution.exists_comp_self_eq` — so no square-root hypotheses on
`U`, arbitrary `n`. The `O(n²)` reading of the two counts is `Concrete.barencoGateBudget_isBigO_sq`.
This is the
`O(n²)`-gate content the exercise names; the sibling Exercise 4.29 is its `U = X` specialisation
(`cnx_circuitBudget`). -/
theorem mcCtrl_controlledUnitary_circuitBudget (U : Evolution qubit) (k : ℕ) :
    CircuitBudget (mcCtrl k (controlledUnitary U)) (8 * k * (k + 1) + 2) (2 * k + 3) := by
  -- `barencoNCircuit_zero_eq_mcCtrl` gives `Cⁿ(sqrtChain U 0) = …`; `sqrtChain U 0 ≡ U` (defeq), so
  -- this typechecks as the clean identity `Cⁿ(U) = barencoNCircuit (sqrtChain U) k 0`.
  have h : mcCtrl k (controlledUnitary U) = barencoNCircuit (sqrtChain U) k 0 :=
    barencoNCircuit_zero_eq_mcCtrl (sqrtChain U) (sqrtChain_sq U) k
  rw [h]
  exact barencoNCircuit_circuitBudget (sqrtChain U) k 0

/-- **Nielsen & Chuang, Exercise 4.30 (existence, fully faithful).** For *every* single-qubit
unitary `U` and every `k`, there is a single-qubit square-root chain `V` (with `V 0 = U`) such that
the `(k+1)`-controlled gate `C^(k+1)(U)` equals the explicit no-work-qubit circuit
`barencoNCircuit V k 0` — built only from single-qubit-controlled gates and multiply-controlled
`NOT`s. The chain is `sqrtChain U`, obtained from `Evolution.exists_comp_self_eq` (every
single-qubit gate has a unitary square root), so no square-root hypotheses are imposed: writing
`n = k + 1`, this is the `Cⁿ(U)` no-work-qubit circuit Exercise 4.30 asks for, for arbitrary `n`. -/
theorem exists_barencoNCircuit_eq_mcCtrl (U : Evolution qubit) (k : ℕ) :
    ∃ V : ℕ → Evolution qubit, V 0 = U ∧
      mcCtrl k (controlledUnitary U) = barencoNCircuit V k 0 :=
  ⟨sqrtChain U, sqrtChain_zero U,
    barencoNCircuit_zero_eq_mcCtrl (sqrtChain U) (sqrtChain_sq U) k⟩

end AxQM
