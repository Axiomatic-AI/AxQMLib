/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.QuditPairPermGate
import AxQM.Concrete.ModularAdder

/-!
# Nielsen & Chuang, Exercise 4.36 — a circuit adding two two-bit numbers modulo 4

*(N&C p. 189.)*

Construct a quantum circuit to add two two-bit numbers modulo 4.

## The formalisation

A two-bit number is an element of `Fin 4` (the values `0, 1, 2, 3`),
carried in binary on **two qubits** — `x = x₀ + 2·x₁` with `x₀ = lowBit x`, `x₁ = highBit x`. So the
two registers are two qubit pairs, four qubits in all, and "construct a circuit" means: exhibit a
circuit *built from elementary gates* whose action on the joint computational basis is
`|x, y⟩ → |x, x + y mod 4⟩`. The answer is that explicit gate circuit, together with the
theorem that it performs the transformation.

* `modFourAdderCircuit` — **the circuit** (the answer to the exercise): the standard two-bit
  ripple-carry adder as a composition of exactly **three elementary gates** — a Toffoli and two
  CNOTs — on the four-qubit register `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))` whose wires carry
  `(x₀, y₀, x₁, y₁)`. Writing it as `adderLowCnot ∘ adderHighCnot ∘ adderCarryToffoli`, the gates
  applied in order are

    1. `adderCarryToffoli` — `Toffoli(x₀, y₀ → y₁)`, writing the carry `x₀ ∧ y₀` into the high bit;
    2. `adderHighCnot` — `CNOT(x₁ → y₁)`, adding the high input bit;
    3. `adderLowCnot` — `CNOT(x₀ → y₀)`, adding the low input bit (after the carry has been read).

* `adderKet x y` — **the input encoding:** the computational basis state
  `|x₀⟩ ⊗ |y₀⟩ ⊗ |x₁⟩ ⊗ |y₁⟩` of the four wires holding the binary digits of the two two-bit numbers
  `x, y : Fin 4`.
* `modFourAdderCircuit_evolvePure_adderKet` — **the exercise:** `modFourAdderCircuit |x, y⟩ =
  |x, x + y⟩` for every pair of two-bit numbers `x, y : Fin 4`, where the second register now holds
  the binary digits of `x + y` computed in `Fin 4`, i.e. **modulo `4`**. This is the full truth
  table of the constructed circuit over all sixteen inputs, exactly the transformation
  `|x, y⟩ → |x, x + y mod 4⟩`.
* `modFourAdderCircuit_evolvePure_bits` — the bit-level truth table the circuit realises directly,
  `|x₀, y₀, x₁, y₁⟩ → |x₀, y₀ + x₀, x₁, y₁ + x₀·y₀ + x₁⟩`; with the ripple-carry correctness lemmas
  `Concrete.lowBit_add` / `Concrete.highBit_add` it yields the `Fin 4`-level statement above.
* `modFourAdderCircuit_two_add_three` — a concrete instance: `modFourAdderCircuit |2, 3⟩ = |2, 1⟩`
  (since `2 + 3 = 5 ≡ 1 (mod 4)`).

The **abstract permutation** the circuit implements is also recorded, as the single unitary on two
four-level registers `qudit 4 ⊗ qudit 4` that permutes the joint computational basis by
`(x, y) ↦ (x, x + y)`:

* `modFourAdder` — `quditPairPerm (Concrete.modAddPerm 4)`, with truth table
  `modFourAdder_evolvePure_quditBasis`. This is the same reversible map at ququart granularity; the
  explicit qubit-gate `modFourAdderCircuit` above is its elementary-gate realisation.

## Where the pieces are

* `AxQM/Concrete/ModularAdder.lean` — the binary digits `Concrete.lowBit` / `Concrete.highBit` with
  ripple-carry correctness `lowBit_add` / `highBit_add`, and the abstract permutation
  `Concrete.modAddPerm n : Equiv.Perm (Fin n × Fin n)`.
* `AxQM/Postulates/API/QuditPairPermGate.lean` — the general two-register basis-permutation gate
  `quditPairPerm`, used for the abstract ququart view `modFourAdder`.
* This file — the elementary-gate circuit `modFourAdderCircuit` and its correctness, plus the
  abstract `modFourAdder`.

## Design notes

* **What "the circuit" is (N&C fidelity).** §4.5 asks for a *circuit*, and the
  verifiable content is an explicit composition of standard gates that performs the transformation —
  as its sibling Exercise 4.27 ("using CNOTs and Toffoli gates, construct a quantum circuit …")
  gives a concrete `CNOT`/Toffoli decomposition, not merely the permutation unitary. Accordingly the
  answer here is the three-gate ripple-carry circuit `modFourAdderCircuit`, built only from the
  Toffoli and CNOT gates (`controlledUnitary`, `cnotGate`, `pauliXGate`, and the `onLeft`/`onRight`
  wire embeddings). A generic "realise this permutation as a unitary" gate would answer *any*
  permutation with no circuit content; giving the elementary-gate construction is what the exercise
  asks for.
* **Why the ripple-carry gates and this order.** With `x = x₀ + 2x₁`, `y = y₀ + 2y₁`, the sum bits
  are `s₀ = x₀ ⊕ y₀` and `s₁ = x₁ ⊕ y₁ ⊕ (x₀ ∧ y₀)` (the carry out of the high bit is dropped — that
  is the reduction mod `4`). Computing `y := x + y` in place while preserving `x` forces the order:
  the `Toffoli(x₀, y₀ → y₁)` must fire *first*, reading the carry from the **original** `y₀`, before
  `CNOT(x₀ → y₀)` overwrites it. The three gates then leave `x₀, x₁` untouched and turn `(y₀, y₁)`
  into `(s₀, s₁)`. `Concrete.lowBit_add` / `highBit_add` verify `(s₀, s₁)` are the binary digits of
  `x + y` in `Fin 4`.
* **Statement shape.** The theorem `modFourAdderCircuit_evolvePure_adderKet` ranges over all
  `x, y : Fin 4` (every two-bit number) and writes the output register as the binary digits of
  `x + y`, with `+` addition in `Fin 4` — so the modulo-`4` reduction sits *in* the statement, with
  no added hypotheses and no specialisation. It is the full sixteen-input truth table, not an
  "on some inputs" surrogate.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The elementary-gate circuit

The four wires of `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))` carry `(x₀, y₀, x₁, y₁)` — the low/high bits
of the two input registers, interleaved so the carry lands adjacently. Each gate below is a Toffoli
or CNOT placed on the relevant wires by controlling on the head qubit (`controlledUnitary`) and
embedding on sub-wires (`Evolution.onLeft`/`onRight`). -/

/-- **The carry gate** `Toffoli(x₀, y₀ → y₁)`: on `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))` it flips the
high `y`-bit (wire `3`) exactly when both `x₀` (wire `0`) and `y₀` (wire `1`) are `|1⟩`, writing the
carry `x₀ ∧ y₀` into `y₁`. Doubly controlled with a spectator wire `x₁` between the controls and the
target: `controlledUnitary (controlledUnitary (X on wire 3))`. -/
def adderCarryToffoli : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  controlledUnitary (controlledUnitary (pauliXGate.onRight qubit))

/-- **The high-bit gate** `CNOT(x₁ → y₁)`: the CNOT on the innermost wire pair `(x₁, y₁)` =
`(2, 3)`, adding the high input bit `x₁` into `y₁`. -/
def adderHighCnot : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  (cnotGate.onRight qubit).onRight qubit

/-- **The low-bit gate** `CNOT(x₀ → y₀)`: controlled on `x₀` (wire `0`), flips `y₀` (wire `1`),
adding the low input bit `x₀` into `y₀`. Applied last, after the carry has been read from the
original `y₀`. -/
def adderLowCnot : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  controlledUnitary (pauliXGate.onLeft (qubit ⊗ qubit))

/-- **Action of the carry gate:** `Toffoli(x₀, y₀ → y₁)` flips the high `y`-bit by the carry
`x₀·y₀`, `|x₀, y₀, x₁, y₁⟩ ↦ |x₀, y₀, x₁, y₁ + x₀·y₀⟩` (products in `Fin 2`). -/
theorem adderCarryToffoli_evolvePure (a b c d : Fin 2) :
    adderCarryToffoli.evolvePure
        ((qubitBasis a) ⊗ ((qubitBasis b) ⊗ ((qubitBasis c) ⊗ (qubitBasis d))))
      = (qubitBasis a) ⊗ ((qubitBasis b) ⊗ ((qubitBasis c) ⊗ (qubitBasis (d + a * b)))) := by
  rw [adderCarryToffoli]
  fin_cases a <;> fin_cases b <;>
    simp [controlledUnitary_evolvePure_ketOne, controlledUnitary_evolvePure_ketZero,
      Evolution.onRight_evolvePure, pauliXGate_evolvePure_qubitBasis]

/-- **Action of the high-bit gate:** `CNOT(x₁ → y₁)` adds `x₁` into the high `y`-bit,
`|x₀, y₀, x₁, y₁⟩ ↦ |x₀, y₀, x₁, y₁ + x₁⟩`. -/
theorem adderHighCnot_evolvePure (a b c d : Fin 2) :
    adderHighCnot.evolvePure
        ((qubitBasis a) ⊗ ((qubitBasis b) ⊗ ((qubitBasis c) ⊗ (qubitBasis d))))
      = (qubitBasis a) ⊗ ((qubitBasis b) ⊗ ((qubitBasis c) ⊗ (qubitBasis (d + c)))) := by
  rw [adderHighCnot, Evolution.onRight_evolvePure, Evolution.onRight_evolvePure,
    cnotGate_evolvePure_qubitBasis]

/-- **Action of the low-bit gate:** `CNOT(x₀ → y₀)` adds `x₀` into the low `y`-bit,
`|x₀, y₀, x₁, y₁⟩ ↦ |x₀, y₀ + x₀, x₁, y₁⟩`. -/
theorem adderLowCnot_evolvePure (a b c d : Fin 2) :
    adderLowCnot.evolvePure
        ((qubitBasis a) ⊗ ((qubitBasis b) ⊗ ((qubitBasis c) ⊗ (qubitBasis d))))
      = (qubitBasis a) ⊗ ((qubitBasis (b + a)) ⊗ ((qubitBasis c) ⊗ (qubitBasis d))) := by
  rw [adderLowCnot]
  fin_cases a <;>
    simp [controlledUnitary_evolvePure_ketOne, controlledUnitary_evolvePure_ketZero,
      Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis]

/-- **Exercise 4.36's circuit:** the two-bit modulo-`4` ripple-carry adder as an explicit
elementary-gate circuit on the four-qubit register `qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))` (wires
`x₀, y₀, x₁, y₁`). It is the composition — applied right to left — of the carry `Toffoli(x₀, y₀ →
y₁)`, then `CNOT(x₁ → y₁)`, then `CNOT(x₀ → y₀)`. -/
def modFourAdderCircuit : Evolution (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  adderLowCnot.comp (adderHighCnot.comp adderCarryToffoli)

/-- **Bit-level truth table of the adder circuit:** `modFourAdderCircuit` leaves the input bits
`x₀, x₁` fixed and turns `(y₀, y₁)` into the sum bits `(y₀ + x₀, y₁ + x₀·y₀ + x₁)`, i.e.
`|x₀, y₀, x₁, y₁⟩ ↦ |x₀, y₀ + x₀, x₁, y₁ + x₀·y₀ + x₁⟩` (arithmetic in `Fin 2`). Obtained by
composing the three gate actions in order. -/
theorem modFourAdderCircuit_evolvePure_bits (a b c d : Fin 2) :
    modFourAdderCircuit.evolvePure
        ((qubitBasis a) ⊗ ((qubitBasis b) ⊗ ((qubitBasis c) ⊗ (qubitBasis d))))
      = (qubitBasis a) ⊗
        ((qubitBasis (b + a)) ⊗ ((qubitBasis c) ⊗ (qubitBasis (d + a * b + c)))) := by
  rw [modFourAdderCircuit, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    adderCarryToffoli_evolvePure, adderHighCnot_evolvePure, adderLowCnot_evolvePure]

/-- **The input encoding of two two-bit numbers** `x, y : Fin 4` on the four adder wires: the
computational basis state `|x₀⟩ ⊗ |y₀⟩ ⊗ |x₁⟩ ⊗ |y₁⟩`, where `x₀ = lowBit x`, `x₁ = highBit x`
(and likewise for `y`) are the binary digits. -/
def adderKet (x y : Fin 4) : PureState (qubit ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  (qubitBasis (Concrete.lowBit x)) ⊗ ((qubitBasis (Concrete.lowBit y)) ⊗
    ((qubitBasis (Concrete.highBit x)) ⊗ (qubitBasis (Concrete.highBit y))))

/-- **Nielsen & Chuang, Exercise 4.36.** The constructed circuit `modFourAdderCircuit` performs the
transformation `|x, y⟩ → |x, x + y mod 4⟩`: on the encoding `|x⟩|y⟩` of any two two-bit numbers
`x, y : Fin 4` it leaves the first register unchanged and replaces the second by the binary digits
of `x + y` computed in `Fin 4` — that is, modulo `4`. This full sixteen-input truth table is the
content of the exercise; it combines the circuit's bit-level action
(`modFourAdderCircuit_evolvePure_bits`) with the ripple-carry correctness of the sum bits
(`Concrete.lowBit_add`, `Concrete.highBit_add`). -/
theorem modFourAdderCircuit_evolvePure_adderKet (x y : Fin 4) :
    modFourAdderCircuit.evolvePure (adderKet x y) = adderKet x (x + y) := by
  rw [adderKet, modFourAdderCircuit_evolvePure_bits, adderKet, Concrete.lowBit_add,
    Concrete.highBit_add]

/-- A concrete instance of the constructed adder: `modFourAdderCircuit |2, 3⟩ = |2, 1⟩`, since
`2 + 3 = 5 ≡ 1 (mod 4)`. -/
theorem modFourAdderCircuit_two_add_three :
    modFourAdderCircuit.evolvePure (adderKet 2 3) = adderKet 2 1 := by
  rw [modFourAdderCircuit_evolvePure_adderKet]; rfl

/-! ### The abstract permutation the circuit implements

The same reversible map, recorded at ququart granularity as a single unitary on two four-level
registers `qudit 4 ⊗ qudit 4`: the permutation `(x, y) ↦ (x, x + y)` of the joint computational
basis. The elementary-gate `modFourAdderCircuit` above is its realisation from standard gates. -/

/-- **The modulo-`4` adder as a single abstract unitary** on `qudit 4 ⊗ qudit 4`: the
`quditPairPerm` basis-permutation gate at `Concrete.modAddPerm 4` (`(x, y) ↦ (x, x + y)`), the
reversible operation realised by `modFourAdderCircuit`. -/
def modFourAdder : Evolution (qudit 4 ⊗ qudit 4) :=
  quditPairPerm (Concrete.modAddPerm 4)

/-- **Truth table of the abstract adder:** `modFourAdder |x, y⟩ = |x, x + y⟩` for all two-bit
numbers `x, y : Fin 4`, with `x + y` addition in `Fin 4` (modulo `4`). -/
theorem modFourAdder_evolvePure_quditBasis (x y : Fin 4) :
    modFourAdder.evolvePure ((quditBasis x) ⊗ (quditBasis y))
      = (quditBasis x) ⊗ (quditBasis (x + y)) := by
  rw [modFourAdder, quditPairPerm_evolvePure_quditBasis]
  rfl

end AxQM
