/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerInduction

/-!
# Concrete: gate-count (circuit-length) foundation for Nielsen & Chuang Theorem 10.6

*(Theorem 10.6, N&C §10.5.2, p. 461.)*

Nielsen & Chuang **Theorem 10.6** asserts that a Pauli normalizer `U ∈ N(Gₙ)` may be composed, up to
a global phase, from **`O(n²)`** Hadamard/phase/CNOT gates. The structural converse — that *some*
Clifford circuit realises `U` up to a global phase — is
`isPauliNormalizer_eq_smul_cliffordCircuit`; the quantitative part of the boxed theorem is the
**`O(n²)` gate-count** bound.

A `CliffordCircuit n` is a `List (CliffordGate n)`, so *its gate count is its `List.length`*. This
file collects the **length arithmetic of the circuit-building blocks** of the Figure 10.9 inductive
synthesis; these bounds compose to bound the synthesised circuit's length.

Contents:

* `CliffordCircuit.length_relabel`, `CliffordCircuit.length_onWire` — wire relabeling preserves the
  gate count (it is `List.map`).
* `CliffordCircuit.length_layerOn_le`, `CliffordCircuit.length_singleQubitLayer_le` — a single-qubit
  layer costs at most `n · m₀` gates when each per-wire word has `≤ m₀` gates (one bounded word on
  each of the `n` wires).
* `CliffordCircuit.length_rotateToX_le`, `…_rotateToZ_le`, `…_rotateToZFixingX_le` — the single-wire
  rotation words are bounded by a *constant* (`≤ 1`, `≤ 2`, `≤ 3` gates), the `m₀` a layer plugs in.
* `length_cnotStep_le`, `length_cnotFan_le`, `length_cnotFanInto_le` — a CNOT fan costs at most one
  gate per target (`≤ |ts|`).
* `length_swapWires_le` — a wire swap costs at most `3` gates (the three-CNOT `SWAP`).
* `CliffordGate.length_invList_le`, `CliffordCircuit.length_inverse_le` — inverting a circuit at
  most *triples* its gate count (`S⁻¹ = S³` is the longest per-gate inverse word).
* `CliffordCircuit.length_inverse_append_relabel_le` — the per-level overhead of the Figure 10.9
  recurrence `C_{n+1} = inverse B ++ relabel C'`: at most `3·|B| + |C'|` gates. With a linear bound
  `|B| ≤ O(n)` on the per-level first-wire-reduction circuit
  (`AxQM/Concrete/PauliNormalizerGateCountFirstPair.lean`), this recurrence unrolls to the `O(n²)`
  total gate count of Theorem 10.6.
-/

namespace AxQM.Concrete

variable {m n : ℕ}

/-- **A gate's inverse word has at most `3` gates**: `(γ.invList).length ≤ 3`. The Hadamard and CNOT
gates are self-inverse (`[H]`, `[CNOT]`, one gate each); the phase gate needs `S⁻¹ = S³`
(`[S, S, S]`, three gates), which is the longest inverse word. -/
theorem CliffordGate.length_invList_le (γ : CliffordGate n) : γ.invList.length ≤ 3 := by
  cases γ <;> simp [CliffordGate.invList]

namespace CliffordCircuit

/-! ### Relabeling and single-wire placement preserve the gate count -/

/-- **Wire relabeling preserves the gate count**: `(C.relabel f).length = C.length`. Relabeling is
`List.map (CliffordGate.relabel f)`, which keeps the list length. -/
theorem length_relabel (f : Fin m ↪ Fin n) (C : CliffordCircuit m) :
    (C.relabel f).length = C.length := by
  simp [relabel]

/-- **Running a single-wire circuit on one wire preserves the gate count**:
`(onWire j C₀).length = C₀.length`. `onWire j` is the relabeling along the wire-`j` embedding. -/
theorem length_onWire (j : Fin n) (C₀ : CliffordCircuit 1) :
    (onWire j C₀).length = C₀.length := by
  rw [onWire, length_relabel]

/-! ### The single-qubit layer costs one bounded word per wire -/

/-- **A per-wire layer over a wire list costs at most one bounded word per wire**: if every
single-wire word `f i` has at most `m₀` gates, then `layerOn f L` has at most `|L| · m₀` gates.
Induction on `L`; each `onWire i (f i)` factor contributes `(f i).length ≤ m₀`
(`length_onWire`, `hf`). -/
theorem length_layerOn_le (f : Fin n → CliffordCircuit 1) {m₀ : ℕ}
    (hf : ∀ i, (f i).length ≤ m₀) (L : List (Fin n)) :
    (layerOn f L).length ≤ L.length * m₀ := by
  induction L with
  | nil => simp
  | cons i L ih =>
      rw [layerOn_cons, List.length_append, length_onWire, List.length_cons, Nat.add_one_mul]
      have := hf i
      omega

/-- **The single-qubit layer costs at most `n · m₀` gates**: if each per-wire word `f i` has at most
`m₀` gates, then `(singleQubitLayer f).length ≤ n · m₀`. The layer runs one word on each of the `n`
wires (`layerOn f (List.finRange n)`), so `length_layerOn_le` gives the bound. -/
theorem length_singleQubitLayer_le (f : Fin n → CliffordCircuit 1) {m₀ : ℕ}
    (hf : ∀ i, (f i).length ≤ m₀) : (singleQubitLayer f).length ≤ n * m₀ := by
  rw [singleQubitLayer]
  calc (layerOn f (List.finRange n)).length
      ≤ (List.finRange n).length * m₀ := length_layerOn_le f hf _
    _ = n * m₀ := by simp

/-! ### The single-wire rotation words are constant-length -/

/-- **`rotateToX c` has at most one gate**: it is `[S]` (`Y ↦ X`), `[H]` (`Z ↦ X`), or `[]`
(`I`/`X`). -/
theorem length_rotateToX_le (c : Fin 4) : (rotateToX c).length ≤ 1 := by
  fin_cases c <;> simp [rotateToX]

/-- **`rotateToZ c` has at most two gates**: it is `[H]` (`X ↦ Z`), `[H, S]` (`Y ↦ Z`), or `[]`
(`I`/`Z`). -/
theorem length_rotateToZ_le (c : Fin 4) : (rotateToZ c).length ≤ 2 := by
  fin_cases c <;> simp [rotateToZ]

/-- **`rotateToZFixingX c` has at most three gates**: it is `[H, S, H]` (`Y ↦ Z` while fixing `X`),
or `[]` (`Z`). -/
theorem length_rotateToZFixingX_le (c : Fin 4) : (rotateToZFixingX c).length ≤ 3 := by
  fin_cases c <;> simp [rotateToZFixingX]

/-! ### Inverting a circuit at most triples the gate count -/

/-- **Inverting a circuit at most triples its gate count**: `(inverse C).length ≤ 3 · C.length`.
Induction on the gate list: `inverse (γ :: U) = inverse U ++ γ.invList`, and each inverse word adds
at most `3` gates (`CliffordGate.length_invList_le`). -/
theorem length_inverse_le (C : CliffordCircuit n) : (inverse C).length ≤ 3 * C.length := by
  induction C with
  | nil => simp [inverse]
  | cons γ U ih =>
      rw [inverse, List.length_append, List.length_cons]
      have := CliffordGate.length_invList_le γ
      omega

/-- **The per-level gate overhead of the Figure 10.9 recurrence.** Prefixing the inverse of the
first-wire-reduction circuit `B` and appending the sub-register circuit `C'` (embedded onto the last
`n` wires via `relabel f`) adds at most `3 · |B|` gates to `C'`:
`(B.inverse ++ C'.relabel f).length ≤ 3 · B.length + C'.length`. This is the arithmetic of the
inductive step `C_{n+1} = inverse B ++ relabel C'`; with a linear bound `|B| ≤ O(n)` it
unrolls to the `O(n²)` gate count of Theorem 10.6. -/
theorem length_inverse_append_relabel_le (B : CliffordCircuit n) (C' : CliffordCircuit m)
    (f : Fin m ↪ Fin n) :
    (inverse B ++ C'.relabel f).length ≤ 3 * B.length + C'.length := by
  rw [List.length_append, length_relabel]
  have := length_inverse_le B
  omega

end CliffordCircuit

/-! ### CNOT fans and wire swaps -/

/-- **A single CNOT step has at most one gate**: `(cnotStep i t).length ≤ 1` (it is `[CNOT_{i→t}]`,
or `[]` on a self-target). -/
theorem length_cnotStep_le (i t : Fin n) : (cnotStep i t).length ≤ 1 := by
  unfold cnotStep
  split <;> simp

/-- **A CNOT fan costs at most one gate per target**: `(cnotFan i ts).length ≤ ts.length`. Induction
on `ts` via `cnotFan_cons`, each step a single `cnotStep` (`length_cnotStep_le`). -/
theorem length_cnotFan_le (i : Fin n) (ts : List (Fin n)) :
    (cnotFan i ts).length ≤ ts.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rw [cnotFan_cons, List.length_append, List.length_cons]
      have := length_cnotStep_le i t
      omega

/-- **A reverse CNOT fan costs at most one gate per control**: `(cnotFanInto c ts).length ≤
ts.length`. Induction on `ts` via `cnotFanInto_cons`, each step a single `cnotStep`. -/
theorem length_cnotFanInto_le (c : Fin n) (ts : List (Fin n)) :
    (cnotFanInto c ts).length ≤ ts.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rw [cnotFanInto_cons, List.length_append, List.length_cons]
      have := length_cnotStep_le t c
      omega

/-- **A wire swap has at most three gates**: `(swapWires a b).length ≤ 3` (the three-CNOT `SWAP`, or
`[]` when `a = b`). -/
theorem length_swapWires_le (a b : Fin n) : (swapWires a b).length ≤ 3 := by
  unfold swapWires
  split <;> simp

end AxQM.Concrete
