/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGateCountSynthesis

/-!
# Nielsen & Chuang, Exercise 10.40 — H, S, CNOT generate the normalizer `N(Gₙ)` (inductive proof)

*(N&C §10.5.2, p. 462.)*

Inductive proof that Hadamard, phase, CNOT generate the normalizer N(Gn) (proof of Thm 10.6).

Theorem 10.6, which this exercise proves, concludes that such a `U` "may be composed from `O(n²)`
Hadamard, phase and controlled-NOT gates". So the exercise carries **two** clauses: (i) that H, S,
CNOT *generate* `N(Gₙ)` (up to global phase) — a group-theoretic existence statement; and (ii) the
*quantitative* `O(n²)` bound on the gate count, restated in parts 2 and 3.

## Context

`Gₙ` is the `n`-qubit Pauli group (`Concrete.PauliGroup`, `iˢ ⊗ₖ σ_{aₖ}`); the set of unitaries `U`
with `U Gₙ U† = Gₙ` is its **normalizer** `N(Gₙ)`, and H, S (phase), CNOT are the **normalizer
gates**. The easy containment `⟨H, S, CNOT⟩ ⊆ N(Gₙ)` is the Clifford-circuit conjugation backbone of
Problem 10.3 (`Concrete.cliffordCircuit_isPauliNormalizer`). The exercise is the **converse** —
`N(Gₙ) ⊆ ⟨H, S, CNOT⟩` up to a (necessary) unit global phase — proved by N&C's inductive synthesis:
peel wire `0` (bring `U` to fix `X₀, Z₀`), tensor-factor the residue as `I₂ ⊗ M'`, recurse on `M'`,
and reassemble (Figure 10.9), together with the `O(n²)` count accumulated along the induction.

## Scope of this formalisation — both clauses, generation and the `O(n²)` gate count

These statements record **both** clauses of Exercise 10.40: clause (i), the group-theoretic
**generation** statement, and clause (ii), the **quantitative `O(n²)` gate-count** bound of parts
2–3 (and Theorem 10.6's conclusion). The gate-count clause follows by re-running the Figure 10.9
synthesis with a length-tracking invariant, threading `O(n)` bounds through every building block
(`fixFirstPair`, `reducePair`, `relabel`, `inverse`, `++`); the recurrence
`L(n+1) ≤ 3·(6·(n+1)+32) + L(n)` unrolls to the exact closed form `L(n) ≤ 9·n² + 105·n`, a concrete
quadratic — manifestly `O(n²)`, matching the textbook count with no weakening.

## Declarations — both clauses

The synthesis is in `AxQM/Concrete/PauliNormalizer*.lean` (namespace `AxQM.Concrete`); the `O(n²)`
gate-count result is in `AxQM/Concrete/PauliNormalizerGateCountSynthesis.lean` and its per-level
`O(n)` first-wire lemma in `AxQM/Concrete/PauliNormalizerGateCountFirstPair.lean`. The two main
results are:

* **`isPauliNormalizer_eq_smul_cliffordCircuit`** (`PauliNormalizerInduction.lean`) — the generation
  clause. For every `U ∈ N(Gₙ)` there is a Clifford circuit `C` (a word in H, S, CNOT) and a unit
  scalar `c` (`‖c‖ = 1`) with `U = c • C.toMatrix`. Proved by `Nat.rec` on the wire count: the base
  `n = 0` is a `1×1` unitary (empty circuit); the step peels the first wire via
  (`exists_cliffordCircuit_fixFirstPair`, `firstWireRestrict_isPauliNormalizer`), applies
  the inductive hypothesis to the wire-`0` restriction, embeds it on wires `1 … n` by `relabel`
  along `Fin.succ`, matches the `2(n+1)` generators, and reassembles with the Clifford inverse.
* **`isPauliNormalizer_eq_smul_cliffordCircuit_length_le`**
  (`PauliNormalizerGateCountSynthesis.lean`) — the `O(n²)` clause. The *same* statement strengthened
  with `C.length ≤ 9·n² + 105·n`. The length-tracking companion of the generation result: the base
  is the empty circuit (`0 ≤ 0`); the step threads the per-level lemma below and
  `CliffordCircuit.length_inverse_append_relabel_le` (`|inverse B ++ relabel C'| ≤ 3·|B| + |C'|`)
  into the recurrence, closing at `9·(n+1)² + 105·(n+1)` by `nlinarith`.
* **`IsPauliNormalizer.exists_cliffordCircuit_fixFirstPair_length_le`**
  (`PauliNormalizerGateCountFirstPair.lean`) — the per-level `O(n)` lemma (Figure 10.9 first-wire
  reduction, part 2). The first-wire-fixing circuit `B` has `B.length ≤ 6·(n+1) + 32`, built from
  `exists_cliffordCircuit_reducePair_length_le` (`≤ 6·(n+1)+20`), a wire swap (`≤ 3`) and a
  single-wire sign gadget (`≤ 9`). It is applied in the result above.

The `O(n)` gate-count cascade these build on — `PauliNormalizerGateCount.lean` (length calculus of
the circuit-building defs), `…Gadgets.lean` (constant base-gadget bounds), `…Reduce.lean`
(single-generator reduction `≤ 2n+2`), `…Pair.lean` (anticommuting-pair reduction `≤ 6n+20`),
`…FirstPair.lean` (first-wire reduction `≤ 6·(n+1)+32`) — and the first-wire reduction, tensor
restriction, decoupling, generator-determinacy, wire relabeling and Clifford-inverse lemmas are in
the files `AxQM/Concrete/PauliNormalizer*.lean` (the shared Theorem 10.6 / Exercise 10.40
development).
-/
