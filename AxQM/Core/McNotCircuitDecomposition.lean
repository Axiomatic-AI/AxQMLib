/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.McNotCircuitEvolution
import AxQM.Core.EvolutionQubitBasisExt

/-!
# A placed `Cᵏ(X)` gate decomposes into a bounded Toffoli circuit (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. `exists_mcNotCircuitEvolution`
lifts a whole *classical* `mcNot` circuit
`gs : List (McNotGate m)` to an `Evolution` on the ambient register `qubit ^⊗ₛ m`, but only
certifies its action *on the computational basis*. This file upgrades that basis-action agreement
to an honest **`Evolution` identity**: a single multiply-controlled `NOT` gate `Cᵏ(X)` placed on the
wires `(S, t)` of a register that has **at least one wire outside the gate's support** *is equal, as
an `Evolution`*, to a genuine circuit of placed `Toffoli`/`CNOT`/`NOT` gates.

## What is formalised

`exists_mcNotCircuitEvolution_eq_placedMcNot` — for a control set `S : Finset (Fin m)`, a target
`t ∉ S`, and one spare wire outside the gate's support (`(insert t S).card < m` — the dirty borrowed
wire the recursion needs), there is a circuit `gs` of gates each with `≤ 2` controls (a
`Toffoli`/`CNOT`/`NOT`, target never a control) and an `Evolution U` on `qubit ^⊗ₛ m` such that

* every gate of `gs` has `≤ 2` controls (`g.1.card ≤ 2 ∧ g.2 ∉ g.1`);
* the circuit has `O(k²)` gates: `gs.length ≤ mcNotGateBound |S|`, and
  `mcNotGateBound =O[atTop] k²` (`Concrete.mcNotGateBound_isBigO_sq`);
* `U` acts on every computational basis state `|⨂ᵢ c i⟩` as the classical circuit denotation
  `Concrete.mcNotDenote gs` — so `U` *is* the closed-system gate sequence of `gs`; and
* **`Evolution.placedMcNot S t ht = U`** — the placed `Cᵏ(X)` gate and the assembled bounded-control
  circuit are the *same* `Evolution`, not merely equal on basis states.

The equality is the composition of three facts read through computational-basis
extensionality (`Evolution.ext_qubitBasis`): the placed gate's truth table
(`Evolution.placedMcNot_evolvePure_qubitBasis`, `= mcNot S t`), the circuit Evolution's truth table
(`exists_mcNotCircuitEvolution`, `= mcNotDenote gs`), and the classical circuit's correctness
(`Concrete.exists_mcNotCircuit`, `mcNotDenote gs = mcNot S t`).

The companion `exists_mcNotCircuitEvolution_eq_placedMcCtrlX` states the same for a `Cᵏ(X)` block
placed by a *wire permutation* `σ` (the `Evolution.onWires` form). The last theorem specialises it
further to `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` — the **contiguous front-block** form
`(Evolution.tensorPowMcCtrlX k).onBlock b` (identity permutation, `Evolution.placedMcCtrlX_one`),
the shape a Barenco `Cᵏ(X)` block takes once the control tower is flattened (its `k` controls and
target are the leading `k + 1` wires, the `b ≥ 1` idle inner wires the spare).

## Its role in the no-work-qubit circuit

This is the **per-block** decomposition every Barenco layer of the tight no-work-qubit
`Cⁿ(X)` circuit needs. On exactly `n + 1` wires the *top* gate `Cⁿ(X)` (support = all `n + 1`
wires, no spare) cannot itself be a permutation-only Toffoli circuit — it is an odd permutation
while every `≤ 2`-control gate is even (the parity obstruction) — so it is decomposed through the
single-qubit `√X` gates (`barencoNCircuit`). But each *internal* block that decomposition
produces is a `Cᵏ(X)` with `k < n`, whose support `k + 1 ≤ n < n + 1` leaves a spare wire, so
`(insert t S).card < m` holds and *this* lemma realises it as a genuine `O(k²)` Toffoli circuit.
Summed over the `O(n)` layers this is the exercise's `O(n²)` gate count.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

/-- **N&C Exercise 4.29: a placed `Cᵏ(X)` decomposes into a bounded
Toffoli/CNOT/NOT circuit.** Given a control set `S : Finset (Fin m)`, a target `t ∉ S`, and one wire
outside the gate's support (`(insert t S).card < m`, the borrowed dirty wire), there is a circuit
`gs` of gates each with at most two controls (a `Toffoli`/`CNOT`/`NOT`, target never a control) and
a single closed-system `Evolution U` on `qubit ^⊗ₛ m` with:

* `∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1` — the gate set is `Toffoli`/`CNOT`/`NOT`;
* `gs.length ≤ Concrete.mcNotGateBound S.card` — the `O(k²)` gate count
  (`k = |S|`; `mcNotGateBound =O[atTop] k²`, `Concrete.mcNotGateBound_isBigO_sq`);
* `U` acts on every computational basis state `|⨂ᵢ c i⟩` exactly as the classical circuit denotation
  `Concrete.mcNotDenote gs` — i.e. `U` is the composite (`exists_mcNotCircuitEvolution`) of the
  placed gates of `gs`; and
* `Evolution.placedMcNot S t ht = U` — the placed `Cᵏ(X)` gate **is** that assembled circuit, as an
  `Evolution`.

The equality follows from computational-basis extensionality (`Evolution.ext_qubitBasis`): both
sides act on `|⨂ᵢ c i⟩` as the classical multiply-controlled `NOT` `Concrete.mcNot S t` — the placed
gate by `Evolution.placedMcNot_evolvePure_qubitBasis`, the circuit `U` by the truth table of
`exists_mcNotCircuitEvolution` composed with the circuit correctness `Concrete.exists_mcNotCircuit`
(`mcNotDenote gs = mcNot S t`).

This is the per-block decomposition consumed by every internal `Cᵏ(X)` block (`k < n`, always with a
spare wire) of the no-work-qubit `Cⁿ(X)` circuit; see the module docstring. -/
theorem exists_mcNotCircuitEvolution_eq_placedMcNot {m : ℕ} (S : Finset (Fin m)) (t : Fin m)
    (ht : t ∉ S) (hspare : (insert t S).card < m) :
    ∃ (gs : List (Concrete.McNotGate m)) (U : Evolution (qubit.tensorPow m)),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ Concrete.mcNotGateBound S.card ∧
      (∀ c : Fin m → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      Evolution.placedMcNot S t ht = U := by
  obtain ⟨gs, hgs, hden, hlen⟩ := Concrete.exists_mcNotCircuit S t ht hspare
  obtain ⟨U, hU⟩ := exists_mcNotCircuitEvolution gs fun g hg => (hgs g hg).2
  refine ⟨gs, U, hgs, hlen, hU, ?_⟩
  refine Evolution.ext_qubitBasis fun c => ?_
  rw [Evolution.placedMcNot_evolvePure_qubitBasis, hU, hden]

/-- **N&C Exercise 4.29: the wire-permutation form of the per-block
decomposition.** The same statement as `exists_mcNotCircuitEvolution_eq_placedMcNot`, but for a
`Cᵏ(X)` block placed by a *wire permutation* `σ` (the form produced by the arbitrary-wire combinator
`Evolution.onWires`, hence the shape a placed Barenco block naturally takes): as soon as there is at
least one idle wire (`1 ≤ b`, so the `k + 1` support wires do not fill the `k + 1 + b`-wire
register), the placed gate `Evolution.placedMcCtrlX k b σ` **equals** a genuine `Evolution` circuit
of `≤ 2`-control gates with `O(k²)` count.

Reduces to `exists_mcNotCircuitEvolution_eq_placedMcNot` applied to the placed gate's own control
set `S = {σ(0), …, σ(k-1)}` (`= Finset.image (σ ∘ Fin.castAdd b) (cnxControls k)`) and target
`t = σ k` (`= σ (Fin.castAdd b (Fin.last k))`): the spare-wire hypothesis holds because `|S| = k`
(the placement is injective) and `|insert t S| = k + 1 < k + 1 + b`, and
`placedMcCtrlX k b σ = placedMcNot S t` by computational-basis extensionality (both have truth
table `Concrete.mcNot S t`). -/
theorem exists_mcNotCircuitEvolution_eq_placedMcCtrlX {k b : ℕ} (hb : 1 ≤ b)
    (σ : Equiv.Perm (Fin (k + 1 + b))) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + b))) (U : Evolution (qubit.tensorPow (k + 1 + b))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ Concrete.mcNotGateBound k ∧
      (∀ c : Fin (k + 1 + b) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      Evolution.placedMcCtrlX k b σ = U := by
  have hinj : Function.Injective (fun j : Fin (k + 1) => σ (Fin.castAdd b j)) :=
    σ.injective.comp (Fin.castAdd_injective _ _)
  have ht_notin : σ (Fin.castAdd b (Fin.last k)) ∉
      Finset.image (fun j => σ (Fin.castAdd b j)) (cnxControls k) := by
    rw [hinj.mem_finset_image]; exact last_notMem_cnxControls k
  have hcard : (Finset.image (fun j => σ (Fin.castAdd b j)) (cnxControls k)).card = k := by
    rw [Finset.card_image_of_injective _ hinj, cnxControls_eq_image_castSucc,
      Finset.card_image_of_injective _ (Fin.castSucc_injective k), Finset.card_univ,
      Fintype.card_fin]
  have hspare : (insert (σ (Fin.castAdd b (Fin.last k)))
      (Finset.image (fun j => σ (Fin.castAdd b j)) (cnxControls k))).card < k + 1 + b := by
    rw [Finset.card_insert_of_notMem ht_notin, hcard]; omega
  obtain ⟨gs, U, hgs, hlen, hUc, hplaced⟩ :=
    exists_mcNotCircuitEvolution_eq_placedMcNot _ _ ht_notin hspare
  refine ⟨gs, U, hgs, ?_, hUc, ?_⟩
  · rwa [hcard] at hlen
  · rw [← hplaced]
    refine Evolution.ext_qubitBasis fun c => ?_
    rw [placedMcCtrlX_evolvePure_qubitBasis, Evolution.placedMcNot_evolvePure_qubitBasis]

/-- **N&C Exercise 4.29: the block-embedded `Cᵏ(X)` decomposes into
a bounded Toffoli circuit.** The contiguous front-block placement
`(Evolution.tensorPowMcCtrlX k).onBlock b` — the grounded `Cᵏ(X)` (`k` controls, one target = the
leading `k + 1` wires) acting as the identity on the trailing `b` ambient wires of
`qubit ^⊗ₛ (k+1+b)` — is, **as an `Evolution`**, a genuine circuit of `≤ 2`-control gates
(`Toffoli`/`CNOT`/`NOT`) with `O(k²)` count, provided at least one ambient wire is present
(`1 ≤ b`, the borrowed dirty wire the recursion needs).

This is the contiguous-front specialisation of `exists_mcNotCircuitEvolution_eq_placedMcCtrlX` at
the identity wire permutation (`Evolution.placedMcCtrlX_one`): the placed gate's control set and
target are then the front wires `(cnxControls k).image (Fin.castAdd b)` and
`Fin.castAdd b (Fin.last k)`. It is the form the multiply-controlled `NOT` blocks of the tight
no-work-qubit `Cⁿ(X)` circuit take after the tower is flattened — the Barenco reduction
(`barencoNCircuit`) puts each internal `Cᵏ(X)` block's `k` controls on the outer tower wires and its
target on the next wire, with the remaining `≥ 1` inner wires idle, i.e. exactly a leading
`(k+1)`-wire block with `b ≥ 1` spare — so each such block is realised here as an `O(k²)` Toffoli
circuit, and the `O(n)` blocks sum to the exercise's `O(n²)` gate count. -/
theorem tensorPowMcCtrlX_onBlock_eq_toffoliCircuit {k b : ℕ} (hb : 1 ≤ b) :
    ∃ (gs : List (Concrete.McNotGate (k + 1 + b))) (U : Evolution (qubit.tensorPow (k + 1 + b))),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      gs.length ≤ Concrete.mcNotGateBound k ∧
      (∀ c : Fin (k + 1 + b) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      (Evolution.tensorPowMcCtrlX k).onBlock b = U := by
  obtain ⟨gs, U, hgs, hlen, hUc, hplaced⟩ :=
    exists_mcNotCircuitEvolution_eq_placedMcCtrlX hb (1 : Equiv.Perm (Fin (k + 1 + b)))
  exact ⟨gs, U, hgs, hlen, hUc, (Evolution.placedMcCtrlX_one k b).symm.trans hplaced⟩

end AxQM
