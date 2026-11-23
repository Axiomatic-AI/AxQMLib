/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.BarencoSplitLinearBlockReduction

/-!
# A compositional elementary-gate budget for `Evolution` circuits (N&C Ex 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`): a nested stack of
`O(n)` reduction layers, each a tail `barencoTail k W = Cᵏ(X) · C(W†) · Cᵏ(X) · C(W)` under a
leading multiplexer that the recursion expands. Each internal `Cᵏ(X)` block is a **linear**
`O(k)` `Toffoli`/`CNOT`/`NOT` circuit with **no** wire budget
(`barencoTail_pauliXGate_onLeft_eq_splitLinearToffoliBlocks`). To obtain the exercise's `O(n²)`
*count* one needs a way to **add** those per-layer counts across the recursion: every
existing reduction lemma is a per-block / per-layer existential on its own tower register, and there
is no abstraction under which the counts compose.

## What is formalised

This file supplies exactly that abstraction.

* `CircuitBudget E t s` — the proposition that the `Evolution` `E` is built, up to register
  isomorphism, from **at most `t`** `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and **at most `s`**
  single-qubit-controlled gates `C(V)` (`V` a single-qubit gate). It is closed under sequential
  composition (`comp`, budgets add), register transport (`congr`), and weakening (`mono`); its
  leaves are a `≤ 2`-control block realised by a classical gate list (`block`, contributing
  `gs.length` to `t`), and a single-qubit-controlled gate `C(unCtrl d g)` or its adjoint (`ctrlGate`
  / `ctrlGateAdj`, contributing `1` to `s`). Because no constructor can *lower* a budget,
  `CircuitBudget E t s` is an honest **upper bound** on the elementary-gate count of a realisation.

* `CircuitBudget.cast_congr` — transport a budget along a bare register **equality**
  `cast (congrArg Evolution h)`, the shape the `barencoNCircuit` recursion glues its layers with
  (`barencoNCircuit_succ`). It is what folds a budget over that recursion.

* `barencoTail_unCtrl_circuitBudget` — the **per-layer budget**: for `2 ≤ k` (block index
  `k+1 ≥ 3`) and any single-qubit root `g : Evolution qubit`, one Barenco tail layer
  `barencoTail (k+1) (unCtrl d g)` has `CircuitBudget … (16 (k+1)) 2` — at most `16 (k+1) = O(k)`
  `≤ 2`-control gates (two blocks of `≤ 8 (k+1)` each) and exactly two
  single-qubit-controlled gates `C(W)`, `C(W†)`. This is the per-layer reduction repackaged
  as a *composable* budget.

## Use for the `O(n²)` count

`barencoNCircuit`'s recursion is a composition of `O(n)` such tail layers (`barencoNCircuit_succ`),
each with `W = unCtrl d (V (d+1))` a single-qubit root, so folding
`barencoTail_unCtrl_circuitBudget` over the recursion (via `CircuitBudget.comp` and
`CircuitBudget.cast_congr`) and summing the linear per-layer counts `Σⱼ 16 (j+1) = O(n²)` yields the
exercise's `O(n²)` `≤ 2`-control-gate total together with the `O(n)` single-qubit-controlled gates,
on exactly the `n + 1`-wire register.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The elementary-gate budget of an `Evolution` circuit (N&C Ex 4.29).** `CircuitBudget E t s`
holds when `E` is built, up to register isomorphism, from **at most `t`** `≤ 2`-control gates
(`Toffoli`/`CNOT`/`NOT`) and **at most `s`** single-qubit gates — single-qubit-*controlled* gates
`C(V)` (`ctrlGate`/`ctrlGateAdj`) or bare uncontrolled ones (`single`), `V` a single-qubit gate.
The predicate is the compositional accountant the `O(n²)` count of `Cⁿ(X)`
circuit needs: its leaves witness genuine elementary gates, and its structural constructors let the
counts of a composed circuit **add**. No constructor lowers a budget, so `CircuitBudget E t s` is an
honest upper bound on the gate count of a realisation of `E`.

* `block` — a `≤ 2`-control block: a classical gate list `gs` (each gate `≤ 2` controls,
  target not a control) whose circuit denotation `mcNotDenote gs` is realised by the `Evolution` `U`
  on the flattened register `qubit ^⊗ₛ m`; contributes `gs.length` to the `≤ 2`-control count.
* `ctrlGate` / `ctrlGateAdj` — a single-qubit-controlled gate `C(unCtrl d g)` (resp. its adjoint
  `C((unCtrl d g)†)`), `g : Evolution qubit`, wrapped by `n` idle controls; contributes `1` to the
  single-qubit count.
* `single` — a bare (uncontrolled) single-qubit gate `g : Evolution qubit`, lifted `d` times by idle
  wraps and placed on one wire of a register (`(unCtrl d g).onRight qubit`); contributes `1` to the
  single-qubit count. This is the leading multiplexer `C⁰(V) = V` of the innermost Barenco reduction
  layer (`barencoReductionCircuit 0`), the one gate of the `barencoNCircuit` recursion that is
  neither a `≤ 2`-control gate nor a *controlled* single-qubit gate. It is an honest "single qubit
  gate" in the exercise's sense; so the single-qubit count `s` bounds the controlled *and*
  uncontrolled single-qubit gates together (each `O(1)`-decomposable to single-qubit + `CNOT` gates,
  Exercise 4.22 / Figure 4.6).
* `bare` — a bare single-qubit gate `g : Evolution qubit` on a one-qubit register, with no idle
  wires at all; contributes `1` to the single-qubit count. The degenerate leaf of `single` (the
  register carries no wire to place a gate *on the right of*): it is the base of the single-qubit
  gate on one tower wire (`qtowerSingleWire_circuitBudget`) when the tower is a single qubit. No
  `unCtrl`/`onRight` wrap can shrink a register below one qubit, so it is its own constructor.
* `comp` — sequential composition: budgets add.
* `congr` — transport along a system isomorphism `e : S ≃ₛ T`: budget preserved.
* `mono` — weakening: a budget may be freely increased. -/
inductive CircuitBudget : {S : QSystem} → Evolution S → ℕ → ℕ → Prop where
  | block {m : ℕ} (gs : List (Concrete.McNotGate m)) (U : Evolution (qubit ^⊗ₛ m))
      (hgs : ∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1)
      (hU : ∀ c : Fin m → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i)) =
          PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) :
      CircuitBudget U gs.length 0
  | ctrlGate {d n : ℕ} (g : Evolution qubit) :
      CircuitBudget (unCtrl n (controlledUnitary (unCtrl d g))) 0 1
  | ctrlGateAdj {d n : ℕ} (g : Evolution qubit) :
      CircuitBudget (unCtrl n (controlledUnitary (unCtrl d g).adjoint)) 0 1
  | single {d : ℕ} (g : Evolution qubit) :
      CircuitBudget ((unCtrl d g).onRight qubit) 0 1
  | bare (g : Evolution qubit) :
      CircuitBudget g 0 1
  | comp {S : QSystem} {E F : Evolution S} {t₁ s₁ t₂ s₂ : ℕ}
      (hE : CircuitBudget E t₁ s₁) (hF : CircuitBudget F t₂ s₂) :
      CircuitBudget (E.comp F) (t₁ + t₂) (s₁ + s₂)
  | congr {S T : QSystem} (e : S.Iso T) {E : Evolution S} {t s : ℕ}
      (h : CircuitBudget E t s) :
      CircuitBudget (Evolution.congr e E) t s
  | mono {S : QSystem} {E : Evolution S} {t s t' s' : ℕ}
      (h : CircuitBudget E t s) (ht : t ≤ t') (hs : s ≤ s') :
      CircuitBudget E t' s'

/-- **A budget transports along a register `Eq`.** If `E : Evolution M` has `CircuitBudget E t s`,
and `h : M = N`, then the transport `cast (congrArg Evolution h) E : Evolution N` has the same
budget. This is the equality-cast counterpart of the `congr` isomorphism constructor: it matches the
bare `cast (congrArg Evolution (qtower_qubit_comm ..))` the `barencoNCircuit` recursion uses to glue
a deeper layer onto its parent register (`barencoNCircuit_succ`). -/
theorem CircuitBudget.cast_congr {M N : QSystem} (h : M = N) {E : Evolution M} {t s : ℕ}
    (hb : CircuitBudget E t s) :
    CircuitBudget (cast (congrArg Evolution h) E) t s := by
  subst h
  simpa using hb

/-- **A product of uniformly-budgeted gates costs, per factor, one copy of that budget.** If every
gate in a list `l` has the *same* budget `CircuitBudget · t₀ s₀`, then their composition `l.prod`
has `CircuitBudget l.prod (l.length * t₀) (l.length * s₀)` — the counts scale with the number of
factors. The single induction behind every wire-by-wire gate layer, in both count coordinates at
once: `comp` adds the head gate's budget onto the tail's accumulated `t.length • (t₀, s₀)` (the
`succ_mul` step), and the `nil` base is the register-identity budget `hid` (`0 * t₀ = 0`, needed
because a general system `S` carries no elementary-gate witness for `1`). Its single-qubit
specialisation `CircuitBudget.listProd` (`t₀ = 0`, `s₀ = 1`) and its `≤ 2`-control specialisation
`CircuitBudget.listProd_twoControl` (`t₀ = 1`, `s₀ = 0`) recover the ergonomic clean-slot
conclusions `0 l.length` and `l.length 0` that callers consume. -/
theorem CircuitBudget.listProd_uniform {S : QSystem} {t₀ s₀ : ℕ}
    (hid : CircuitBudget (1 : Evolution S) 0 0)
    (l : List (Evolution S)) (h : ∀ E ∈ l, CircuitBudget E t₀ s₀) :
    CircuitBudget l.prod (l.length * t₀) (l.length * s₀) := by
  induction l with
  | nil => simpa using hid
  | cons a t ih =>
      rw [List.prod_cons, List.length_cons, Evolution.mul_def, add_one_mul, add_one_mul]
      exact ((h a (by simp)).comp (ih fun E hE => h E (by simp [hE]))).mono (by omega) (by omega)

/-- **N&C Exercise 4.29: the per-layer budget.** For `2 ≤ k` (so the block index `k + 1`
is `≥ 3`) and any single-qubit root `g : Evolution qubit`, one Barenco tail reduction layer
`barencoTail (k+1) (unCtrl d g)` — on the control tower `qtower (k+1) (qubit ⊗ qtower d qubit)` —
has

`CircuitBudget (barencoTail (k+1) (unCtrl d g)) (16 * (k + 1)) 2`,

i.e. it is built from at most `16 (k+1) = O(k)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) — two
`Cᵏ⁺¹(X)` blocks of `≤ 8 (k+1)` each — and exactly two single-qubit-controlled gates
`C(unCtrl d g)`, `C((unCtrl d g)†)`. This repackages the per-layer reduction
`barencoTail_pauliXGate_onLeft_eq_splitLinearToffoliBlocks` as a *composable* budget: the two
transported blocks `B = Evolution.congr (barencoBlockFlatten (k+1) d).symm U` each get `block` +
`congr`, the two single-qubit-controlled gates get `ctrlGateAdj` / `ctrlGate`, and `comp` sums the
counts (`2 · 8 (k+1)` blocks, `2` controlled gates), rounded to `16 (k+1)` via `mono`. Folding this
over the `barencoNCircuit` recursion gives the `O(n²)` count of Exercise 4.29. -/
theorem barencoTail_unCtrl_circuitBudget (k d : ℕ) (hk : 2 ≤ k) (g : Evolution qubit) :
    CircuitBudget (barencoTail (k + 1) (unCtrl d g)) (16 * (k + 1)) 2 := by
  obtain ⟨gs, U, hgs, hlen, hUc, htail⟩ :=
    barencoTail_pauliXGate_onLeft_eq_splitLinearToffoliBlocks k d hk (unCtrl d g)
  rw [htail]
  have hB : CircuitBudget
      (Evolution.congr (barencoBlockFlatten (k + 1) d).symm U) gs.length 0 :=
    CircuitBudget.congr _ (CircuitBudget.block gs U hgs hUc)
  refine (hB.comp
    ((CircuitBudget.ctrlGateAdj (n := k + 1) (d := d) g).comp
      (hB.comp (CircuitBudget.ctrlGate (n := k + 1) (d := d) g)))).mono ?_ ?_
  · omega
  · omega

end AxQM
