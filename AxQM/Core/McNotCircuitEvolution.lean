/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.WireGatherPermutation
import AxQM.Concrete.MultiControlledNotCircuit
import AxQM.Postulates.API.TensorPowSplit
import AxQM.Postulates.API.LeftPairGate

/-!
# A classical `mcNot` circuit as an `Evolution` (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The classical development
(`Concrete/MultiControlledNot*`) produces that circuit as a `List` of gates
`gs : List (McNotGate m)` — each gate `(Sᵢ, tᵢ)` a wire-addressed multiply-controlled `NOT`
`Concrete.mcNot Sᵢ tᵢ` with `|Sᵢ| ≤ 2` — with composite denotation `Concrete.mcNotDenote gs` the
reversible bit-string permutation `Cⁿ(X)`. `placedMcCtrlX_wireGather_evolvePure_qubitBasis` turns a
**single** such gate `(S, t)` into a genuine closed-system `Evolution` — but on the *gate-local*
register `qubit ^⊗ₛ (|S| + 1 + b)` sized to that one gate's control arity. This file reconciles
those varying gate-local registers with the **one ambient register** `qubit ^⊗ₛ m` a circuit's gates
all share, and composes the gates into a single `Evolution` realising the whole circuit.

The reconciliation is the **register cast** (`QSystem.tensorPowCongr`): for a gate
`(S, t)` with `t ∉ S`, the support `insert t S` has `|S| + 1 ≤ m` wires, so
`|S| + 1 + (m - (|S| + 1)) = m`
and the gate-local register `qubit ^⊗ₛ (|S| + 1 + (m - (|S| + 1)))` is *propositionally* the ambient
`qubit ^⊗ₛ m`. Transporting that gate along `QSystem.tensorPowCongr qubit (finCongr …)` (the
gate transported by `Evolution.congr`, the state by `PureState.congr`) lands it on `qubit ^⊗ₛ m`
with its truth table `Concrete.mcNot S t` intact — the equivariance of `mcNot` under the wire
relabelling (`Concrete.mcNot_map_equiv`) carries the classical action through the cast.

## What is formalised

* `Evolution.congr_tensorPowCongr_evolvePure_qubitBasis` — the **register-cast dictionary for a
  classical gate**: if `G : Evolution (qubit ^⊗ₛ a)` has computational-basis truth table
  `G |⨂ d⟩ = |⨂ γ d⟩` and `e : Fin a ≃ Fin p`, then the transported gate
  `G.congr (QSystem.tensorPowCongr qubit e)` on `qubit ^⊗ₛ p` acts on `|⨂ c⟩` as
  `|⨂ⱼ (γ (c ∘ e)) (e.symm j)⟩` — the classical action `γ` conjugated by the wire relabelling `e`.
* `Evolution.placedMcNot S t ht` — a single classical gate `(S, t)` (`t ∉ S`) realised as a genuine
  `Evolution (qubit ^⊗ₛ m)` on the **ambient** register, the register cast of the gate-local
  `Evolution.placedMcCtrlX` gathered onto `(S, t)` by `wireGatherPerm`. Its computational-basis
  truth table `Evolution.placedMcNot_evolvePure_qubitBasis` is exactly `Concrete.mcNot S t` on
  `Fin m`.
* `exists_mcNotCircuitEvolution` — the **circuit assembly**: for any classical circuit
  `gs : List (McNotGate m)` whose gates all satisfy `tᵢ ∉ Sᵢ`, there is a single `Evolution` on
  `qubit ^⊗ₛ m` — the composite of the per-gate `Evolution.placedMcNot` gates — acting on every
  computational basis state `|⨂ c⟩` exactly as the classical circuit denotation
  `Concrete.mcNotDenote gs`. Applied to the `O(n²)` circuit `Concrete.exists_mcNotCircuit` produces,
  this exhibits `Cⁿ(X)` (on its dirty-borrow register) as a genuine `Evolution` circuit of placed
  `Toffoli`/`CNOT`/`NOT` gates.

## Design notes

* **Why a register cast, not a fresh placement.** `Evolution.placedMcCtrlX k b σ` is typed on
  `qubit ^⊗ₛ (k + 1 + b)` by construction (it embeds the `(k+1)`-wire gate into `k+1+b` wires via
  `Evolution.onWires`). A circuit's gates have *varying* `kᵢ = |Sᵢ|`, so no single `k + 1 + b` is
  `m` definitionally; the cast `QSystem.tensorPowCongr qubit (finCongr h)` (with `h : k+1+b = m`) is
  the minimal, purely structural reconciliation — it relabels the wire *index type* without
  touching the gate's action, so the gate-local truth table survives up to `mcNot` equivariance.
* **Why the truth table survives.** Transporting `G |⨂ d⟩ = |⨂ γ d⟩` across the cast conjugates the
  bit-string action by `e`: the input `|⨂ c⟩` is read as `|⨂ (c ∘ e)⟩` on the gate-local register,
  `γ` acts there, and the output is relabelled back by `e.symm`. For `γ = Concrete.mcNot S' t'`
  (with `S' = S.map e.symm.toEmbedding`, `t' = e.symm t` the pulled-back gate data) this conjugated
  action is exactly `Concrete.mcNot S t` on the ambient register — `Concrete.mcNot_map_equiv`, the
  naturality of `mcNot` under a bijective wire relabelling.
* **Why an existence statement for the circuit.** The circuit assembly returns *some* realising
  `Evolution` (the fold of the per-gate gates over `Evolution.comp`) rather than a total
  `List → Evolution` function: the per-gate `Evolution.placedMcNot` needs the gate hypothesis
  `tᵢ ∉ Sᵢ`, which the `O(n²)` construction `Concrete.exists_mcNotCircuit` guarantees for every
  gate but which a *total* function over unconstrained lists would have to fake. The existence form
  threads the hypothesis through the list induction cleanly (base = `Evolution.id`, `cons` =
  `Evolution.comp`).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {m : ℕ}

/-- **The gate-local register matches the ambient register.** For a gate `(S, t)` with `t ∉ S` on
`Fin m`, the support `insert t S` uses `|S| + 1 ≤ m` wires, so the gate-local wire count
`|S| + 1 + (m - (|S| + 1))` (the `Evolution.placedMcCtrlX` register arity) is exactly `m`. The
arithmetic identity the register cast `finCongr` consumes. -/
theorem card_succ_add_sub (S : Finset (Fin m)) (t : Fin m) (ht : t ∉ S) :
    S.card + 1 + (m - (S.card + 1)) = m := by
  have h : S.card + 1 ≤ m := by
    have hle := Finset.card_le_univ (insert t S)
    rwa [Finset.card_insert_of_notMem ht, Fintype.card_fin] at hle
  omega

/-- **Register-cast dictionary for a classical gate.** If `G : Evolution (qubit ^⊗ₛ a)` is a
classical gate — it permutes the computational basis, `G |⨂ᵢ d i⟩ = |⨂ᵢ γ d i⟩` for a bit-string
action `γ : (Fin a → Fin 2) → (Fin a → Fin 2)` — then transporting it along the factor-relabelling
register cast `QSystem.tensorPowCongr qubit e` (`e : Fin a ≃ Fin p`) yields a classical gate on
`qubit ^⊗ₛ p` whose action is `γ` conjugated by the wire relabelling: on `|⨂ⱼ c j⟩` it produces
`|⨂ⱼ (γ (c ∘ e)) (e.symm j)⟩` — read the input on the relabelled wires (`c ∘ e`), run `γ`, relabel
the output back by `e.symm`. Proved by rewriting the input as the transport of `|⨂ᵢ c (e i)⟩` under
`QSystem.tensorPowCongr_congr_piTensor`, pushing the transport through `G` with the gate transport
law `Evolution.congr_evolvePure_congr`, applying `γ` via `hG`, and reading the output back through
the cast. -/
theorem Evolution.congr_tensorPowCongr_evolvePure_qubitBasis {a p : ℕ}
    (G : Evolution (qubit ^⊗ₛ a)) (e : Fin a ≃ Fin p)
    (γ : (Fin a → Fin 2) → (Fin a → Fin 2))
    (hG : ∀ d : Fin a → Fin 2,
      G.evolvePure (PureState.piTensor fun i => qubitBasis (d i))
        = PureState.piTensor fun i => qubitBasis (γ d i))
    (c : Fin p → Fin 2) :
    (G.congr (QSystem.tensorPowCongr qubit e)).evolvePure
        (PureState.piTensor fun j => qubitBasis (c j))
      = PureState.piTensor fun j => qubitBasis (γ (fun i => c (e i)) (e.symm j)) := by
  have hinput : PureState.piTensor (fun j => qubitBasis (c j))
      = PureState.congr (QSystem.tensorPowCongr qubit e)
          (PureState.piTensor fun i => qubitBasis (c (e i))) := by
    rw [QSystem.tensorPowCongr_congr_piTensor]
    simp only [Equiv.apply_symm_apply]
  have hcongr := Evolution.congr_evolvePure_congr (QSystem.tensorPowCongr qubit e) G
    (PureState.piTensor fun i => qubitBasis (c (e i)))
  rw [hinput, hcongr, hG, QSystem.tensorPowCongr_congr_piTensor]

/-- **A single classical `mcNot` gate placed on the ambient register.** Given a control set
`S : Finset (Fin m)` and target `t ∉ S`, the multiply-controlled `NOT` gate `(S, t)` realised as a
genuine closed-system `Evolution (qubit ^⊗ₛ m)` on the whole ambient register. Built from the
gate-local `Evolution.placedMcCtrlX` (`Cᵏ(X)`, `k = |S|`) gathered onto the wires `(S, t)` by
`wireGatherPerm`, then cast from its gate-local register `qubit ^⊗ₛ (|S| + 1 + (m - (|S| + 1)))`
onto the ambient `qubit ^⊗ₛ m` by the register cast `QSystem.tensorPowCongr` (the two are
propositionally equal, `card_succ_add_sub`). For `|S| ≤ 2` this is a `Toffoli`/`CNOT`/`NOT`
addressed to the wires `(S, t)`; its computational-basis truth table is
`Evolution.placedMcNot_evolvePure_qubitBasis`. -/
def Evolution.placedMcNot (S : Finset (Fin m)) (t : Fin m) (ht : t ∉ S) :
    Evolution (qubit ^⊗ₛ m) :=
  (Evolution.placedMcCtrlX S.card (m - (S.card + 1))
      (wireGatherPerm (S.map (finCongr (card_succ_add_sub S t ht)).symm.toEmbedding)
        ((finCongr (card_succ_add_sub S t ht)).symm t)
        (by rw [Finset.card_map])
        (by
          intro hmem
          rw [Finset.mem_map] at hmem
          obtain ⟨x, hx, hxe⟩ := hmem
          rw [Equiv.coe_toEmbedding] at hxe
          exact ht ((finCongr (card_succ_add_sub S t ht)).symm.injective hxe ▸ hx)))).congr
    (QSystem.tensorPowCongr qubit (finCongr (card_succ_add_sub S t ht)))

/-- **Computational-basis truth table of the ambient-register `mcNot` gate.** The placed gate
`Evolution.placedMcNot S t ht` acts on every computational product basis state `|⨂ᵢ c i⟩` exactly as
the classical multiply-controlled `NOT` `Concrete.mcNot S t` on the ambient register `Fin m`:
`placedMcNot S t ht |⨂ᵢ c i⟩ = |⨂ᵢ (mcNot S t c) i⟩`. So the placed quantum gate **is** the
reversible bit-string permutation flipping wire `t` iff every control in `S` is set — the
wire-addressed `Toffoli`/`CNOT`/`NOT` truth table on the shared circuit register. Proved by feeding
the gate-local truth table (`placedMcCtrlX_wireGather_evolvePure_qubitBasis`, with classical
action `Concrete.mcNot (S.map e.symm.toEmbedding) (e.symm t)`) through the register-cast dictionary
`Evolution.congr_tensorPowCongr_evolvePure_qubitBasis`, then collapsing the conjugated action to
`Concrete.mcNot S t` by the `mcNot` relabelling naturality `Concrete.mcNot_map_equiv`. -/
theorem Evolution.placedMcNot_evolvePure_qubitBasis (S : Finset (Fin m)) (t : Fin m) (ht : t ∉ S)
    (c : Fin m → Fin 2) :
    (Evolution.placedMcNot S t ht).evolvePure (PureState.piTensor fun i => qubitBasis (c i))
      = PureState.piTensor fun i => qubitBasis (Concrete.mcNot S t c i) := by
  rw [Evolution.placedMcNot,
    Evolution.congr_tensorPowCongr_evolvePure_qubitBasis _ (finCongr (card_succ_add_sub S t ht)) _
      (placedMcCtrlX_wireGather_evolvePure_qubitBasis _ _ _ _)]
  refine congrArg PureState.piTensor ?_
  funext j
  refine congrArg qubitBasis ?_
  rw [Concrete.mcNot_map_equiv]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply]

/-- **A whole classical `mcNot` circuit realised as an `Evolution`.** For any classical circuit
`gs : List (McNotGate m)` whose every gate `(Sᵢ, tᵢ)` has target off its controls (`tᵢ ∉ Sᵢ`),
there is a single closed-system `Evolution` on the ambient qubit register `qubit ^⊗ₛ m` — the
composite (under `Evolution.comp`) of the per-gate `Evolution.placedMcNot` gates — acting on every
computational product basis state `|⨂ᵢ c i⟩` exactly as the classical circuit denotation
`Concrete.mcNotDenote gs`: `U |⨂ᵢ c i⟩ = |⨂ᵢ (mcNotDenote gs c) i⟩`.

Applied to the circuit `Concrete.exists_mcNotCircuit` produces for `Cⁿ(X)` (whose gates each have
`≤ 2` controls, so are genuine `Toffoli`/`CNOT`/`NOT` gates), this exhibits `Cⁿ(X)` — on the
dirty-borrow register `Fin m` with `m ≥ n + 2` — as a genuine `Evolution` circuit built from placed
two-control gates, closing the gap between the classical bit-string circuit and a bona fide
closed-system gate sequence. Proved by induction on `gs`: the empty circuit is `Evolution.id`, and
`g :: gs` is `Evolution.placedMcNot g.1 g.2 · |>.comp` the inductive gate, tracked through
`Evolution.evolvePure_comp` and the per-gate truth table
`Evolution.placedMcNot_evolvePure_qubitBasis`. -/
theorem exists_mcNotCircuitEvolution (gs : List (Concrete.McNotGate m))
    (hgs : ∀ g ∈ gs, g.2 ∉ g.1) :
    ∃ U : Evolution (qubit ^⊗ₛ m), ∀ c : Fin m → Fin 2,
      U.evolvePure (PureState.piTensor fun i => qubitBasis (c i))
        = PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i) := by
  induction gs with
  | nil =>
    refine ⟨Evolution.id, fun c => ?_⟩
    let ψ0 : PureState (qubit ^⊗ₛ m) := PureState.piTensor fun i => qubitBasis (c i)
    change Evolution.id.evolvePure ψ0 = _
    rw [Evolution.id_evolvePure]
    simp only [Concrete.mcNotDenote_nil]
    rfl
  | cons g gs IH =>
    obtain ⟨U, hU⟩ := IH fun g' hg' => hgs g' (List.mem_cons.2 (Or.inr hg'))
    refine ⟨(Evolution.placedMcNot g.1 g.2 (hgs g (List.mem_cons.2 (Or.inl rfl)))).comp U,
      fun c => ?_⟩
    let ψ0 : PureState (qubit ^⊗ₛ m) := PureState.piTensor fun i => qubitBasis (c i)
    change ((Evolution.placedMcNot g.1 g.2 (hgs g (List.mem_cons.2 (Or.inl rfl)))).comp
        U).evolvePure
      ψ0 = _
    rw [Evolution.evolvePure_comp, hU, Evolution.placedMcNot_evolvePure_qubitBasis]
    simp only [Concrete.mcNotDenote_cons]
    rfl

end AxQM
