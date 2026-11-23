/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.McNotCircuitEvolution
import AxQM.Concrete.ParityCheckSyndromeCircuit

/-!
# Nielsen & Chuang, Exercise 10.26 — computing a parity-check syndrome with CNOTs

Explain how to compute |x>|0> -> |x>|Hx> using a circuit of controlled-NOTs.

*(N&C §10.5.1, p. 451.)*

## The formalisation

For a parity-check matrix `H` — carried by its entry function `H : Fin k → Fin n → Fin 2` (`k`
parity checks, `n` code bits) — `exists_cnotEvolution_paritySyndrome` exhibits a gate list `gs`
composed entirely of single-control CNOTs together with the genuine closed-system unitary
`U : Evolution (qubit ^⊗ₛ (n + k))` realising it, on `n` data qubits followed by `k` syndrome
ancillas, such that `U` maps every computational basis state `|x⟩|0⟩` to `|x⟩|Hx⟩`, where the
syndrome `(Hx)ᵢ = ∑ⱼ H i j · xⱼ` is computed mod 2 in the ancillas. The register is the flat
`n + k`-qubit tensor power, the bipartite state `|x⟩|0⟩` written as `⨂_w |(Fin.append x 0) w⟩` and
the output `|x⟩|Hx⟩` as `⨂_w |(Fin.append x (fun i => ∑ⱼ H i j · xⱼ)) w⟩`.

`U` is the composite of the CNOTs in `Concrete.parityCnotCircuit H`: for every entry `H i j = 1`, a
CNOT with control the data wire `Fin.castAdd k j` and target the syndrome wire `Fin.natAdd n i`.
Each gate is a *single-control* controlled-NOT (`Concrete.parityCnotCircuit_card_controls`), so the
circuit is "composed entirely of controlled-NOTs" exactly as the exercise asks — never a `NOT` or a
`Toffoli`.

## Design decisions

* **The vehicle: `exists_mcNotCircuitEvolution`.** The library already realises any classical
  multiply-controlled-`NOT` circuit `gs : List (Concrete.McNotGate m)` (each gate's target off its
  controls) as an `Evolution (qubit ^⊗ₛ m)` acting on the computational basis by the circuit's
  bit-string denotation `Concrete.mcNotDenote gs`. This exercise is then purely the *classical*
  problem of exhibiting a CNOT gate list whose denotation sends `Fin.append x 0` to
  `Fin.append x (fun i => ∑ⱼ H i j · xⱼ)` — carried out in
  `Concrete/ParityCheckSyndromeCircuit.lean` (`Concrete.mcNotDenote_parityCnotCircuit_append`) —
  plus feeding it through the framework with `Concrete.parityCnotCircuit_target_notMem_controls`.

* **The CNOT-circuit constraint is bundled into the type.** N&C asks to *explain how to compute* the
  transformation *using a circuit composed entirely of controlled-NOTs* — so the existential
  quantifies over the **gate list** `gs` as well as the unitary `U`, and asserts three things: (i)
  every gate of `gs` is a genuine single-control CNOT (`g.1.card = 1`, target off its control); (ii)
  `U` is exactly the closed-system realisation of that circuit (it acts on every computational
  basis state by the circuit's classical denotation `Concrete.mcNotDenote gs`); and (iii) `U` sends
  `|x⟩|0⟩` to `|x⟩|Hx⟩`. Without (i)+(ii) the bare `∃ U, U|x⟩|0⟩ = |x⟩|Hx⟩` would be vacuous — for
  *any* target `f`, the partial isometry `|x⟩|0⟩ ↦ |x⟩|f(x)⟩` extends to some unitary — so the
  "composed entirely of controlled-NOTs" content must live in the theorem's type, not merely in a
  detached certificate. The witness is `gs := Concrete.parityCnotCircuit H`, whose gate structure
  (`parityCnotCircuit_card_controls`, `parityCnotCircuit_target_notMem_controls`) and syndrome
  denotation (`mcNotDenote_parityCnotCircuit_append`) are the reusable Concrete facts.

* **`H` as its entry function.** A parity-check matrix over `Fin 2` is exactly a
  `Fin k → Fin n → Fin 2`, and `(Hx)ᵢ = ∑ⱼ H i j · xⱼ` is exactly the matrix–vector product `H *ᵥ x`
  read out entrywise. Stating it this way names only plain indexed data while capturing the full
  content of "compute `|x⟩|Hx⟩`".

* **Generality.** `H` is an arbitrary `k × n` matrix over `Fin 2`; no rank,
  squareness, or dimension constraint is imposed — the CNOT circuit computes `Hx` for *every* parity
  check matrix, matching the unqualified "Suppose `H` is a parity check matrix" of the exercise.
-/

noncomputable section

namespace AxQM

/-- **N&C Exercise 10.26: a CNOT circuit computing the parity-check syndrome.** For any parity-check
matrix `H : Fin k → Fin n → Fin 2`, there is a **gate list** `gs` and a unitary `Evolution U` on the
`n + k`-qubit register `qubit ^⊗ₛ (n + k)` (`n` data qubits, `k` syndrome ancillas) such that:
* every gate of `gs` is a genuine single-control controlled-NOT — control set of size one, target
  off it (`g.1.card = 1 ∧ g.2 ∉ g.1`): the circuit is *composed entirely of controlled-NOTs*;
* `U` is exactly the closed-system realisation of that circuit — it acts on every computational
  basis state `⨂ᵢ |c i⟩` by the circuit's classical denotation `Concrete.mcNotDenote gs`;
* `U` sends `|x⟩|0⟩` to `|x⟩|Hx⟩`, the syndrome `(Hx)ᵢ = ∑ⱼ H i j · xⱼ` computed mod 2 in the
  ancillas.

The witness is `gs := Concrete.parityCnotCircuit H` (one CNOT `castAdd k j → natAdd n i` per entry
`H i j = 1`) and the `U` returned by `exists_mcNotCircuitEvolution`; the three clauses are its gate
structure (`parityCnotCircuit_card_controls`, `parityCnotCircuit_target_notMem_controls`), the
framework's realisation, and the classical denotation `mcNotDenote_parityCnotCircuit_append`.
Bundling `gs` and the CNOT-only clause into the existential keeps the theorem's truth tied to the
CNOT construction — a bare `∃ U, U|x⟩|0⟩ = |x⟩|Hx⟩` holds for any target by unitary extension. -/
theorem exists_cnotEvolution_paritySyndrome {n k : ℕ} (H : Fin k → Fin n → Fin 2) :
    ∃ (gs : List (Concrete.McNotGate (n + k))) (U : Evolution (qubit ^⊗ₛ (n + k))),
      (∀ g ∈ gs, g.1.card = 1 ∧ g.2 ∉ g.1) ∧
      (∀ c : Fin (n + k) → Fin 2,
        U.evolvePure (PureState.piTensor fun i => qubitBasis (c i))
          = PureState.piTensor fun i => qubitBasis (Concrete.mcNotDenote gs c i)) ∧
      ∀ x : Fin n → Fin 2,
        U.evolvePure (PureState.piTensor fun w => qubitBasis (Fin.append x (fun _ => 0) w))
          = PureState.piTensor fun w =>
            qubitBasis (Fin.append x (fun i => ∑ j, H i j * x j) w) := by
  obtain ⟨U, hU⟩ := exists_mcNotCircuitEvolution (Concrete.parityCnotCircuit H)
    (Concrete.parityCnotCircuit_target_notMem_controls H)
  refine ⟨Concrete.parityCnotCircuit H, U,
    fun g hg => ⟨Concrete.parityCnotCircuit_card_controls H g hg,
      Concrete.parityCnotCircuit_target_notMem_controls H g hg⟩, hU, fun x => ?_⟩
  rw [hU (Fin.append x (fun _ => 0))]
  simp only [Concrete.mcNotDenote_parityCnotCircuit_append]
  rfl

end AxQM
