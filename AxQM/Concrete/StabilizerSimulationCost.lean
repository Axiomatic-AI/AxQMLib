/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit

/-!
# Concrete: the Gottesman–Knill efficiency bound — `O(n²m)` classical simulation cost

The **efficiency bound** of the Gottesman–Knill theorem (Nielsen & Chuang **Theorem 10.7**,
§10.5.4, p. 464).

Cost of classically simulating a stabilizer circuit.

N&C's argument (p. 464) is a *counting* claim: the classical computer keeps track of the `n`
generators of the stabilizer, and each allowed operation — state preparation in the computational
basis, a Hadamard / phase / controlled-`NOT` gate, a Pauli gate, or a measurement of a Pauli-group
observable — is simulated by updating that generator description "using `O(n²)` steps"; a generator
is an `n`-qubit Pauli string, so touching all `n` of them is `O(n²)` work. Summed over the `m`
operations of a computation, the total cost is `O(n²m)`.

This file formalises exactly that, following the library's established resource-bound idiom — a
**defined** `ℕ`-valued cost function together with a *uniform* polynomial ceiling (cf.
`Concrete.mcNotGateBound_isBigO_sq`, `Concrete.qftControlledRkCount`, and the sibling **Theorem
10.6** `Concrete.isPauliNormalizer_eq_smul_cliffordCircuit_bigO` with `List.length C ≤ K · n²`):

* `StabilizerOp n` — the inductive **stabiliser-computation operation** type enumerating exactly
  N&C's allowed elements: `prep`, `clifford g` (`H` / `S` / `CNOT`, reusing
  `Concrete.CliffordGate`), `pauli p`, and `measure p` (measurement of the Pauli-group observable
  `p`).
* `StabilizerComputation n := List (StabilizerOp n)` — a computation is the sequence of `m`
  operations actually executed.
* `StabilizerOp.tableauCost` — the per-operation count of elementary tableau updates: `n · (n+1)`
  for each of `prep` / `clifford` / `pauli` (update all `n` generators, each an `n`-cell Pauli
  string plus a sign), and `2 · n · (n+1)` for `measure` (a commutation-scan pass over the `n`
  generators followed by an update pass). Each is `≤ 4 · n²` (`StabilizerOp.tableauCost_le`).
* `StabilizerComputation.simCost` — the total classical simulation cost, `∑` of the per-operation
  costs.
* `exists_simCost_le_mul_sq_length` — **the `O(n²m)` headline**: a *single universal constant* `K`
  (here `4`) with `simCost prog ≤ K · n² · prog.length` for every `n` and every computation `prog`.
  The constant is uniform in both `n` and `m = prog.length`, so this is the faithful reading of
  N&C's `O(n²m)` (a per-`n` existential `K` would be vacuous).

## Design notes (fidelity)

* **Why a defined count, not an instrumented step trace.** As with `mcNotGateBound` /
  `qftControlledRkCount`, `tableauCost` is a *documented* closed-form count of the standard
  generator-tableau update for each operation, not a reduction-step counter of a Lean program. The
  companion computable tableau simulator whose per-step work this count measures — and the
  correctness of its tracked stabiliser against the actual quantum state — is treated separately
  (by `Concrete.CliffordCircuit.updatedGenerator_mulVec_toMatrix_mulVec_of_mem` for the unitary
  part and the §10.5.3 rules in `AxQM/Postulates/API/StabilizerMeasurement.lean` for measurement).

* **Classical control.** A real stabiliser computation may condition later operations on measurement
  outcomes; the `StabilizerComputation` list models the sequence of operations *actually executed*
  in one run. Classical control only selects which operations run — it changes neither the operation
  count `m` nor the `O(n²)` cost of simulating each, so the `O(n²m)` bound is control-independent.

* **Uniform `O(n²)` per operation.** N&C bound *every* listed operation by `O(n²)` steps (dominated
  by measurement). Assigning each operation a cost `≤ 4·n²` is exactly that claim; a cheaper local
  gate is still `≤ 4·n²`, so the total ceiling is faithful and not a weakening.
-/

namespace AxQM.Concrete

variable {n : ℕ}

/-- An **operation of a stabiliser computation** on the `n`-qubit register: exactly the elements
Nielsen & Chuang **Theorem 10.7** allows.

* `prep` — preparation of the computational-basis state (reset the tracked stabiliser to the trivial
  `⟨Z₁, …, Zₙ⟩`);
* `clifford g` — a Hadamard, phase (`S`), or controlled-`NOT` gate (the elementary Clifford gates
  `Concrete.CliffordGate n`);
* `pauli p` — a Pauli gate: the Pauli operator with Pauli string `p : Fin n → Fin 4` applied as a
  unitary (its tableau action changes only generator signs);
* `measure p` — a measurement of the Pauli-group observable with Pauli string `p`.

A computation is a finite sequence of these (`StabilizerComputation`), and the Gottesman–Knill
theorem asserts each is classically simulable in `O(n²)` steps. -/
inductive StabilizerOp (n : ℕ) : Type where
  /-- Prepare the computational-basis state (reset to the trivial stabiliser `⟨Z₁, …, Zₙ⟩`). -/
  | prep : StabilizerOp n
  /-- Apply an elementary Clifford gate (Hadamard, phase, or controlled-`NOT`). -/
  | clifford (g : CliffordGate n) : StabilizerOp n
  /-- Apply the Pauli gate with Pauli string `p`. -/
  | pauli (p : Fin n → Fin 4) : StabilizerOp n
  /-- Measure the Pauli-group observable with Pauli string `p`. -/
  | measure (p : Fin n → Fin 4) : StabilizerOp n

/-- A **stabiliser computation** on the `n`-qubit register: the finite sequence of `m` operations
(`StabilizerOp n`) actually executed. Its classical simulation cost is `O(n²m)`
(`exists_simCost_le_mul_sq_length`). -/
abbrev StabilizerComputation (n : ℕ) : Type := List (StabilizerOp n)

/-- The **classical cost of simulating one operation**: the number of elementary tableau-cell
updates the standard generator-tracking simulator performs. The stabiliser of an `n`-qubit state is
tracked as `n` generators, each an `n`-qubit Pauli string (`n` Pauli cells) with a `±1` sign, so a
full pass over the tableau costs `n · (n + 1)`.

* `prep`, `clifford`, `pauli` — one pass updating all `n` generators: `n · (n + 1)`.
* `measure` — a commutation-scan pass (which generators anticommute with the measured observable)
  followed by an update pass: `2 · n · (n + 1)`.

Every value is `≤ 4 · n²` (`StabilizerOp.tableauCost_le`) — N&C's uniform "`O(n²)` steps per
operation". -/
def StabilizerOp.tableauCost : StabilizerOp n → ℕ
  | .prep => n * (n + 1)
  | .clifford _ => n * (n + 1)
  | .pauli _ => n * (n + 1)
  | .measure _ => 2 * (n * (n + 1))

/-- **Each operation costs `O(n²)`.** Every `StabilizerOp.tableauCost` value is bounded by `4 · n²`,
uniformly in the operation — the faithful reading of N&C's "may all be done using `O(n²)` steps on a
classical computer". -/
theorem StabilizerOp.tableauCost_le (op : StabilizerOp n) : op.tableauCost ≤ 4 * n ^ 2 := by
  cases op <;> simp only [StabilizerOp.tableauCost] <;> nlinarith [Nat.le_self_pow two_ne_zero n]

/-- The **total classical cost of simulating a stabiliser computation**: the sum of the
per-operation tableau-update costs `StabilizerOp.tableauCost`. This is `O(n²m)` for
`m = prog.length` (`exists_simCost_le_mul_sq_length`).

(`StabilizerComputation` is a `List` abbreviation, so this is spelled `StabilizerComputation.simCost
prog` — dot notation `prog.simCost` would resolve into the `List` namespace.) -/
def StabilizerComputation.simCost (prog : StabilizerComputation n) : ℕ :=
  (prog.map StabilizerOp.tableauCost).sum

@[simp] theorem StabilizerComputation.simCost_nil :
    StabilizerComputation.simCost ([] : StabilizerComputation n) = 0 := rfl

@[simp] theorem StabilizerComputation.simCost_cons (op : StabilizerOp n)
    (prog : StabilizerComputation n) :
    StabilizerComputation.simCost (op :: prog) =
      op.tableauCost + StabilizerComputation.simCost prog := by
  simp [StabilizerComputation.simCost]

/-- **The Gottesman–Knill efficiency theorem (N&C Theorem 10.7, the `O(n²m)` headline).**
There is a *universal* constant `K` (here `4`) such that every stabiliser computation `prog` of
`m = prog.length` operations on `n` qubits is classically simulated in at most `K · n² · m`
elementary tableau updates:
`∃ K, ∀ n (prog : StabilizerComputation n), simCost prog ≤ K · n² · prog.length`.

The constant `K` is uniform in **both** `n` and `m`, so this is the faithful formalisation of N&C's
"`O(n²m)` operations on a classical computer" (a per-`n` existential `K` would be vacuous). It
follows from `StabilizerOp.tableauCost_le` (each of the `m` operations costs `≤ 4 · n²`) via
`List.sum_le_card_nsmul`. This mirrors the sibling Theorem 10.6 headline
`isPauliNormalizer_eq_smul_cliffordCircuit_bigO` (`List.length C ≤ K · n²`). -/
theorem exists_simCost_le_mul_sq_length :
    ∃ K, ∀ (n : ℕ) (prog : StabilizerComputation n),
      StabilizerComputation.simCost prog ≤ K * n ^ 2 * prog.length := by
  refine ⟨4, fun n prog => ?_⟩
  have hbound : (prog.map StabilizerOp.tableauCost).sum ≤
      (prog.map StabilizerOp.tableauCost).length • (4 * n ^ 2) := by
    refine List.sum_le_length_nsmul _ _ ?_
    intro x hx
    obtain ⟨op, _, rfl⟩ := List.mem_map.mp hx
    exact op.tableauCost_le
  calc StabilizerComputation.simCost prog = (prog.map StabilizerOp.tableauCost).sum := rfl
    _ ≤ (prog.map StabilizerOp.tableauCost).length • (4 * n ^ 2) := hbound
    _ = prog.length * (4 * n ^ 2) := by rw [List.length_map, smul_eq_mul]
    _ = 4 * n ^ 2 * prog.length := by ring

end AxQM.Concrete
