/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch4.Exercise4_30
import AxQM.Core.MultiControlledNotBasis
import AxQM.Core.BarencoLayerBudget
import AxQM.Concrete.MultiControlledNotAsymptotics

/-!
# Nielsen & Chuang, Exercise 4.29 — a no-work-qubit `O(n²)` circuit for `Cⁿ(X)`

*(N&C p. 184.)*

Find an O(n^2)-gate circuit implementing C^n(X) with no work qubits.

`Cⁿ(X)` is the gate `mcCtrl n pauliXGate` (the Pauli-`X` gate wrapped by `n` control qubits,
`AxQM/Core/MultiControlledReduction.lean`), acting on the `(n+1)`-qubit register `qtower n qubit` —
the `n` controls and the one target.

## What the exercise asks for, and how this file answers it

The exercise asks for a **single** circuit `C` that simultaneously (i) implements `Cⁿ(X)`, (ii) is
built from `Toffoli`/`CNOT`/single-qubit gates, (iii) has `O(n²)` gate count, and (iv) uses exactly
`n + 1` wires (no work qubit) — Barenco's Corollary 7.4. This conjoined claim is delivered by
`cnx_circuitBudget` below (plus the `O(n²)` read-off `Concrete.barencoGateBudget_isBigO_sq`), the
fusion of the two structural statements `cnx_eq_barencoNCircuit` and `cnx_evolvePure_towerKet`.

### A single `Evolution` circuit for `Cⁿ(X)` on exactly `n + 1` wires

(`cnx_eq_barencoNCircuit`.)

`Cⁿ(X) = barencoNCircuit (sqrtChain pauliXGate) k 0`, a full `Evolution` identity on exactly `n + 1`
qubits (`qtower k (qubit ⊗ qubit)`, `n = k + 1`), with **no extra/borrowed wire** — so this meets
(i) and (iv). The circuit uses single-qubit-controlled `√X`-chain gates `C(Vⱼ)`, `C(Vⱼ†)`
(`V₀ = X`, `Vⱼ₊₁ = √Vⱼ`, from `Evolution.exists_comp_self_eq`, no square-root hypotheses) — the
"single qubit gates" the exercise names — and multiply-controlled `NOT` blocks `Cᵏ(X)`. This is
Exercise 4.30 at `U = X`.

### `Cⁿ(X)` *is* the reversible permutation, with a purely-classical `O(n²)` circuit

(`cnx_evolvePure_towerKet`.)

`Cⁿ(X)` acts on **every** computational basis state `towerKet n b` exactly as the classical
multiply-controlled `NOT` `Concrete.mcNot (cnxControls n) (Fin.last n)`. Since `Cⁿ(X)` is a
permutation matrix, agreement on all basis states is full agreement, so `Cⁿ(X)` **is** that
reversible bit-string permutation, for which `AxQM/Concrete/` builds a purely
`Toffoli`/`CNOT`/`NOT` circuit of `O(n²)` gates (`Concrete.exists_mcNotCircuit`,
`Concrete.mcNotGateBound_isBigO_sq`). **Honest caveat (iv):** that permutation-only circuit needs
one wire *outside* the gate's support to borrow, so it lives on `m ≥ n + 2` wires — one dirty
borrowed ancilla (restored) — **not** the tight `n + 1` register. This is unavoidable for a
permutation-only circuit (parity, below); `cnx_circuitBudget` attains the tight register by
admitting the `√X` single-qubit gates.

### The fused answer: an `O(n²)`-gate `Cⁿ(X)` circuit on exactly `n + 1` wires

(`barencoNCircuit_circuitBudget`, `cnx_circuitBudget`; the `O(n²)` read-off is
`Concrete.barencoGateBudget_isBigO_sq`.)

The tight `n + 1`-wire circuit of `cnx_eq_barencoNCircuit` is equipped with a compositional
elementary-gate budget: `cnx_circuitBudget` gives `CircuitBudget (Cⁿ(X)) (8k(k+1)+2) (2k+3)`, i.e.
that circuit is built — on exactly `n + 1` wires, **no work qubit** — from at most
`8k(k+1)+2 = O(n²)` genuine `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`) and at most
`2k+3 = O(n)` single-qubit(-controlled) gates. The accountant is `CircuitBudget`
(`AxQM/Core/CircuitBudget.lean`): its `block` leaf certifies each internal `Cᵏ(X)` bottomed to a
**classical `≤ 2`-control gate list** on the tight register (the split-route linear reduction
borrows one *ambient* tower wire *within* the `n + 1`, no extra ancilla), and its `comp`
constructor adds the per-layer counts across the `O(n)`-layer `barencoNCircuit` recursion
(`barencoNCircuit_circuitBudget`, the fold). Reading `8k(k+1)+2 + 2k+3` off as `O(k²)` is
`Concrete.barencoGateBudget_isBigO_sq` (a `ℕ→ℝ` asymptotic statement). This is (i)∧(ii)∧(iii)∧(iv)
together — the exercise's conjoined claim.

**Scope of "single qubit gates" (honest).** The `2k+3` gates counted in the single-qubit bucket are
the `√X`-chain **controlled** gates `C(Vⱼ)`, `C(Vⱼ†)` and the base multiplexer `V₀`. A
controlled-single-qubit gate is not literally one of `{Toffoli, CNOT, single-qubit}`, but is exactly
a **constant** number of `CNOT` + single-qubit gates (Corollary 4.2 / Exercise 4.22, the ABC
decomposition) — this is what §4.3 means by building controlled gates from `CNOT` and single-qubit
gates, and is how N&C's own solution counts the controlled-`√X`s. As there are only `O(n)` of them,
the grand total in the exercise's own gate set stays `O(n²)`. Bottoming those `O(n)` gates to the
literal three-gate basis at the `Evolution` level (an arbitrary-wire ABC placement) is a purely
cosmetic `O(1)`-per-gate expansion left un-inlined, exactly as Exercise 4.30 leaves its `C(Vⱼ)`.

## The parity obstruction — why the tight register needs the `√X` gates

On exactly `n + 1` wires (`n ≥ 3`) a **permutation-only** circuit (`Toffoli`/`CNOT`/`NOT`) cannot
equal `Cⁿ(X)`: `Cⁿ(X)` is a single transposition of basis strings (**odd**), while every
`≤ 2`-control gate is `2^(m-1-k)` transpositions with `m-1-k ≥ 1` (**even**), and a product of even
permutations is even (decide-verified on `Fin 5`). Hence (a) the purely-classical circuit of
`cnx_evolvePure_towerKet` *must* borrow a wire (its support already fills the tight register), and
(b) any exactly-`(n+1)`-wire circuit for `Cⁿ(X)` *must* use non-permutation single-qubit gates — the
`√X` of `cnx_eq_barencoNCircuit` and `cnx_circuitBudget`. The obstruction does **not** touch the
exercise's claim, which permits single-qubit gates; it is precisely why the mixed-gate circuit of
`cnx_circuitBudget`, not a purely-classical one, is the tight-register answer.

## Ingredients

The statements use `mcCtrl`, `controlledUnitary`, `pauliXGate`, `barencoNCircuit`, `sqrtChain`,
`CircuitBudget`, `Evolution.evolvePure` and `towerKet`, together with the `Concrete` bit-string
model (`mcNot`, `cnxControls`) and plain `Fin`/`ℕ`. They rely on `AxQM/Concrete/MultiControlledNot*`
(including the `O(n²)` read-off `Concrete.barencoGateBudget_isBigO_sq`),
`AxQM/Core/MultiControlledNotBasis.lean` (the bridge between the quantum gate and the classical
permutation), `AxQM/Core/CircuitBudget.lean` and `AxQM/Core/BarencoLayerBudget.lean` (the gate
accounting), and Exercise 4.30 (`barencoNCircuit`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.29 (a single `Cⁿ(X)` circuit on exactly `n + 1`
wires).** For every `k`, the multiply-controlled `NOT`
`Cⁿ(X) = mcCtrl k (controlledUnitary pauliXGate)` (`n = k + 1` controls) equals the explicit circuit
`barencoNCircuit (sqrtChain pauliXGate) k 0`, a **full `Evolution` identity on exactly `n + 1`
qubits** (`qtower k (qubit ⊗ qubit)`) — no work qubit, no borrowed wire (properties (i) and (iv) of
Exercise 4.29). The circuit uses single-qubit-controlled `√X`-chain gates (`C(Vⱼ)`, `C(Vⱼ†)` with
`V₀ = X`, `Vⱼ₊₁ = √Vⱼ`) — the "single qubit gates" the exercise names, needed on the tight register
by the parity obstruction (see the file docstring).

The exercise's `Toffoli`/`CNOT` gate set (ii) and `O(n²)` count (iii) for this very circuit are
delivered by `cnx_circuitBudget`, which certifies each internal `Cᵏ(X)` block bottomed to
`≤ 2`-control gates on this register and sums the per-layer counts. This is the `U = X`
specialisation of Exercise 4.30's `barencoNCircuit_zero_eq_mcCtrl`: the chain `sqrtChain pauliXGate`
is total (every single-qubit gate has a unitary square root, from `Evolution.exists_comp_self_eq`),
so no hypotheses on `X`. -/
theorem cnx_eq_barencoNCircuit (k : ℕ) :
    mcCtrl k (controlledUnitary pauliXGate)
      = barencoNCircuit (sqrtChain pauliXGate) k 0 :=
  barencoNCircuit_zero_eq_mcCtrl (sqrtChain pauliXGate) (sqrtChain_sq pauliXGate) k

/-- **Nielsen & Chuang, Exercise 4.29 (`Cⁿ(X)` is the reversible permutation with an
`O(n²)` `Toffoli` circuit).** The `n`-controlled `NOT` `mcCtrl n pauliXGate` acts
on the `(n+1)`-qubit computational basis `towerKet n b` exactly as the classical multiply-controlled
`NOT` `Concrete.mcNot` with controls the first `n` wires (`cnxControls n`) and target the last
(`Fin.last n`). As `Cⁿ(X)` is a permutation matrix, agreement on every basis state is full
agreement, so `Cⁿ(X)` **is** that reversible bit-string permutation — the permutation for which
`Concrete.exists_mcNotCircuit` exhibits an explicit circuit of `≤ 2`-control gates
(`Toffoli`/`CNOT`/`NOT`) of length `≤ Concrete.mcNotGateBound n`, with `O(n²)` count
(`Concrete.mcNotGateBound_isBigO_sq`) — the exercise's properties (ii)/(iii).

Honest caveat: that *purely-classical* circuit needs one wire outside the gate's support to borrow,
so it lives on `m ≥ n + 2` wires (one dirty borrowed ancilla, restored), not the tight `n + 1`
register — unavoidable for a permutation-only circuit (parity, file docstring). The tight
`n + 1`-wire `O(n²)` circuit (property (iv) fused with (ii)/(iii)) is `cnx_circuitBudget`, which
reaches it by admitting the `√X` single-qubit gates. The statement here is the quantum–classical
bridge `mcCtrl_pauliXGate_evolvePure_towerKet` (`AxQM/Core/MultiControlledNotBasis.lean`). -/
theorem cnx_evolvePure_towerKet (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    (mcCtrl n pauliXGate).evolvePure (towerKet n b)
      = towerKet n (Concrete.mcNot (cnxControls n) (Fin.last n) b) :=
  mcCtrl_pauliXGate_evolvePure_towerKet n b

/-! ### The fused `O(n²)` gate count on exactly `n + 1` wires -/

/-! The whole-circuit gate budget `barencoNCircuit_circuitBudget` — for **every** single-qubit
square-root chain `V`, `CircuitBudget (barencoNCircuit V k d) (8·k·(k+1)+2) (2·k+3)`, the fold that
adds the per-layer counts across the `barencoNCircuit` recursion — is a general fact about the
Exercise 4.30 circuit, and is stated in `AxQM/NC/Ch4/Exercise4_30.lean` (imported above). The
theorem below is its `U = X` specialisation. -/

/-- **Nielsen & Chuang, Exercise 4.29 (the fused gate budget for `Cⁿ(X)` on exactly `n + 1`
wires).** The `n`-controlled `NOT` `Cⁿ(X) = mcCtrl k (controlledUnitary pauliXGate)` (`n = k + 1`)
equals — on exactly the `n + 1`-qubit register, **no work qubit** — an explicit circuit built from
at most

`8k(k+1) + 2 = O(k²)` `≤ 2`-control gates (`Toffoli`/`CNOT`/`NOT`), and
`2k + 3 = O(k)` single-qubit(-controlled) gates `C(Vⱼ)`, `C(Vⱼ†)`, `V₀`.

This fuses two facts: `cnx_eq_barencoNCircuit` gives the exact `n+1`-wire circuit identity
`Cⁿ(X) = barencoNCircuit (√X-chain) k 0` [(i) + (iv)], and the budget below equips that very
circuit with a compositional elementary-gate budget [(ii) + the count for (iii)], obtained by
transporting the whole-circuit budget `barencoNCircuit_circuitBudget` across that identity. The
single-qubit-*controlled* gates `C(Vⱼ)` are not literally in the exercise's `{Toffoli, CNOT,
single-qubit}` set, but each is a **constant** number of `CNOT` + single-qubit gates (Corollary 4.2
/ Exercise 4.22, the ABC decomposition); there are only `O(n)` of them, so the grand total in the
exercise's own gate set stays `O(n²)`, via
`Concrete.barencoGateBudget_isBigO_sq`. -/
theorem cnx_circuitBudget (k : ℕ) :
    CircuitBudget (mcCtrl k (controlledUnitary pauliXGate))
      (8 * k * (k + 1) + 2) (2 * k + 3) := by
  rw [cnx_eq_barencoNCircuit]
  exact barencoNCircuit_circuitBudget (sqrtChain pauliXGate) k 0

/-! The `O(n²)` read-off of `cnx_circuitBudget`'s counts — that the total
`(8k(k+1)+2) + (2k+3)` is `O(k²)` — is `Concrete.barencoGateBudget_isBigO_sq`. It is a pure `ℕ→ℝ`
asymptotic statement, in `AxQM/Concrete/MultiControlledNotAsymptotics.lean` (alongside
`Concrete.mcNotGateBound_isBigO_sq`); it is the exercise's `O(n²)` reading. -/

end AxQM
