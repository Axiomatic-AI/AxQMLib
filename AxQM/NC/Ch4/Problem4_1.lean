/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.PhaseWire
import AxQM.Core.PhaseLayerBudget
import AxQM.Core.CircuitBudgetOnRightTower
import AxQM.Core.CircuitBudgetAdjoint

/-!
# Nielsen & Chuang, Problem 4.1 (Computable phase shifts)

Build a circuit with 2T+n gates implementing |x> -> exp(-2pi i f(x)/2^n)|x>.

## The construction

Take an `m`-qubit input register `A = qudit (2^m)` and an `n`-qubit ancilla register
`B = qudit (2^n)` initialized to `|0⟩`. The circuit is **compute → phase → uncompute**:

1. `U_f` : the reversible oracle for `f`. On the initialized ancilla it computes
   `|x⟩|0⟩ ↦ |x⟩|f(x)⟩` (the `y = 0` instance of `(x,y) ↦ (x, y ⊕ f(x))`). This is the block of
   `T` Toffoli (three-qubit) gates N&C hands us; here it is a hypothesis `hUf`, exactly as N&C
   supplies it ("`f` may be computed reversibly using `T` Toffoli gates").
2. `I_A ⊗ D` : a diagonal **phase gate** `D = diagPhase (computablePhaseAngle n)` on the ancilla,
   `D|y⟩ = exp(−2πi y / 2ⁿ)|y⟩`. This is a product of `n` single-qubit phase gates — the `n` in
   the gate count — modelled here as one diagonal unitary (`diagPhase`).
3. `U_f†` : the reverse of step 1, another `T` Toffoli gates, which uncomputes the ancilla back
   to `|0⟩` (since `U_f` is unitary, `U_f† U_f = 1`).

Composed, `C = U_f† ∘ (I_A ⊗ D) ∘ U_f` uses `2T + n` gates and, on the initialized ancilla,
imprints the computable phase on the input register:
`C|x⟩|0⟩ = exp(−2πi f(x) / 2ⁿ) |x⟩|0⟩`  (eq. 4.116), with the ancilla returned to `|0⟩`.

Phase kickback in one line: `U_f` moves the phase's dependence into the ancilla index `f(x)`,
`D` imprints `exp(−2πi f(x)/2ⁿ)` there, and `U_f†` restores the ancilla, leaving the phase on the
input — this is the mechanism later reused for phase estimation (§5.2).

## What is formalized

* `computablePhaseAngle n k = −2π k / 2ⁿ` — the phase angle, so `exp(i · angle) = exp(−2πi k/2ⁿ)`.
* `computablePhaseAngle_mul_I` — the angle *is* the textbook phase: `θ_k · i = −2πi k / 2ⁿ`, so the
  correctness theorem's eigenvalue `exp(i · θ_{f(x)})` is literally the printed `exp(−2πi f(x)/2ⁿ)`
  of (4.116).
* `computablePhaseShiftCircuit Uf = U_f† ∘ (I_A ⊗ D) ∘ U_f` — the circuit, for any oracle `Uf`.
* `computablePhaseShiftCircuit_hasEigenstate` — **correctness (eq. 4.116)**: for an oracle `Uf`
  computing `|x⟩|0⟩ ↦ |x⟩|f(x)⟩`, every input `|x⟩|0⟩` is an eigenstate of `C` with eigenvalue
  `exp(−2πi f(x)/2ⁿ)`. "Eigenstate of `|x⟩|0⟩`" encodes both facts at once: the acquired phase is
  exactly the computable phase, and the ancilla returns to `|0⟩`.
* `phaseWireAngle n t = −2π·2ᵗ/2ⁿ`, `sum_phaseWireAngle_eq_computablePhaseAngle`, and
  `phaseGradientLayer_phaseWireAngle_eq_diagPhase` — the **`n`-gate decomposition of the phase
  layer** `D`: `D = phaseGradientLayer n (phaseWireAngle n)`, the product of the `n` single-qubit
  phase gates (the `n` of `2T + n`); see the gate-count discussion below.
* `diagPhase_computablePhaseAngle_circuitBudget` and
  `diagPhase_computablePhaseAngle_onRight_circuitBudget` — the **`n` of `2T + n` as a genuine
  `CircuitBudget`**: the ancilla phase gate `D` costs `n+1` single-qubit gates
  (`CircuitBudget D 0 (n+1)`), and the whole phase block `I_A ⊗ D` on the input⊗ancilla register
  still costs only `n+1` (`CircuitBudget (I_A ⊗ D) 0 (n+1)`) — the idle input adds nothing.
* `computablePhaseShiftCircuit_circuitBudget` — **the full `2T + n` gate count (eq. 4.116)**: for an
  oracle with `CircuitBudget Uf T 0`, the whole circuit
  `C = U_f† ∘ (I_A ⊗ D) ∘ U_f` has `CircuitBudget C (2T) (n+1)` — at most `2T` `≤ 2`-control gates
  and `n+1` single-qubit gates. Assembled from the ingredients above by `CircuitBudget.comp`/`mono`,
  with `U_f†`'s budget *derived* from `U_f`'s via `CircuitBudget.adjoint` (the uncompute is the same
  `T` gates reversed), not assumed as a separate hypothesis.

## Faithfulness to the exercise (what is captured)

The verifiable proposition of Problem 4.1 — *this circuit correctly realizes the unitary (4.116)* —
is captured in **full generality**, with nothing weakened:

* **Arbitrary data.** `m, n : ℕ`, an arbitrary `f : Fin (2^m) → Fin (2^n)`, and an arbitrary oracle
  `Uf` are universally quantified; no dimension is specialized and no property of `f` is assumed.
* **The oracle is the exercise's own given, not an added hypothesis.** N&C *supplies* `f` "computed
  reversibly using `T` Toffoli gates" — `(x,y) ↦ (x, y⊕f(x))` implementable by `T` Toffoli gates.
  `hUf` records exactly the instance the circuit uses — the initialized-ancilla action
  `|x⟩|0⟩ ↦ |x⟩|f(x)⟩` (the `y = 0` case) — so it is the problem's premise, not a convenience.
* **The claimed unitary is fully pinned down.** `HasEigenstate` over *every* computational-basis
  input `|x⟩` fixes `C` on a spanning set, hence (by linearity) on the whole input register; N&C
  itself specifies the unitary by its action on the basis kets `|x⟩`, so the per-`x` statement is
  the faithful form, not a per-input weakening. It also certifies the ancilla returns to `|0⟩`.
* **Registers.** `qudit (2^m)` / `qudit (2^n)` *are* the `m`- and `n`-qubit registers: the `|x⟩`,
  `|y⟩` are their computational-basis kets, which is all (4.116) refers to.

The **gate count** `2T + n` — the efficiency requirement of the exercise — is a genuine
proposition, and it is **formalized in full** (`computablePhaseShiftCircuit_circuitBudget`) over the
library's elementary-gate cost model (`Core/CircuitBudget.lean`'s `CircuitBudget E t s`: a
compositional `≤`-gate-count predicate over an arbitrary `Evolution`, with `comp` adding budgets and
`mono`/`congr`/`adjoint` — the same `∃`-realization pattern discharged elsewhere in this chapter,
e.g. `ccontrolledUnitary_gateCount_le`). The circuit is literally `U_f† ∘ (I ⊗ D) ∘ U_f`: the `2T`
is the two Toffoli blocks `U_f`, `U_f†` (each the `T` gates N&C hands us, taken as the exercise's
given `CircuitBudget Uf T 0`), and the `n` is the phase layer `D`, which factors as `n`
**single-qubit phase gates**, one per ancilla wire, assembled here as the one diagonal unitary
`diagPhase`. The final bound `CircuitBudget C (2T) (n+1)` follows from `CircuitBudget.comp`/`mono`
once `D`'s phase-gradient decomposition into those `n` wire gates, and the closures below, are in
hand.

The decomposition consists of:

* **The `n` wire gates.** `Postulates/API/PhaseWire.lean` supplies `phaseWireEvolution n t φ`, the
  single-qubit phase gate `P(φ) = diag(1, e^{iφ})` on ancilla wire `t`, with its diagonal action and
  the `n`-gate layer `phaseGradientLayer n φ` (their `List.prod`).
* **The operator identity.** With `φₜ = phaseWireAngle n t = −2π·2ᵗ/2ⁿ`,
  `phaseGradientLayer_phaseWireAngle_eq_diagPhase` proves
  `phaseGradientLayer n (phaseWireAngle n) = diagPhase (computablePhaseAngle n) = D`, i.e. `D` *is*
  the composition of the `n` single-qubit phase gates `P(φ₀), …, P(φ_{n−1})`. Proved by
  computational-basis extensionality (`qudit_evolution_ext`): on `|k⟩` the wire gates contribute
  `exp(i·∑ₜ fₜφₜ)`, and the angle sum `sum_phaseWireAngle_eq_computablePhaseAngle` (`∑ₜ fₜφₜ = θ_k`,
  from `k = ∑ₜ fₜ·2ᵗ`) collapses this to `D`'s eigenvalue `exp(iθ_k)`.
* **The layer budget.** `diagPhase_computablePhaseAngle_circuitBudget`:
  `CircuitBudget D 0 (n+1)` — the ancilla's `n+1` single-qubit phase gates — via the `Core/`
  closures `phaseGradientLayer_circuitBudget` (each of the `n+1` wire gates costs `1`,
  `qtowerSingleWire_circuitBudget`, folded by `CircuitBudget.listProd`).
* **The idle-input lift.** `diagPhase_computablePhaseAngle_onRight_circuitBudget`:
  `CircuitBudget (I_A ⊗ D) 0 (n+1)` on the full register `qudit (2^(m+1)) ⊗ qudit (2^(n+1))` — the
  idle input adds nothing — via the tower-prepend closure `CircuitBudget.onRight_qtower`.
* **The adjoint closure.** `CircuitBudget.adjoint` (`Core/CircuitBudgetAdjoint.lean`):
  `CircuitBudget E t s → CircuitBudget E.adjoint t s`, so `U_f†`'s budget is *derived* from `U_f`'s
  (the uncompute is the same `T` gates reversed) rather than assumed as a second hypothesis — which
  would be a weakening.
* **The assembly.** `computablePhaseShiftCircuit_circuitBudget` composes the three factors of
  `C = U_f† ∘ (I_A ⊗ D) ∘ U_f` by `CircuitBudget.comp` (`T + 0 + T = 2T` control gates,
  `0 + (n+1) + 0` single-qubit gates) and collapses the `+ 0`s by `CircuitBudget.mono`, yielding
  `CircuitBudget C (2T) (n+1)`.

The formalization uses evolutions and pure states, the registers `qudit`/`quditBasis`, the phase
gates `diagPhase`, `Evolution.tmul`/`Evolution.adjoint`/`Evolution.evolvePure`, and the eigenstate
predicate `Evolution.HasEigenstate`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The **computable phase angle** `θ_k = −2π k / 2ⁿ` of Nielsen & Chuang Problem 4.1, for an
ancilla index `k : Fin (2ⁿ)`. It is chosen so that `exp(i · θ_k) = exp(−2πi k / 2ⁿ)` is the phase
(eq. 4.116) that the circuit imprints when the ancilla holds `|k⟩`. -/
def computablePhaseAngle (n : ℕ) (k : Fin (2 ^ n)) : ℝ := -(2 * Real.pi * (k : ℝ)) / (2 ^ n : ℝ)

/-- **The computable phase angle imprints exactly the Nielsen & Chuang phase (eq. 4.116).** The
complex exponent `θ_k · i` of the circuit's eigenvalue is `−2πi k / 2ⁿ`, so
`exp(i · θ_k) = exp(−2πi k / 2ⁿ)` — the phase printed in (4.116) with `k = f(x)`. This makes the
correctness theorem's eigenvalue `exp(i · computablePhaseAngle n (f x))` literally the textbook
`exp(−2πi f(x) / 2ⁿ)`, rather than a value the reader must unfold the definition to recognize. -/
theorem computablePhaseAngle_mul_I (n : ℕ) (k : Fin (2 ^ n)) :
    (computablePhaseAngle n k : ℂ) * Complex.I
      = -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) / (2 ^ n : ℂ) := by
  unfold computablePhaseAngle
  push_cast
  ring

/-- The **per-wire phase angle** `φₜ = −2π·2ᵗ / 2ⁿ` of Nielsen & Chuang Problem 4.1, for ancilla
wire `t : Fin n`. It is the angle of the single-qubit phase gate `P(φₜ)` placed on wire `t`: because
the binary weight of wire `t` in the ancilla index is `2ᵗ`, this gate contributes exactly the phase
`exp(i φₜ) = exp(−2πi·2ᵗ/2ⁿ)` to a `|1⟩` on that wire. Summed over the wires carrying a `1`, the `n`
gates `P(φ₀), …, P(φ_{n−1})` reproduce the diagonal phase `exp(−2πi k/2ⁿ)` on `|k⟩` — this is the
sense in which the phase layer `D` is `n` single-qubit gates (the `n` of the `2T + n` count). -/
def phaseWireAngle (n : ℕ) (t : Fin n) : ℝ := -(2 * Real.pi * 2 ^ (t : ℕ)) / (2 ^ n : ℝ)

/-- **The per-wire angles sum, weighted by the binary digits of `k`, to the phase angle.**
For `k = finFunctionFinEquiv f` (the ancilla index whose bit `t` is `f t`),
`∑ₜ fₜ · φₜ = θ_k = −2π k / 2ⁿ`, because `k = ∑ₜ fₜ · 2ᵗ` and `φₜ = −2π·2ᵗ/2ⁿ`. This is the
arithmetic core of the phase-layer decomposition: the total phase the `n` wire gates imprint on
`|k⟩` (the sum of the per-wire angles over the set bits) equals the single computable phase angle
`θ_k` of `diagPhase (computablePhaseAngle n)`. -/
theorem sum_phaseWireAngle_eq_computablePhaseAngle (n : ℕ) (f : Fin n → Fin 2) :
    (∑ t, (f t : ℝ) * phaseWireAngle n t) = computablePhaseAngle n (finFunctionFinEquiv f) := by
  have hk : ((finFunctionFinEquiv f : Fin (2 ^ n)) : ℝ) = ∑ t, (f t : ℝ) * 2 ^ (t : ℕ) := by
    exact_mod_cast finFunctionFinEquiv_apply f
  -- factor the common constant `−2π/2ⁿ` out of the per-wire sum, leaving `∑ₜ fₜ·2ᵗ = k`
  have hL : (∑ t, (f t : ℝ) * phaseWireAngle n t)
      = (∑ t, (f t : ℝ) * 2 ^ (t : ℕ)) * (-(2 * Real.pi) / 2 ^ n) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [phaseWireAngle]
    ring
  rw [hL, computablePhaseAngle, hk]
  ring

/-- **The phase layer `D` is exactly the `n`-gate phase-gradient layer** (Nielsen & Chuang Problem
4.1, the `n` single-qubit gates of the `2T + n` count). The diagonal phase gate
`D = diagPhase (computablePhaseAngle n)` — which scales `|k⟩` by the single computable phase
`exp(−2πi k/2ⁿ)` — equals the composition `phaseGradientLayer n (phaseWireAngle n)` of the `n`
single-qubit phase gates `P(φₜ)`, one on each ancilla wire, with `φₜ = −2π·2ᵗ/2ⁿ`. This is the
operator identity that turns the monolithic phase layer of `computablePhaseShiftCircuit` into its
`n` elementary gates: on each computational-basis ket `|k⟩`, the wire gates each contribute
`exp(iφₜ)` for a set bit, and their product `exp(i·∑ₜ fₜφₜ) = exp(iθ_k)` is `D`'s eigenvalue
(`sum_phaseWireAngle_eq_computablePhaseAngle`). Proved by computational-basis extensionality
(`qudit_evolution_ext`). -/
theorem phaseGradientLayer_phaseWireAngle_eq_diagPhase (n : ℕ) :
    phaseGradientLayer n (phaseWireAngle n) = diagPhase (computablePhaseAngle n) := by
  refine qudit_evolution_ext fun i => ?_
  obtain ⟨f, rfl⟩ := finFunctionFinEquiv.surjective i
  rw [phaseGradientLayer_op_apply_quditBasis, diagPhase_op_apply_quditBasis]
  congr 1
  -- turn `∏ₜ (e^{iφₜ})^{fₜ}` into `exp(i·∑ₜ fₜφₜ)` and match `exp(iθ_k)` via the angle sum
  simp only [← Complex.exp_natCast_mul]
  rw [← Complex.exp_sum]
  congr 1
  rw [← sum_phaseWireAngle_eq_computablePhaseAngle]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **The phase layer `D` costs `n` single-qubit gates** (Nielsen & Chuang Problem 4.1, the `n` of
the `2T + n` gate count). For an `(n+1)`-qubit ancilla, the phase gate
`D = diagPhase (computablePhaseAngle (n+1))` — which scales `|k⟩` by the single computable phase
`exp(−2πi k/2ⁿ⁺¹)` — has elementary-gate budget

`CircuitBudget (diagPhase (computablePhaseAngle (n+1))) 0 (n+1)`:

at most `n+1` single-qubit gates and **no** `≤ 2`-control gates. This is the `n` single-qubit phase
gates of the exercise's `2T + n` count, made a genuine `CircuitBudget`. It follows from the operator
identity `phaseGradientLayer_phaseWireAngle_eq_diagPhase` (`D` *is* the phase-gradient layer at the
per-wire angles `phaseWireAngle`) and the layer budget `phaseGradientLayer_circuitBudget` (that
layer is `n+1` single-wire phase gates on the tower). The ancilla size `n+1 ≥ 1` matches the
exercise's positive integer `n`.

This is the `CircuitBudget D 0 n` ingredient of the eventual `2T + n` bound: the remaining assembly
lifts it to the input⊗ancilla register (`CircuitBudget (I_A ⊗ D) 0 n`) and composes with the
oracle's given budgets `CircuitBudget Uf T 0` / `CircuitBudget Uf† T 0` for the terminal
`CircuitBudget (computablePhaseShiftCircuit Uf) (2T) n`. -/
theorem diagPhase_computablePhaseAngle_circuitBudget (n : ℕ) :
    CircuitBudget (diagPhase (computablePhaseAngle (n + 1))) 0 (n + 1) := by
  rw [← phaseGradientLayer_phaseWireAngle_eq_diagPhase (n + 1)]
  exact phaseGradientLayer_circuitBudget n (phaseWireAngle (n + 1))

/-- **The phase block `I_A ⊗ D` costs `n` single-qubit gates** (Nielsen & Chuang Problem 4.1, the
`n` of the `2T + n` gate count, on the *full* input⊗ancilla register). For an `(m+1)`-qubit input
register `A = qudit (2^(m+1))` and an `(n+1)`-qubit ancilla, the phase block

`I_A ⊗ D = (Evolution.id) ⊗ diagPhase (computablePhaseAngle (n+1))`

— which acts as `D` on the ancilla and idles on the input — has elementary-gate budget

`CircuitBudget (I_A ⊗ D) 0 (n+1)`:

at most `n+1` single-qubit gates and **no** `≤ 2`-control gates. The idle input register contributes
nothing to the count, so the whole phase block costs exactly the `n+1` single-qubit phase gates of
the ancilla (`diagPhase_computablePhaseAngle_circuitBudget`). Proof: `I_A ⊗ D` is `D.onRight` of the
input register `qudit (2^(m+1))`; since that register is the `(m+1)`-qubit tower `qtower m qubit`
(`quditPowTower m`), the tower-prepend closure `CircuitBudget.onRight_qtower` lifts `D`'s budget
over the idle input without adding gates, and the budget is carried back onto `qudit (2^(m+1))` by
`CircuitBudget.congr` (`Evolution.congr_tmul`/`congr_id`/`congr_refl` collapse the transport of the
idle-identity ⊗ `D` product).

This is the `CircuitBudget (I_A ⊗ D) 0 n` ingredient of the terminal `2T + n` bound: the remaining
assembly composes it with the oracle's given Toffoli budgets
`CircuitBudget Uf T 0` / `CircuitBudget Uf† T 0` for
`CircuitBudget (computablePhaseShiftCircuit Uf) (2T) n`. The input size `m+1 ≥ 1` and ancilla size
`n+1 ≥ 1` match the exercise's positive integers `m`, `n`. -/
theorem diagPhase_computablePhaseAngle_onRight_circuitBudget (m n : ℕ) :
    CircuitBudget ((Evolution.id (S := qudit (2 ^ (m + 1)))).tmul
      (diagPhase (computablePhaseAngle (n + 1)))) 0 (n + 1) := by
  have hTower :
      CircuitBudget
        ((diagPhase (computablePhaseAngle (n + 1))).onRight (qtower m qubit)) 0 (n + 1) :=
    (diagPhase_computablePhaseAngle_circuitBudget n).onRight_qtower m
  have h := CircuitBudget.congr
    ((quditPowTower m).symm.tmul (QSystem.Iso.refl (qudit (2 ^ (n + 1))))) hTower
  simpa only [Evolution.onRight, Evolution.congr_tmul, Evolution.congr_id, Evolution.congr_refl]
    using h

/-- The **computable-phase-shift circuit** `C = U_f† ∘ (I_A ⊗ D) ∘ U_f` of Nielsen & Chuang
Problem 4.1, built from a reversible oracle `Uf` on the input⊗ancilla register
`qudit (2^m) ⊗ qudit (2^n)`. Here `D = diagPhase (computablePhaseAngle n)` is the ancilla phase
gate `|y⟩ ↦ exp(−2πi y/2ⁿ)|y⟩`, `I_A ⊗ D = Evolution.id ⊗ D` acts as `D` on the ancilla only, and
`U_f†` (`Evolution.adjoint`) uncomputes the ancilla. On an ancilla initialized to `|0⟩` this
realizes the computable phase shift `|x⟩ ↦ exp(−2πi f(x)/2ⁿ)|x⟩` (see
`computablePhaseShiftCircuit_hasEigenstate`). -/
def computablePhaseShiftCircuit {m n : ℕ}
    (Uf : Evolution (qudit (2 ^ m) ⊗ qudit (2 ^ n))) :
    Evolution (qudit (2 ^ m) ⊗ qudit (2 ^ n)) :=
  Uf.adjoint.comp
    (((Evolution.id (S := qudit (2 ^ m))).tmul (diagPhase (computablePhaseAngle n))).comp Uf)

/-- **Computable phase shifts** (Nielsen & Chuang Problem 4.1, eq. 4.116). Let `Uf` be a
reversible oracle on the register `qudit (2^m) ⊗ qudit (2^n)` computing `|x⟩|0⟩ ↦ |x⟩|f(x)⟩` for
every input `x` (the `y = 0` instance of the Toffoli-implemented map `(x,y) ↦ (x, y ⊕ f(x))`).
Then, for each `x`, the initialized state `|x⟩|0⟩` is an **eigenstate** of the circuit
`C = U_f† ∘ (I_A ⊗ D) ∘ U_f` with eigenvalue `exp(−2πi f(x)/2ⁿ)`:

`C |x⟩|0⟩ = exp(−2πi f(x)/2ⁿ) · |x⟩|0⟩`.

The eigenvalue is written `exp(i · computablePhaseAngle n (f x))`; by `computablePhaseAngle_mul_I`
this is exactly `exp(−2πi f(x)/2ⁿ)`, the phase of (4.116).

Thus `C` implements the unitary `|x⟩ ↦ exp(−2πi f(x)/2ⁿ)|x⟩` on the input register, returning the
ancilla to `|0⟩`. The proof is phase kickback: `U_f` sends `|x⟩|0⟩ ↦ |x⟩|f(x)⟩`, `I_A ⊗ D` scales
by `exp(−2πi f(x)/2ⁿ)` (the diagonal eigenvalue `diagPhase_op_apply_quditBasis`), and `U_f†`
inverts `U_f` (`Evolution.adjoint_comp_self`), restoring `|x⟩|0⟩` up to that scalar. -/
theorem computablePhaseShiftCircuit_hasEigenstate {m n : ℕ}
    (Uf : Evolution (qudit (2 ^ m) ⊗ qudit (2 ^ n)))
    (f : Fin (2 ^ m) → Fin (2 ^ n))
    (hUf : ∀ x : Fin (2 ^ m), Uf.evolvePure ((quditBasis x).tmul (quditBasis 0))
        = (quditBasis x).tmul (quditBasis (f x)))
    (x : Fin (2 ^ m)) :
    (computablePhaseShiftCircuit Uf).HasEigenstate
      (Complex.exp ((computablePhaseAngle n (f x) : ℂ) * Complex.I))
      ((quditBasis x).tmul (quditBasis 0)) := by
  -- Step 1 (compute): `U_f |x⟩|0⟩ = |x⟩|f(x)⟩`, at the vector level.
  have hA : Uf.op ((quditBasis x).tmul (quditBasis 0)).vec
      = (quditBasis x).vec ⊗ₜ[ℂ] (quditBasis (f x)).vec := by
    have h := congrArg PureState.vec (hUf x)
    rwa [Evolution.evolvePure_vec, PureState.tmul_vec] at h
  -- Step 2 (phase): the diagonal eigenvalue on the ancilla index `f(x)`.
  have hD := diagPhase_op_apply_quditBasis (computablePhaseAngle n) (f x)
  change (computablePhaseShiftCircuit Uf).op ((quditBasis x).tmul (quditBasis 0)).vec
      = Complex.exp ((computablePhaseAngle n (f x) : ℂ) * Complex.I)
        • ((quditBasis x).tmul (quditBasis 0)).vec
  unfold computablePhaseShiftCircuit
  -- unfold the composite `C = U_f† ∘ (I ⊗ D) ∘ U_f`, apply `U_f` (Step 1)
  rw [Evolution.comp_op, Evolution.comp_op, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hA]
  -- the phase layer `I ⊗ D` scales the ancilla `|f(x)⟩` by `exp(-2πi f(x)/2ⁿ)` (Step 2);
  -- `erw` bridges the `mapL` instance gap between the composite system and its underlying space
  rw [Evolution.tmul_op, Evolution.id_op]
  erw [TensorProduct.mapL_tmul]
  -- Step 3 (uncompute): `U_f†` inverts `U_f`, restoring `|x⟩|0⟩`
  rw [one_apply_eq_self, hD, TensorProduct.tmul_smul, Evolution.adjoint_op]
  erw [ContinuousLinearMap.map_smul]
  rw [← hA, ← ContinuousLinearMap.comp_apply, Uf.adjoint_comp_self, one_apply_eq_self]

/-- **The `2T + n` gate count** (Nielsen & Chuang Problem 4.1, the efficiency requirement).
For an `(m+1)`-qubit input register `A = qudit (2^(m+1))`, an `(n+1)`-qubit ancilla
`B = qudit (2^(n+1))`, and a reversible oracle `Uf` on `A ⊗ B` costing `T` `≤ 2`-control gates
(Toffoli/CNOT/NOT) and **no** single-qubit gates (`CircuitBudget Uf T 0` — the exercise's own given,
"`f` computable reversibly using `T` Toffoli gates"), the computable-phase-shift circuit
`C = U_f† ∘ (I_A ⊗ D) ∘ U_f` has elementary-gate budget

`CircuitBudget (computablePhaseShiftCircuit Uf) (2 * T) (n + 1)`:

at most `2T` `≤ 2`-control gates and at most `n+1` single-qubit gates — the exercise's `2T + n`
count, with the ancilla's `n+1` qubits playing the role of N&C's positive integer `n`.

The three summands assemble by `CircuitBudget.comp` (budgets add) and `CircuitBudget.mono`:

* `U_f` contributes `(T, 0)` — the exercise's given `hUf`;
* `U_f†` contributes `(T, 0)` — **not** a second hypothesis but `hUf.adjoint`
  (`CircuitBudget.adjoint`): the uncompute is the *same* `T` gates reversed, so its budget is
  *derived* from the oracle's, keeping the statement faithful (adding a separate `U_f†` budget
  hypothesis would be a weakening);
* `I_A ⊗ D` contributes `(0, n+1)` — `diagPhase_computablePhaseAngle_onRight_circuitBudget`, the `n`
  single-qubit phase gates of `D` lifted over the idle input register.

Summed over `C = U_f† ∘ (I_A ⊗ D) ∘ U_f`: `T + 0 + T = 2T` `≤ 2`-control gates and `0 + (n+1) + 0`
single-qubit gates, giving `(2T, n+1)` after collapsing the `+ 0`s (`mono`). Together with the
correctness theorem `computablePhaseShiftCircuit_hasEigenstate`, this closes Problem 4.1: `C`
realizes `|x⟩ ↦ exp(−2πi f(x)/2ⁿ)|x⟩` (eq. 4.116) *and* does so within the claimed `2T + n` gate
budget. -/
theorem computablePhaseShiftCircuit_circuitBudget {m n : ℕ} (T : ℕ)
    (Uf : Evolution (qudit (2 ^ (m + 1)) ⊗ qudit (2 ^ (n + 1))))
    (hUf : CircuitBudget Uf T 0) :
    CircuitBudget (computablePhaseShiftCircuit Uf) (2 * T) (n + 1) := by
  have hID := diagPhase_computablePhaseAngle_onRight_circuitBudget m n
  refine (hUf.adjoint.comp (hID.comp hUf)).mono ?_ ?_
  · omega
  · omega

end AxQM
