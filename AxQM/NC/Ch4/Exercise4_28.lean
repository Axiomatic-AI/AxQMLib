/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction
import AxQM.Postulates.API.UnitarySquareRoot

/-!
# Nielsen & Chuang, Exercise 4.28 — a `C⁵(U)` gate for `U = V²` using no work qubits

**Exercise 4.28.** *For `U = V²` with `V` unitary, construct a `C⁵(U)` gate analogous to that in
Figure 4.10, but using no work qubits. You may use controlled-`V` and controlled-`V†` gates.*

Figure 4.10 builds `C⁵(U)` *with* four work qubits: a tower of Toffoli gates ANDs the five controls
into an ancilla, a single `C(U)` fires, and the tower uncomputes. This exercise asks for the same
five-fold controlled gate **without** any ancilla, at the cost of replacing the single `C(U)` by a
recursively-halved family of single-qubit-controlled gates.

## The construction

The heart is the **Barenco reduction** `mcCtrl_controlledUnitary_sq`
(`AxQM/Core/MultiControlledReduction.lean`), the no-work-qubit generalisation of Figure 4.8
(Exercise 4.21) from two controls to `k + 1`:
`Cᵏ⁺¹(W²) = Cᵏ(W) · Cᵏ(X) · C(W†) · Cᵏ(X) · C(W)`.
Every gate on the right acts on the *same* register — no work qubits — and only the leading `Cᵏ(W)`
is still multiply-controlled on a non-`X` target. Applying the reduction four times, each level
peeling one control off that leading multiplexer with a **fresh square root**, unfolds `C⁵(U)` all
the way down:

* level 1 (`k = 4`): `C⁵(V₁²)` with `V₁ = V`, leaving `C⁴(V₁)`;
* level 2 (`k = 3`): `C⁴(V₂²) = C⁴(V₁)`, leaving `C³(V₂)`;
* level 3 (`k = 2`): `C³(V₃²) = C³(V₂)`, leaving `C²(V₃)`;
* level 4 (`k = 1`): `C²(V₄²) = C²(V₃)`, leaving the single-qubit-controlled `C(V₄)`.

The surviving `C(V₄)` is single-controlled, so the fully unfolded circuit `barenco5Circuit` is built
**only** from single-qubit-controlled gates (`C(Vⱼ)`, `C(Vⱼ†)`, all acting on the register with no
ancilla) and the multiply-controlled `NOT`s `C⁴(X), C³(X), C²(X), C¹(X)` — exactly the answer
Exercise 4.28 asks for. Peeling a control off `Cᵏ(W²)` needs the square root of `W`, but the target
register carried by each multiplexer is only ever *idle*-extended (`Evolution.onRight`), which is a
composition homomorphism, so a root of the deeper gate is a root of the shallower one and the whole
tower is generated from a single chain of square roots `V₂² = V₁, V₃² = V₂, V₄² = V₃`.

## Fidelity

The exercise supplies *one* root `V` (`U = V²`); the construction needs three further roots. Rather
than assume them (which would narrow the theorem), `exists_barenco5Circuit_eq_mcCtrl` **derives**
the whole tower from `Evolution.exists_comp_self_eq` — every single-qubit unitary has a unitary
square root — so the statement applies to *every* single-qubit `U = V²` with no added hypotheses.
The gate `C⁵(U)` is `mcCtrl 5 (V.comp V)` (`= mcCtrl 4 (controlledUnitary (V.comp V))`, five
controls onto the qubit target), `V†` is the genuine adjoint gate `Evolution.adjoint`, and the
equality is a full `Evolution` identity — no on-basis-states or up-to-phase weakening.

## Ingredients

The statements use `mcCtrl`, `unCtrl`, `controlledUnitary`, `pauliXGate`,
`Evolution.onRight`/`onLeft`/`comp`/`adjoint` and `ℕ` data. `barenco5Circuit` is expressed via the
helpers `barencoTail` / `barencoReductionCircuit_eq_mux_comp_tail` (general in `k` and the target
module; they decompose `barencoReductionCircuit` and are in
`AxQM/Core/MultiControlledReduction.lean`, also used by Exercises 4.29–4.30), giving it a
transparent, `rfl`-checkable shape.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The Exercise 4.28 circuit** for `C⁵(U)`, `U = V₁²`, with no work qubits. It is the four-level
Barenco reduction with every leading multiplexer recursively expanded: the innermost layer
`barencoReductionCircuit 1 …` (a fully single-qubit-controlled `C²`-reduction on the fourth root
`V₄`) composed with the tails `barencoTail 2 …`, `barencoTail 3 …`, `barencoTail 4 V₁` of the outer
layers. Every gate is single-qubit-controlled (`C(Vⱼ)`, `C(Vⱼ†)`) or a multiply-controlled `NOT`
(`Cᵏ(X)`); all act on the six-qubit register `qtower 4 (qubit ⊗ qubit)` with no ancilla. Each `Vⱼ`
is lifted by `Evolution.onRight` over the controls it skips. -/
def barenco5Circuit (V₁ V₂ V₃ V₄ : Evolution qubit) : Evolution (qtower 4 (qubit ⊗ qubit)) :=
  (((barencoReductionCircuit 1 (((V₄.onRight qubit).onRight qubit).onRight qubit)).comp
        (barencoTail 2 ((V₃.onRight qubit).onRight qubit))).comp
      (barencoTail 3 (V₂.onRight qubit))).comp
    (barencoTail 4 V₁)

/-- **Nielsen & Chuang, Exercise 4.28 (the assembled construction).** For a square-root chain
`V₂² = V₁`, `V₃² = V₂`, `V₄² = V₃`, the five-fold controlled gate `C⁵(V₁²)` equals the explicit
no-work-qubit circuit `barenco5Circuit V₁ V₂ V₃ V₄`, which uses only single-qubit-controlled gates
and multiply-controlled `NOT`s.

Proof: apply the Barenco reduction `mcCtrl_controlledUnitary_sq` at the top level (`k = 4`), then
reduce the surviving multiplexer three more times. Each reduction rewrites `Cᵏ(Vⱼ)` (idle over the
target register): substitute the square root `Vⱼ = Vⱼ₊₁²` and push it through the idle
`Evolution.onRight` liftings (`onRight_comp`), exposing a square `(Vⱼ₊₁ ↑)²`, whereupon
`mcCtrl_controlledUnitary_sq` at `k - 1` applies — the re-index `mcCtrl k _ = mcCtrl (k-1) (C _)` is
definitional at each concrete level. -/
theorem barenco5Circuit_eq_mcCtrl (V₁ V₂ V₃ V₄ : Evolution qubit)
    (h₁ : V₂.comp V₂ = V₁) (h₂ : V₃.comp V₃ = V₂) (h₃ : V₄.comp V₄ = V₃) :
    mcCtrl 4 (controlledUnitary (V₁.comp V₁)) = barenco5Circuit V₁ V₂ V₃ V₄ := by
  -- Level 2: `C⁴(V₁)` reduces (Barenco step at 3 controls) with root `V₂`.
  have t1 : mcCtrl 4 (V₁.onRight qubit) = barencoReductionCircuit 3 (V₂.onRight qubit) := by
    rw [← h₁, ← Evolution.onRight_comp]
    exact mcCtrl_controlledUnitary_sq 3 (V₂.onRight qubit)
  -- Level 3: `C³(V₂)` reduces (step at 2 controls) with root `V₃`.
  have t2 : mcCtrl 3 ((V₂.onRight qubit).onRight qubit)
      = barencoReductionCircuit 2 ((V₃.onRight qubit).onRight qubit) := by
    rw [← h₂, ← Evolution.onRight_comp, ← Evolution.onRight_comp]
    exact mcCtrl_controlledUnitary_sq 2 ((V₃.onRight qubit).onRight qubit)
  -- Level 4: `C²(V₃)` reduces (step at 1 control) with root `V₄`, leaving single-controlled C(V₄).
  have t3 : mcCtrl 2 (((V₃.onRight qubit).onRight qubit).onRight qubit)
      = barencoReductionCircuit 1 (((V₄.onRight qubit).onRight qubit).onRight qubit) := by
    rw [← h₃, ← Evolution.onRight_comp, ← Evolution.onRight_comp, ← Evolution.onRight_comp]
    exact mcCtrl_controlledUnitary_sq 1 (((V₄.onRight qubit).onRight qubit).onRight qubit)
  rw [mcCtrl_controlledUnitary_sq 4 V₁, barencoReductionCircuit_eq_mux_comp_tail, t1,
    barencoReductionCircuit_eq_mux_comp_tail, t2, barencoReductionCircuit_eq_mux_comp_tail, t3]
  rfl

/-- **Nielsen & Chuang, Exercise 4.28 (existence, fully faithful).** For *every* single-qubit
unitary `V` — so `U = V²` — there is a no-work-qubit circuit `barenco5Circuit V V₂ V₃ V₄` equal to
`C⁵(U)`, built only from single-qubit-controlled gates (`C(V), C(V†), …, C(V₄), C(V₄†)`) and
multiply-controlled `NOT`s. The three deeper square roots `V₂² = V`, `V₃² = V₂`, `V₄² = V₃` are
obtained from `Evolution.exists_comp_self_eq` (every single-qubit gate has a unitary square root),
so no square-root hypotheses are imposed beyond the exercise's own `U = V²`. Here
`C⁵(U) = mcCtrl 5 (V.comp V)` (five controls onto the qubit target, no ancilla). -/
theorem exists_barenco5Circuit_eq_mcCtrl (V : Evolution qubit) :
    ∃ V₂ V₃ V₄ : Evolution qubit, mcCtrl 5 (V.comp V) = barenco5Circuit V V₂ V₃ V₄ := by
  obtain ⟨V₂, h₁⟩ := Evolution.exists_comp_self_eq V
  obtain ⟨V₃, h₂⟩ := Evolution.exists_comp_self_eq V₂
  obtain ⟨V₄, h₃⟩ := Evolution.exists_comp_self_eq V₃
  exact ⟨V₂, V₃, V₄, barenco5Circuit_eq_mcCtrl V V₂ V₃ V₄ h₁ h₂ h₃⟩

end AxQM
