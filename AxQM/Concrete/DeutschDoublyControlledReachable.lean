/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschControlledReachable

/-!
# Concrete: doubly-controlled Deutsch gate reaches `C²(R_x β)` and `Toffoli` (N&C Ex 4.44)

Every statement is about matrices: the `2 × 2` rotations/gates (`rotX`, `pauliX`), the
once-controlled construction `controlledMat`, and Mathlib's Kronecker product `⊗ₖ`.

## Doubly-controlled matrix reachability

The universality of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44) is
assembled — following Exercise 4.43 — from a **matrix-level** development. Its once-controlled
matrix layer (`Concrete/DeutschControlledReachable.lean`) established the once-controlled generators
`S ⊗ 1` and `CNOT` as closure limits of the once-controlled Deutsch iterates. This file is its
**doubly-controlled** sibling: it lifts the same `2 × 2` cyclic-orbit density facts of
`Concrete/DeutschGateDensity.lean` through the **doubly**-controlled matrix construction
`ccontrolledMat = controlledMat ∘ controlledMat`, obtaining the two doubly-controlled generators the
assembly needs from `G` itself (the *doubly*-controlled gate):

* the **doubly-controlled `x`-rotation** `C²(R_x(β))` — which, placed on a register with its two
  control wires held at `|1⟩`, realises a bare `x`-rotation `R_x(β)` on the target wire (the first
  dense single-qubit axis of `G`);
* the **Toffoli gate** `C²(X)` — the reversible gate `G` reaches in the limit, the density
  counterpart of `deutschGate 1 = toffoliGate` (which holds *exactly* only at rational `α = 1`).

## The construction and results

* `ccontrolledMat g = controlledMat (controlledMat g)` — the **doubly-controlled gate** on
  `Fin 2 × (Fin 2 × τ)` (the two outer qubits the controls, the `τ`-system the target): `g` fires
  exactly when both control qubits are `|1⟩`. Being a composite of the once-controlled
  construction, it inherits its structure directly: `ccontrolledMat_one`, `ccontrolledMat_mul`,
  `continuous_ccontrolledMat`.
* `deutschDoublyControlledReachableMats α` — the doubly-controlled Deutsch iterates
  `{C²(iⁿ R_x(nπα))}`, the image of the cyclic orbit `⟨iR_x(πα)⟩` (`deutschTargetOrbit`) under
  `ccontrolledMat`; its forward members are the gate powers (`ccontrolledMat_iRxMat_pow_mem`).
* `ccontrolledMat_rotX_mem_closure_deutschDoublyControlledReachableMats` — **the doubly-controlled
  `x`-rotation `C²(R_x(β))`** (`α` irrational): lies in the closure of the doubly-controlled
  iterates, via `rotX β ∈ closure ⟨iR_x(πα)⟩` (`rotX_mem_closure_cyclic_iRx`) and continuity of
  `ccontrolledMat`.
* `ccontrolledMat_pauliX_mem_closure_deutschDoublyControlledReachableMats` — **the Toffoli gate
  `C²(X)`** (`α` irrational): lies in the closure of the doubly-controlled iterates, via
  `X ∈ closure ⟨iR_x(πα)⟩` (`pauliX_mem_closure_cyclic_iRx`, `X = i · R_x(π)`). That the
  doubly-controlled `X` is the Toffoli gate is recorded by
  `ccontrolledMat_pauliX_eq_controlledMat_twoQubitCNOT` (`C²(X) = C(CNOT)`, in nested-product form).

These are the doubly-controlled gates the §4.5 register assembly needs from `G`; the
once-controlled gates (`S ⊗ 1`, `CNOT`) are treated in
`Concrete/DeutschControlledReachable.lean`. This is the matrix incarnation of the operator-level
`ccontrolledUnitary_rotXGate_op_mem_closure_deutschReachableOps`
(`Postulates/API/DeutschGateReachable.lean`) and `toffoliGate_op_mem_closure_deutschReachableOps`
(`Postulates/API/DeutschGateReversible.lean`).
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-! ### The doubly-controlled matrix construction -/

/-- **The doubly-controlled gate at the matrix level.** For a target operator `g : Matrix τ τ ℂ`,
`ccontrolledMat g = controlledMat (controlledMat g)` on `Fin 2 × (Fin 2 × τ)` — the two outer
qubits are the controls and the `τ`-system the target: `g` fires exactly on the `|1⟩ ⊗ |1⟩` control
block (both controls set), the doubly-controlled operation `C²(g)`. Built as the composite of the
once-controlled construction `controlledMat` (`Concrete/DeutschControlledReachable.lean`), from
which it inherits its monoid-homomorphism and continuity structure. This is the raw-matrix analogue
of the operator-level `ccontrolledOp` (`Postulates/API/DeutschGateReachable.lean`). -/
noncomputable def ccontrolledMat (g : Matrix τ τ ℂ) :
    Matrix (Fin 2 × (Fin 2 × τ)) (Fin 2 × (Fin 2 × τ)) ℂ :=
  controlledMat (controlledMat g)

omit [Fintype τ] in
/-- **`ccontrolledMat` sends the identity to the identity:** `ccontrolledMat 1 = 1`, by applying
`controlledMat_one` twice. -/
theorem ccontrolledMat_one : ccontrolledMat (1 : Matrix τ τ ℂ) = 1 := by
  rw [ccontrolledMat, controlledMat_one, controlledMat_one]

/-- **`ccontrolledMat` is multiplicative:**
`ccontrolledMat a * ccontrolledMat b = ccontrolledMat (a * b)`, by applying the once-controlled
multiplicativity `controlledMat_mul` at both the outer and inner control. -/
theorem ccontrolledMat_mul (a b : Matrix τ τ ℂ) :
    ccontrolledMat a * ccontrolledMat b = ccontrolledMat (a * b) := by
  rw [ccontrolledMat, ccontrolledMat, ccontrolledMat, controlledMat_mul, controlledMat_mul]

omit [Fintype τ] in
/-- **`ccontrolledMat` is continuous** in its target block: it is the composite of the two
continuous once-controlled embeddings `controlledMat`. -/
theorem continuous_ccontrolledMat :
    Continuous fun g : Matrix τ τ ℂ => ccontrolledMat g :=
  (continuous_controlledMat (τ := Fin 2 × τ)).comp continuous_controlledMat

/-! ### The reachable doubly-controlled operator set of the Deutsch gate -/

/-- **The doubly-controlled reachable set of the Deutsch gate.** The doubly-controlled Deutsch
iterates `{C²(iⁿ R_x(nπα))}`, i.e. the image of the target orbit `⟨iR_x(πα)⟩`
(`deutschTargetOrbit`) under `ccontrolledMat`. Its forward members are the actual gate powers
(`ccontrolledMat_iRxMat_pow_mem`): they are obtained by iterating the Deutsch gate `G` on its
target. This is the matrix-level counterpart of the operator-level `deutschReachableOps`
(`Postulates/API/DeutschGateReachable.lean`). -/
noncomputable def deutschDoublyControlledReachableMats (α : ℝ) :
    Set (Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) :=
  ccontrolledMat '' deutschTargetOrbit α

/-- **The `k`-th doubly-controlled gate power is reachable:** `ccontrolledMat ((iR_x(πα))^k)` lies
in `deutschDoublyControlledReachableMats α`. Grounds the reachable set in the actual Deutsch gate
`G`: its members are obtained by iterating `G = C²(iR_x(πα))` on its doubly-controlled subspace. -/
theorem ccontrolledMat_iRxMat_pow_mem (α : ℝ) (k : ℕ) :
    ccontrolledMat (iRxMat (Real.pi * α) ^ k) ∈ deutschDoublyControlledReachableMats α :=
  Set.mem_image_of_mem _ (iRxMat_pow_mem_deutschTargetOrbit α k)

/-! ### The doubly-controlled `x`-rotation `C²(R_x(β))` from the Deutsch gate -/

/-- **The doubly-controlled `x`-rotation `C²(R_x(β))` is reachable from the Deutsch gate** (Nielsen
& Chuang, Exercise 4.44, matrix level). When `α` is irrational,
`ccontrolledMat (rotX β) = C²(R_x(β))` lies in the closure of the doubly-controlled Deutsch iterates
`deutschDoublyControlledReachableMats α`, for every angle `β`.

The `x`-rotation `R_x(β)` is a closure limit of the cyclic orbit `⟨iR_x(πα)⟩`
(`rotX_mem_closure_cyclic_iRx`: the phase-free iterates `(iR_x(πα))^{4k} = R_x(k·4πα)` are dense
since `2α` is irrational), and continuity of `ccontrolledMat` carries the density through the
doubly-controlled embedding (`image_closure_subset_closure_image`). Placed on a register with its
two control wires held at `|1⟩`, `C²(R_x(β))` realises a bare `x`-rotation on the target wire — the
first dense single-qubit axis of `G`. This is the matrix incarnation of the operator-level
`ccontrolledUnitary_rotXGate_op_mem_closure_deutschReachableOps`
(`Postulates/API/DeutschGateReachable.lean`). -/
theorem ccontrolledMat_rotX_mem_closure_deutschDoublyControlledReachableMats {α : ℝ}
    (hα : Irrational α) (β : ℝ) :
    ccontrolledMat (rotX β) ∈ closure (deutschDoublyControlledReachableMats α) :=
  image_closure_subset_closure_image continuous_ccontrolledMat
    (Set.mem_image_of_mem _ (rotX_mem_closure_cyclic_iRx hα β))

/-! ### The Toffoli gate `C²(X)` from the Deutsch gate -/

/-- **The doubly-controlled Pauli `X` is the Toffoli gate `C²(X)`:**
`ccontrolledMat pauliX = controlledMat twoQubitCNOT` — flipping the target with `X` conditioned on
both `|1⟩` controls, exhibited in the nested-product form `C(CNOT)` (a control gating the
once-controlled `CNOT`). Immediate from the once-controlled `controlledMat pauliX = twoQubitCNOT`
(`controlledMat_pauliX_eq_twoQubitCNOT`). -/
theorem ccontrolledMat_pauliX_eq_controlledMat_twoQubitCNOT :
    ccontrolledMat pauliX = controlledMat twoQubitCNOT := by
  rw [ccontrolledMat, controlledMat_pauliX_eq_twoQubitCNOT]

/-- **The Toffoli gate `C²(X)` is reachable from the Deutsch gate** (Nielsen & Chuang, Exercise
4.44, matrix level). When `α` is irrational, the doubly-controlled Pauli `X`,
`ccontrolledMat pauliX = C²(X)` (the Toffoli gate,
`ccontrolledMat_pauliX_eq_controlledMat_twoQubitCNOT`), lies in the closure of the doubly-controlled
Deutsch iterates `deutschDoublyControlledReachableMats α`.

The Pauli `X` is a closure limit of the cyclic orbit `⟨iR_x(πα)⟩` (`pauliX_mem_closure_cyclic_iRx`,
`X = i · R_x(π)`), and continuity of `ccontrolledMat` carries the density through. This is the
density counterpart of `deutschGate_one_eq_toffoliGate`, which gives the Toffoli gate *exactly* but
only at the rational value `α = 1`; for irrational `α`, `G` never equals `Toffoli`, yet its iterates
approximate it. It is the matrix incarnation of the operator-level
`toffoliGate_op_mem_closure_deutschReachableOps` (`Postulates/API/DeutschGateReversible.lean`). -/
theorem ccontrolledMat_pauliX_mem_closure_deutschDoublyControlledReachableMats {α : ℝ}
    (hα : Irrational α) :
    ccontrolledMat pauliX ∈ closure (deutschDoublyControlledReachableMats α) :=
  image_closure_subset_closure_image continuous_ccontrolledMat
    (Set.mem_image_of_mem _ (pauliX_mem_closure_cyclic_iRx hα))

/-- **The packing bijection `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8`** matching `ccontrolledMat`'s
right-nested `Fin 2 × (Fin 2 × Fin 2)` index type: `(c₁, c₂, t) ↦ finProdFinEquiv (c₁,
finProdFinEquiv (c₂, t))`, the big-endian packing `4·c₁ + 2·c₂ + t`. Used to reindex the
doubly-controlled matrix onto the eight-level register `Fin 8`. (Distinct from the left-nested
`ToffoliConj.triQubitEquiv : (Fin 2 × Fin 2) × Fin 2 ≃ Fin 8`.) -/
def threeQubitIndex : (Fin 2 × Fin 2 × Fin 2) ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv

/-- **The doubly-controlled gate `C²(g)` as a `Fin 8 × Fin 8` matrix.** The doubly-controlled
matrix `ccontrolledMat g` (on `Fin 2 × Fin 2 × Fin 2`) reindexed to `Fin 8` along `threeQubitIndex`
— the matrix form of `C²(g)` on the eight-level register. -/
noncomputable def ccontrolledMatFin8 (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  (ccontrolledMat g).reindex threeQubitIndex threeQubitIndex

omit [Fintype τ] in
/-- **The entrywise formula for the doubly-controlled gate `C²(g)`.** The `((a,b,s), (c,d,t))` entry
of `ccontrolledMat g` (target system `τ`, control bits in `Fin 2`) is: `0` unless the two control
bits are preserved (`a = c`, `b = d`); on that control-diagonal block it is `g s t` when both
controls are `|1⟩` (the target undergoes `g`), and the identity `δ_{s,t}` otherwise (the target is
untouched). Read off by unfolding the two Kronecker sums `controlledMat (controlledMat g)` and
casing on the four control-bit values (the target indices `s, t` stay symbolic). This is the
entrywise witness that `C²(g)` fires `g` exactly on the `|1⟩|1⟩` control block; polymorphic in `τ`
like `ccontrolledMat_mul` / `ccontrolledMat_one`, and instantiated at `τ = Fin 2` by the `Fin 8`
bridge. -/
theorem ccontrolledMat_apply (g : Matrix τ τ ℂ) (a b : Fin 2) (s : τ) (c d : Fin 2) (t : τ) :
    ccontrolledMat g (a, b, s) (c, d, t)
      = if a = c ∧ b = d then (if c = 1 ∧ d = 1 then g s t else if s = t then 1 else 0) else 0 := by
  simp only [ccontrolledMat, controlledMat, Matrix.add_apply, Matrix.kronecker_apply,
    Matrix.diagonal_apply, Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp

end AxQM.Concrete
