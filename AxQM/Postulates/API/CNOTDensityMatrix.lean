/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary

/-!
# AxQM.Postulates.API — CNOT as a permutation of the density matrix (N&C Ex 4.19)

Nielsen & Chuang's Exercise 4.19: the action of the `CNOT` gate on a
two-qubit *density matrix* `ρ`, written out explicitly in the computational basis.

Explicit action of CNOT on a density matrix in the computational basis.

`CNOT` acts on a state (density operator) by conjugation, `ρ ↦ CNOT ρ CNOT†` (Postulate 5,
`Evolution.evolve`). Because `CNOT` merely *permutes* the computational basis
(`|c,t⟩ ↦ |c, t ⊕ c⟩`), conjugating `ρ` by it simply **permutes the matrix entries** by that same
permutation acting on both the row and the column index — the "rearrangement of elements" N&C
describes.

## What this file provides

* `State.twoQubitStdMatrix` — the **density matrix** of a two-qubit state in the computational
  product basis `{|i⟩ ⊗ |j⟩}` (indexed by `Fin 2 × Fin 2`), whose `(i, j)` entry is
  `⟨i|ρ|j⟩ = ⟪|i⟩, ρ|j⟩⟫`. The density-operator analogue of `Evolution.twoQubitStdMatrix`
  (N&C Ex 4.16).
* `cnotBasisPerm` — the permutation of the computational basis `(c, t) ↦ (c, t ⊕ c)` induced by
  `CNOT`, as an `Equiv.Perm (Fin 2 × Fin 2)` (`CNOT` "is a simple permutation"); it is the
  transposition swapping `|10⟩` and `|11⟩` (`cnotBasisPerm_eq_swap`), fixing `|00⟩` and `|01⟩`.
* `cnotGate_op_qubitBasis_tmul` / `cnotGate_adjoint_op_qubitBasis_tmul` — the operator `CNOT` and
  its adjoint act on the product basis by `|c,t⟩ ↦ |c, t ⊕ c⟩`. (`CNOT` is a self-inverse
  permutation of the basis, so `CNOT†` acts the same way; this is obtained from unitarity,
  `CNOT† CNOT = 1`, with no operator-algebra detour.)
* `cnotGate_evolve_twoQubitStdMatrix` — **Exercise 4.19:** the density matrix of `CNOT ρ CNOT†` is
  the density matrix of `ρ` with its rows and columns reindexed by `cnotBasisPerm`:
  `(CNOT.evolve ρ).twoQubitStdMatrix = ρ.twoQubitStdMatrix.submatrix cnotBasisPerm cnotBasisPerm`,
  i.e. entrywise `⟨(c,t)|CNOT ρ CNOT†|(c',t')⟩ = ⟨(c, t⊕c)|ρ|(c', t'⊕c')⟩`.

## Design notes

* **Statement.** The statement is the exact conjugation action `ρ ↦ CNOT ρ CNOT†` of
  the genuine gate `Evolution` on an *arbitrary* two-qubit state `ρ`, realised as an equality of
  honest `4 × 4` complex matrices (`Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`) — not a claim only on
  basis states or on a special ρ. `cnotBasisPerm` is a genuine `Equiv.Perm`, so "`CNOT` is a simple
  permutation of the matrix elements" is captured literally; `cnotBasisPerm_eq_swap` pins it down as
  the single transposition N&C's rearrangement amounts to.
* **Proof (no adjoint-of-a-matrix detour).** The entry of `CNOT ρ CNOT†` is
  `⟪|i⟩, CNOT (ρ (CNOT† |j⟩))⟫`; `adjoint_inner_left` moves the outer `CNOT` across to give
  `⟪CNOT† |i⟩, ρ (CNOT† |j⟩)⟫`. It then suffices to know `CNOT† |c,t⟩ = |c, t⊕c⟩`, which follows
  purely from `CNOT`'s basis action together with unitarity `CNOT† CNOT = 1`
  (`Evolution.adjoint_comp_self`): `CNOT†|c,t⟩ = CNOT†(CNOT|c,t⊕c⟩) = |c,t⊕c⟩` since `(t⊕c)⊕c = t`.
  This sidesteps computing the adjoint of the underlying operator (equivalently, `CNOT`'s
  self-adjointness).
* The statement of Exercise 4.19 is in `AxQM/NC/Ch4/Exercise4_19.lean`; compare `Exercise4_16`
  (the two-qubit *gate* matrix).
-/

open scoped InnerProductSpace TensorProduct

open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The density matrix of a two-qubit state in the computational basis -/

/-- The **computational-basis density matrix** of a two-qubit state `ρ`: the matrix in the product
basis `{|i⟩ ⊗ |j⟩}` (indexed by `Fin 2 × Fin 2`) whose `(i, j)` entry is the matrix element
`⟨i|ρ|j⟩ = ⟪|i⟩, ρ|j⟩⟫`. The density-operator analogue of `Evolution.twoQubitStdMatrix`
(N&C Ex 4.16); its entry formula is `State.twoQubitStdMatrix_apply`. -/
def State.twoQubitStdMatrix (ρ : State (qubit ⊗ qubit)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => inner ℂ (qubitBasis i.1 ⊗ qubitBasis i.2).vec
    (ρ.op (qubitBasis j.1 ⊗ qubitBasis j.2).vec)

/-- **Entry formula** for the two-qubit density matrix: the `(i, j)` entry of
`ρ.twoQubitStdMatrix` is the matrix element `⟪|i₁⟩⊗|i₂⟩, ρ(|j₁⟩⊗|j₂⟩)⟫` of `ρ.op`. -/
@[simp]
theorem State.twoQubitStdMatrix_apply (ρ : State (qubit ⊗ qubit)) (i j : Fin 2 × Fin 2) :
    ρ.twoQubitStdMatrix i j = inner ℂ (qubitBasis i.1 ⊗ qubitBasis i.2).vec
      (ρ.op (qubitBasis j.1 ⊗ qubitBasis j.2).vec) := rfl

/-! ### The CNOT basis permutation -/

/-- The permutation of the two-qubit computational basis induced by `CNOT`,
`(c, t) ↦ (c, t ⊕ c)` (addition in `Fin 2`), as a genuine `Equiv.Perm (Fin 2 × Fin 2)`. It is an
involution — `CNOT` flips the target twice back to itself — so it is its own inverse. This encodes
N&C's statement that `CNOT` "is a simple permutation" of the density-matrix elements. -/
def cnotBasisPerm : Equiv.Perm (Fin 2 × Fin 2) :=
  Function.Involutive.toPerm (fun p => (p.1, p.2 + p.1)) fun p => by
    obtain ⟨a, b⟩ := p
    have : b + a + a = b := by fin_cases a <;> fin_cases b <;> decide
    simp [this]

/-- The `CNOT` basis permutation sends `(c, t)` to `(c, t ⊕ c)`. -/
@[simp]
theorem cnotBasisPerm_apply (p : Fin 2 × Fin 2) : cnotBasisPerm p = (p.1, p.2 + p.1) := rfl

/-- The `CNOT` basis permutation is exactly the **transposition of `|10⟩` and `|11⟩`**, fixing
`|00⟩` and `|01⟩`: `cnotBasisPerm = swap (1,0) (1,1)`. This is the concrete "rearrangement of
elements" N&C describes — only the last two computational-basis states are exchanged. -/
theorem cnotBasisPerm_eq_swap :
    cnotBasisPerm = Equiv.swap ((1 : Fin 2), (0 : Fin 2)) ((1 : Fin 2), (1 : Fin 2)) := by
  ext p : 1
  obtain ⟨a, b⟩ := p
  fin_cases a <;> fin_cases b <;> decide

/-! ### The action of CNOT and its adjoint on the computational basis -/

/-- **`CNOT` on the computational basis (operator form):** `CNOT|c,t⟩ = |c, t ⊕ c⟩`, i.e.
`cnotGate.op` sends the vector `|c⟩ ⊗ |t⟩` to `|c⟩ ⊗ |t ⊕ c⟩`. The operator-level restatement of
`cnotGate_evolvePure_qubitBasis`. -/
theorem cnotGate_op_qubitBasis_tmul (c t : Fin 2) :
    cnotGate.op (qubitBasis c ⊗ qubitBasis t).vec = (qubitBasis c ⊗ qubitBasis (t + c)).vec := by
  rw [← Evolution.evolvePure_vec, cnotGate_evolvePure_qubitBasis]

/-- **`CNOT†` on the computational basis:** `CNOT†|c,t⟩ = |c, t ⊕ c⟩` — the adjoint acts the same
way as `CNOT`, because `CNOT` is a self-inverse permutation of the basis. Proved from `CNOT`'s basis
action and unitarity `CNOT† CNOT = 1` (`Evolution.adjoint_comp_self`), with `(t ⊕ c) ⊕ c = t`, and
so needs no operator-algebra computation of the adjoint. -/
theorem cnotGate_adjoint_op_qubitBasis_tmul (c t : Fin 2) :
    (adjoint cnotGate.op) (qubitBasis c ⊗ qubitBasis t).vec
      = (qubitBasis c ⊗ qubitBasis (t + c)).vec := by
  have hidx : t + c + c = t := by fin_cases c <;> fin_cases t <;> decide
  have key : cnotGate.op (qubitBasis c ⊗ qubitBasis (t + c)).vec
      = (qubitBasis c ⊗ qubitBasis t).vec := by
    rw [cnotGate_op_qubitBasis_tmul, hidx]
  rw [← key, ← ContinuousLinearMap.comp_apply, cnotGate.adjoint_comp_self,
    one_apply_eq_self]

/-! ### Exercise 4.19: CNOT permutes the density-matrix entries -/

/-- **Nielsen & Chuang, Exercise 4.19: `CNOT` rearranges the density-matrix elements.** Conjugating
a two-qubit density matrix `ρ` by `CNOT` (the state evolution `ρ ↦ CNOT ρ CNOT†`,
`Evolution.evolve`) permutes the computational-basis matrix entries by `cnotBasisPerm` acting on
*both* the row and the column index:
`(CNOT.evolve ρ).twoQubitStdMatrix = ρ.twoQubitStdMatrix.submatrix cnotBasisPerm cnotBasisPerm`,
i.e. entrywise `⟨(c,t)|CNOT ρ CNOT†|(c',t')⟩ = ⟨(c, t⊕c)|ρ|(c', t'⊕c')⟩`. Since `cnotBasisPerm` is
the transposition `|10⟩ ↔ |11⟩` (`cnotBasisPerm_eq_swap`), the concrete effect is to swap the third
and fourth rows, and the third and fourth columns, of the density matrix. -/
theorem cnotGate_evolve_twoQubitStdMatrix (ρ : State (qubit ⊗ qubit)) :
    (cnotGate.evolve ρ).twoQubitStdMatrix
      = ρ.twoQubitStdMatrix.submatrix cnotBasisPerm cnotBasisPerm := by
  ext i j
  simp only [Matrix.submatrix_apply, State.twoQubitStdMatrix_apply, cnotBasisPerm_apply,
    Evolution.evolve_op, ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left, cnotGate_adjoint_op_qubitBasis_tmul,
    cnotGate_adjoint_op_qubitBasis_tmul]

end AxQM
