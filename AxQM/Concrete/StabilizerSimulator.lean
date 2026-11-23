/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerSimulationCost
import AxQM.Concrete.CliffordStabilizerTracking
import AxQM.Concrete.StabilizerGeneratorFlip
import AxQM.Concrete.PauliStringEncodingLayers
import AxQM.Concrete.PauliNormalizerRestrict

/-!
# Concrete: the stabiliser tableau simulator and its unitary-fragment correctness

The **correctness of the classical stabiliser simulator** underlying the
Gottesman–Knill theorem (Nielsen & Chuang **Theorem 10.7**, §10.5.4, p. 464), for the *unitary
fragment* of a stabiliser computation.

N&C's proof runs a classical simulation that "keep[s] track of the generators of the stabiliser":
the state of an `n`-qubit stabiliser computation is described by `n` generators, each an `n`-qubit
Pauli string with a `±1` sign, and every allowed operation updates that description in `O(n²)` steps
(the efficiency headline `Concrete.exists_simCost_le_mul_sq_length`, this file's sibling in
`Concrete/StabilizerSimulationCost.lean`). This file supplies the missing **correctness** half: the
tracked generators really do stabilise the actual quantum state.

The classically-tracked description is a `StabilizerTableau` (the `n` signed generators). The
simulator's per-operation update (`StabilizerOp.stepTableau`) runs *in lockstep* with the actual
raw-state evolution (`StabilizerOp.stepState`), and the invariant `StabilizerTableau.Stabilizes`
("each signed generator fixes the state vector") is **preserved** by every unitary operation:

* `zGenPauli_mulVec_compBasisZero` / `StabilizerTableau.prep_stabilizes` — **preparation**: the
  computational-basis state `|0…0⟩` is stabilised by the trivial tableau `⟨Z₁, …, Zₙ⟩`.
* `CliffordGate.smul_pauliString_mulVec_stabilizes` — **Clifford gate** (`H` / `S` / `CNOT`): the
  updated signed generator `(c · sign) • P_{act}` fixes the evolved vector `U ·ᵥ v` (Eq. (10.87),
  via `conj_mulVec_toMatrix_mulVec` and `CliffordGate.conj`).
* `pauli_smul_pauliString_mulVec_stabilizes` — **Pauli gate**: conjugation by a Pauli string flips
  only the sign (`pauliString_conj`), leaving the check row fixed; the sign-updated generator fixes
  the evolved vector.
* `StabilizerOp.step_stabilizes` — the three assembled into one preservation step, and
  `StabilizerTableau.run_stabilizes` — folded over a whole computation: for a **measurement-free**
  computation `prog`, if the tableau `T` stabilises `v` then the run's tableau
  `StabilizerTableau.run prog T` stabilises the evolved state `runState prog v`.

## Why the correctness theorem is stated for the measurement-free fragment

Measurement of a Pauli-group observable is the one allowed operation whose effect on the state is
**not** a matrix acting on a vector: it is a projective (Born-rule) collapse. Its stabiliser
update and state correctness are exactly the §10.5.3 measurement rules in
`AxQM/Postulates/API/StabilizerMeasurement.lean` (deterministic and random cases, generator
replacement).
Accordingly `StabilizerOp.stepState` / `StabilizerOp.stepTableau` carry the state and tableau
through a `measure` unchanged, and `StabilizerTableau.run_stabilizes` is stated with an explicit
measurement-free hypothesis — it is the **unitary-fragment** half of the correctness claim, which
together with the measurement rules gives Theorem 10.7. This is a component of the correctness
statement, not a weakening of it.
-/

open scoped Matrix

namespace AxQM.Concrete

noncomputable section

variable {n : ℕ}

/-- The **all-zeros computational-basis vector** `|0…0⟩` on the `n`-qubit register, as a raw vector
`(Fin n → Fin 2) → ℂ`: the standard basis vector `Pi.single 0 1` supported at the all-zeros bit
string. This is the state prepared by `StabilizerOp.prep`. -/
def compBasisZero (n : ℕ) : (Fin n → Fin 2) → ℂ := Pi.single 0 1

/-- **`Z_j` fixes `|0…0⟩`.** Every pure-`Z` generator `Zⱼ` stabilises the all-zeros
computational-basis vector: `pauliString (zGenPauli j) ·ᵥ |0…0⟩ = |0…0⟩`. On the all-zeros column a
`Z` factor is indistinguishable from `I` (both act as `+1` on `|0⟩`), so the column of
`pauliString (zGenPauli j)` at the all-zeros index is again the all-zeros indicator. This is the
preparation fact for the stabiliser simulator. -/
theorem zGenPauli_mulVec_compBasisZero (j : Fin n) :
    (pauliString (zGenPauli j)).mulVec (compBasisZero n) = compBasisZero n := by
  rw [compBasisZero, Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, pauliString_apply, Pi.single_apply]
  simp only [Pi.zero_apply]
  have hfac : ∀ k, pauli (zGenPauli j k) (i k) (0 : Fin 2)
      = if i k = (0 : Fin 2) then (1 : ℂ) else 0 := by
    intro k
    simp only [zGenPauli, Function.update_apply, Pi.zero_apply]
    rcases eq_or_ne k j with hk | hk
    · rw [ite_eq_left hk, show pauli 3 = pauliZ from rfl, pauliZ_apply']
      rcases eq_or_ne (i k) (0 : Fin 2) with hik | hik <;> simp [hik]
    · rw [ite_eq_right hk, show pauli 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
        Matrix.one_apply]
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_boole]
  simp only [Finset.mem_univ, forall_true_left]
  by_cases hi : i = 0
  · subst hi; simp
  · rw [ite_eq_right, ite_eq_right hi]
    intro h
    exact hi (funext h)

/-! ### The stabiliser tableau -/

/-- A **stabiliser tableau** on the `n`-qubit register: the classical description the
Gottesman–Knill simulator tracks — `n` generators `gen i` (each a Pauli string `Fin n → Fin 4`),
together
with the `±1` sign `sign i` of each. It represents the signed generator family
`(sign i • pauliString (gen i))ᵢ`. -/
structure StabilizerTableau (n : ℕ) where
  /-- The `n` generators, each a phase-free Pauli string (a check-matrix row). -/
  gen : Fin n → Fin n → Fin 4
  /-- The `±1` sign carried by each generator. -/
  sign : Fin n → ℂ

/-- The tableau **stabilises** the vector `v` when every signed generator fixes it:
`(sign i • pauliString (gen i)) ·ᵥ v = v` for all `i`. This is the simulator's correctness
invariant — "the tracked generators are a genuine stabiliser of the state". -/
def StabilizerTableau.Stabilizes (T : StabilizerTableau n) (v : (Fin n → Fin 2) → ℂ) : Prop :=
  ∀ i, (T.sign i • pauliString (T.gen i)).mulVec v = v

/-- The **trivial preparation tableau** `⟨Z₁, …, Zₙ⟩`: generator `i` is the pure-`Z` string `Zᵢ`
(`zGenPauli i`) with sign `+1`. This is the stabiliser of the computational-basis state `|0…0⟩`
produced by `StabilizerOp.prep`. -/
def StabilizerTableau.prep (n : ℕ) : StabilizerTableau n where
  gen := zGenPauli
  sign := fun _ => 1

/-- **Preparation is correct.** The trivial tableau `⟨Z₁, …, Zₙ⟩` stabilises the all-zeros
computational-basis state `|0…0⟩`. Immediate from `zGenPauli_mulVec_compBasisZero`. -/
theorem StabilizerTableau.prep_stabilizes :
    (StabilizerTableau.prep n).Stabilizes (compBasisZero n) := by
  intro i
  simp only [StabilizerTableau.prep, one_smul]
  exact zGenPauli_mulVec_compBasisZero i

/-! ### Per-operation preservation of the stabiliser invariant -/

/-- **Clifford tracking, one signed generator.** If the signed Pauli string `c • P_a` fixes `v`,
then applying an elementary Clifford gate `g` updates the generator to
`(c · g.sign a) • P_{g.act a}` — its check row `g.act a` and sign `c · g.sign a` — which fixes the
evolved vector `g.toMatrix ·ᵥ v`.
This is Eq. (10.87) at the level of one signed generator: `conj_mulVec_toMatrix_mulVec` (unitarity
`g.toMatrix · g.toMatrixᴴ = 1`) applied to the conjugation identity `CliffordGate.conj`. -/
theorem CliffordGate.smul_pauliString_mulVec_stabilizes (g : CliffordGate n) (c : ℂ)
    (a : Fin n → Fin 4) {v : (Fin n → Fin 2) → ℂ}
    (hv : (c • pauliString a).mulVec v = v) :
    ((c * g.sign a) • pauliString (g.act a)).mulVec (g.toMatrix.mulVec v)
      = g.toMatrix.mulVec v := by
  have hconj : g.toMatrix * (c • pauliString a) * g.toMatrixᴴ
      = (c * g.sign a) • pauliString (g.act a) := by
    rw [mul_smul_comm, smul_mul_assoc, g.conj, smul_smul]
  rw [← hconj]
  exact conj_mulVec_toMatrix_mulVec g.mul_conjTranspose hv

/-- **Pauli tracking, one signed generator.** If the signed Pauli string `c • P_a` fixes `v`, then
applying the Pauli gate `P_p` flips only the sign — conjugation by a Pauli string leaves the check
row fixed and multiplies by the commutation sign `(-1)^{pauliAnticommCount p a}`
(`pauliString_conj`) — so the sign-updated generator `(c · (-1)^{…}) • P_a` fixes the evolved
vector `P_p ·ᵥ v`. The Pauli
gate is the sign-only (`act = id`) case of Eq. (10.87), using involutivity `P_p · P_pᴴ = 1`. -/
theorem pauli_smul_pauliString_mulVec_stabilizes (p : Fin n → Fin 4) (c : ℂ)
    (a : Fin n → Fin 4) {v : (Fin n → Fin 2) → ℂ}
    (hv : (c • pauliString a).mulVec v = v) :
    ((c * (-1) ^ pauliAnticommCount p a) • pauliString a).mulVec ((pauliString p).mulVec v)
      = (pauliString p).mulVec v := by
  have hU : pauliString p * (pauliString p)ᴴ = 1 := by
    rw [(pauliString_isHermitian p : (pauliString p)ᴴ = pauliString p)]
    exact pauliString_mul_self p
  have hconj : pauliString p * (c • pauliString a) * (pauliString p)ᴴ
      = (c * (-1) ^ pauliAnticommCount p a) • pauliString a := by
    rw [mul_smul_comm, smul_mul_assoc,
      show ((pauliString p)ᴴ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
        = star (pauliString p) from rfl, pauliString_conj, smul_smul]
  rw [← hconj]
  exact conj_mulVec_toMatrix_mulVec hU hv

/-! ### The simulator: per-operation update and the full run -/

/-- Whether a stabiliser operation is a **measurement** (`measure p`). The correctness theorem
`StabilizerTableau.run_stabilizes` is scoped to measurement-free computations; see the module
docstring. -/
def StabilizerOp.IsMeasurement : StabilizerOp n → Prop
  | .measure _ => True
  | _ => False

/-- The **actual raw-state evolution** of one stabiliser operation on the `n`-qubit register:
`prep` prepares `|0…0⟩`, a Clifford / Pauli gate applies its unitary matrix, and `measure` carries
the state through unchanged (its Born-rule collapse is the physics engine of §10.5.3 — see the
module docstring). -/
def StabilizerOp.stepState : StabilizerOp n → ((Fin n → Fin 2) → ℂ) → ((Fin n → Fin 2) → ℂ)
  | .prep, _ => compBasisZero n
  | .clifford g, v => g.toMatrix.mulVec v
  | .pauli p, v => (pauliString p).mulVec v
  | .measure _, v => v

/-- The **classical tableau update** of one stabiliser operation — the Gottesman–Knill simulator's
per-operation step: `prep` resets to the trivial tableau `⟨Z₁, …, Zₙ⟩`, a Clifford gate `g` maps
each generator's check row by `g.act` and sign by `· g.sign`, a Pauli gate `p` flips each
generator's sign
by `(-1)^{pauliAnticommCount p ·}` (check row unchanged), and `measure` carries the tableau through
unchanged (its genuine generator-replacement update is the §10.5.3 physics engine). -/
def StabilizerOp.stepTableau : StabilizerOp n → StabilizerTableau n → StabilizerTableau n
  | .prep, _ => StabilizerTableau.prep n
  | .clifford g, T => ⟨fun i => g.act (T.gen i), fun i => T.sign i * g.sign (T.gen i)⟩
  | .pauli p, T => ⟨T.gen, fun i => T.sign i * (-1) ^ pauliAnticommCount p (T.gen i)⟩
  | .measure _, T => T

/-- **One preservation step.** If a stabiliser operation is not a measurement and the tableau `T`
stabilises `v`, then the updated tableau `op.stepTableau T` stabilises the evolved state
`op.stepState v`. Assembles the three per-operation lemmas (`prep_stabilizes`,
`CliffordGate.smul_pauliString_mulVec_stabilizes`, `pauli_smul_pauliString_mulVec_stabilizes`). -/
theorem StabilizerOp.step_stabilizes (op : StabilizerOp n) (hop : ¬ op.IsMeasurement)
    (T : StabilizerTableau n) (v : (Fin n → Fin 2) → ℂ) (hTv : T.Stabilizes v) :
    (op.stepTableau T).Stabilizes (op.stepState v) := by
  cases op with
  | prep => exact StabilizerTableau.prep_stabilizes
  | clifford g =>
      intro i
      exact g.smul_pauliString_mulVec_stabilizes (T.sign i) (T.gen i) (hTv i)
  | pauli p =>
      intro i
      exact pauli_smul_pauliString_mulVec_stabilizes p (T.sign i) (T.gen i) (hTv i)
  | measure p => exact absurd trivial hop

/-- The **tableau run** of a stabiliser computation: fold the per-operation classical update
`StabilizerOp.stepTableau` over the operation list, left to right (first operation first). -/
def StabilizerTableau.run : StabilizerComputation n → StabilizerTableau n → StabilizerTableau n
  | [], T => T
  | op :: rest, T => StabilizerTableau.run rest (op.stepTableau T)

/-- The **actual state** after running a stabiliser computation: fold the raw-state evolution
`StabilizerOp.stepState` over the operation list, left to right. -/
def runState : StabilizerComputation n → ((Fin n → Fin 2) → ℂ) → ((Fin n → Fin 2) → ℂ)
  | [], v => v
  | op :: rest, v => runState rest (op.stepState v)

/-- **The stabiliser simulator is correct on the unitary fragment (N&C Theorem 10.7).** For a
**measurement-free** stabiliser computation `prog` (state preparations and Hadamard / phase /
controlled-`NOT` / Pauli gates), if the tableau `T` stabilises the state `v`, then after running the
computation the tracked tableau `StabilizerTableau.run prog T` stabilises the actually-evolved state
`runState prog v`. So "the classical computer keeps track of the generators of the stabiliser"
(N&C §10.5.4) is **correct** for the whole unitary fragment: the tracked signed generators
`(sign i • P_{gen i})ᵢ` are a genuine stabiliser of the evolved quantum state at every step.

Starting from `StabilizerTableau.prep`/`compBasisZero` (`StabilizerTableau.prep_stabilizes`) this
propagates the invariant along any prefix of unitary operations. Measurement's stabiliser update and
its post-collapse correctness are the §10.5.3 measurement rules
(`AxQM/Postulates/API/StabilizerMeasurement.lean`); assembling the two halves gives Theorem 10.7.
By induction on `prog` from `StabilizerOp.step_stabilizes`. -/
theorem StabilizerTableau.run_stabilizes :
    ∀ (prog : StabilizerComputation n), (∀ op ∈ prog, ¬ op.IsMeasurement) →
      ∀ (T : StabilizerTableau n) (v : (Fin n → Fin 2) → ℂ),
        T.Stabilizes v → (StabilizerTableau.run prog T).Stabilizes (runState prog v) := by
  intro prog
  induction prog with
  | nil => intro _ T v hTv; exact hTv
  | cons op rest ih =>
      intro hprog T v hTv
      refine ih (fun o ho => hprog o (List.mem_cons.2 (Or.inr ho))) (op.stepTableau T)
        (op.stepState v) ?_
      exact op.step_stabilizes (hprog op (List.mem_cons.2 (Or.inl rfl))) T v hTv

end

end AxQM.Concrete
