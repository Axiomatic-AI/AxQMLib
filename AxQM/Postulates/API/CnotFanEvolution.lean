/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FourGateReversibleWire
import AxQM.Postulates.API.Evolution
import AxQM.Concrete.CnotWirePermGate

/-!
# The Figure-4.19 parity `CNOT` fan as a register `Evolution`

Nielsen & Chuang **Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit
gates" — computes the parity `⊕_{i∈S} xᵢ` of a Pauli string's support onto a single *collector*
wire `c` with a fan of `CNOT`s (Figure 4.19). At the matrix level that fan is the reverse `CNOT`
fan `Concrete.cnotFanInto c ts` (control `t ∈ ts`, target `c`), a `Concrete.CliffordCircuit`
(`Concrete/PauliStringParityCascade`). To *count* it with the elementary-gate budget `CircuitBudget`
(which addresses `Evolution`s on the qubit control tower), the fan must first be a register
`Evolution`; this file supplies it.

## What is formalised

* `cnotWireEvolution n a b` — a single `CNOT` with control `a` and target `b`, placed on the
  `2ⁿ`-level register as an `Evolution (qudit (2ⁿ))`: it is `mcNotWireEvolution n {a} b` (the
  one-control multiply-controlled `NOT`) when `a ≠ b`, and the identity when `a = b` (a
  self-targeting `CNOT` is undefined; the identity fallback makes the gate a total function of the
  two wires, exactly as `Concrete.cnotStep` returns the empty circuit for `t = c`). It is used in
  `Core/CnotFanEvolutionBudget`.

* `cnotFanIntoEvolution n c ts` — the reverse `CNOT` fan into the collector `c`, as one
  `Evolution (qudit (2ⁿ))`: the ordered product `∏_{t ∈ ts} cnotWireEvolution n t c` of the per-
  control `CNOT`s (a `List.prod` over the control list `ts`). The `Evolution` promotion of
  `Concrete.cnotFanInto c ts`; for a collector `c ∉ ts` its `ts.length` factors are genuine
  `CNOT`s (each `≤ 2`-control), the `O(n)` two-qubit gates of Figure 4.19.

The definition takes no `c ∉ ts` hypothesis: `cnotWireEvolution` is total, so the fan is a plain
`List.map … |>.prod`, which keeps the register-transport and gate-count proofs
(`Core/CnotFanEvolutionBudget`) a clean `Evolution.congr_prod` fold. The `c ∉ ts` hypothesis enters
only where it matters — the `O(n)` gate count, which needs every factor to be a real `CNOT`.

* `cnotWireEvolution_op` / `cnotFanIntoEvolution_op` — **faithfulness**: the operators of the single
  register `CNOT` and of the whole fan are exactly the Clifford matrices `(cnotStep a b).toMatrix` /
  `(cnotFanInto c ts).toMatrix` (`Concrete/PauliStringParityCascade`), reindexed from bit strings
  `Fin n → Fin 2` to the flat register `Fin (2ⁿ)` along `finFunctionFinEquiv` and promoted through
  `Matrix.toEuclideanCLM`. So the `Evolution` promotion genuinely *is* the Figure-4.19 parity
  circuit `V`, not merely some product of `CNOT`s. The single-gate case rests on the matrix bridge
  `Concrete.permGate_mcNotPerm_singleton_eq_submatrix_cnotWireGate`
  (`Concrete/CnotWirePermGate`); the fan folds it against `cnotFanInto_cons` /
  `CliffordCircuit.toMatrix_append`, with `Matrix.toEuclideanCLM`'s `map_mul` and
  `Matrix.submatrix_mul_equiv` distributing the promotion and the reindexing over the product. The
  reindex is the same `.submatrix finFunctionFinEquiv.symm` that `pauliStringStd` / `kronFamilyStd`
  use, so `cnotFanIntoEvolution_op` chains directly to the matrix-level parity collapse
  `pauliString_exp_smul_conj_cnotFanInto`.

The definitions wrap `mcNotWireEvolution` of `FourGateReversibleWire`, and the gate-count lift
`Core/CnotFanEvolutionBudget` uses `cnotWireEvolution` and `cnotFanIntoEvolution`.
-/

open scoped InnerProductSpace Matrix

namespace AxQM

noncomputable section

/-- **A single `CNOT` on register wires, control `a`, target `b`.** Placed on the `2ⁿ`-level
register `qudit (2ⁿ)` as an `Evolution`: the one-control multiply-controlled `NOT`
`mcNotWireEvolution n {a} b` when `a ≠ b` (`b ∉ {a}`), and the identity `1` when `a = b`. The
identity fallback makes `cnotWireEvolution` a total function of `(a, b)` — a self-targeting `CNOT`
being undefined — mirroring `Concrete.cnotStep`, whose circuit is empty for `t = c`. It is the
single-`CNOT` factor the parity fan `cnotFanIntoEvolution` is built from. -/
def cnotWireEvolution (n : ℕ) (a b : Fin n) : Evolution (qudit (2 ^ n)) :=
  if h : b = a then 1 else mcNotWireEvolution n {a} b (Finset.notMem_singleton.mpr h)

/-- **The reverse `CNOT` fan into a collector wire `c`, as a register `Evolution`.** The ordered
product `∏_{t ∈ ts} cnotWireEvolution n t c` of the per-control `CNOT`s `CNOT_{t→c}` (control
`t ∈ ts`, target the collector `c`), placed on the `2ⁿ`-level register `qudit (2ⁿ)`. The
`Evolution` promotion of the matrix-level fan `Concrete.cnotFanInto c ts`
(`Concrete/PauliStringParityCascade`): reading the product right-to-left is Figure 4.19's parity
accumulation, each `CNOT_{t→c}` adding `x_t` into the collector's bit. For a collector `c ∉ ts` all
`ts.length` factors are genuine `≤ 2`-control `CNOT`s, so the fan costs `ts.length` two-qubit gates
(`cnotFanIntoEvolution_circuitBudget`, `Core/CnotFanEvolutionBudget`) — the `O(n)` two-qubit gates
of Problem 4.3(3). -/
def cnotFanIntoEvolution (n : ℕ) (c : Fin n) (ts : List (Fin n)) : Evolution (qudit (2 ^ n)) :=
  (ts.map fun t => cnotWireEvolution n t c).prod

/-- **The fan on no controls is the identity.** `cnotFanIntoEvolution n c [] = 1`, the empty
`List.prod`. -/
theorem cnotFanIntoEvolution_nil (n : ℕ) (c : Fin n) : cnotFanIntoEvolution n c [] = 1 := rfl

/-- **Peeling the head control off the fan.** `cnotFanIntoEvolution n c (t :: ts)`
`= cnotWireEvolution n t c * cnotFanIntoEvolution n c ts`: the head `CNOT_{t→c}` composed before the
rest of the fan (`List.prod_cons`). The recursion the faithfulness `cnotFanIntoEvolution_op` folds
against the matrix fan's `cnotFanInto_cons`. -/
theorem cnotFanIntoEvolution_cons (n : ℕ) (c t : Fin n) (ts : List (Fin n)) :
    cnotFanIntoEvolution n c (t :: ts)
      = cnotWireEvolution n t c * cnotFanIntoEvolution n c ts := by
  simp only [cnotFanIntoEvolution, List.map_cons, List.prod_cons]

/-- **Faithfulness of a single register `CNOT`.** The operator of `cnotWireEvolution n a b` is the
Clifford `CNOT` matrix of the step `cnotStep a b` (`Concrete/PauliStringEncodingCnotLayer`),
reindexed from bit strings `Fin n → Fin 2` to the flat register `Fin (2ⁿ)` along
`finFunctionFinEquiv` and promoted through `Matrix.toEuclideanCLM`:

`(cnotWireEvolution n a b).op`
`= Matrix.toEuclideanCLM ((cnotStep a b).toMatrix.submatrix finFunctionFinEquiv.symm
    finFunctionFinEquiv.symm)`.

Two branches, matching `cnotWireEvolution` / `cnotStep`'s shared self-target guard: for `a = b` both
collapse to the identity (`quditGate` of `1`, and the empty circuit), and for `a ≠ b` the register
gate is the one-control `mcNotWireEvolution n {a} b` — whose operator is `Matrix.toEuclideanCLM` of
`permGate finFunctionFinEquiv (mcNotPerm {a} …)` (`quditGate_op`) — which the single-`CNOT` matrix
bridge `Concrete.permGate_mcNotPerm_singleton_eq_submatrix_cnotWireGate` identifies with the
reindexed `cnotWireGate a b = (cnotStep a b).toMatrix` (`Concrete.cnotStep_toMatrix_of_ne`). -/
theorem cnotWireEvolution_op (n : ℕ) (a b : Fin n) :
    (cnotWireEvolution n a b).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          ((Concrete.CliffordCircuit.toMatrix (Concrete.cnotStep a b)).submatrix
            finFunctionFinEquiv.symm finFunctionFinEquiv.symm) := by
  by_cases hab : a = b
  · -- identity branch: `a = b` collapses both the register gate and the matrix step to `1`.
    have hcw : cnotWireEvolution n a b = 1 := dite_eq_left hab.symm
    have hcs : Concrete.CliffordCircuit.toMatrix (Concrete.cnotStep a b) = 1 := by
      rw [show Concrete.cnotStep a b = [] from dite_eq_left hab]; rfl
    rw [hcw, Evolution.one_def, Evolution.id_op, hcs, Matrix.submatrix_one_equiv]
    exact (map_one _).symm
  · -- genuine `CNOT` branch: identify the register gate with the reindexed Clifford matrix.
    have hbne : ¬ (b = a) := fun h => hab h.symm
    have hbmem : b ∉ ({a} : Finset (Fin n)) := Finset.notMem_singleton.mpr hbne
    have hop : (cnotWireEvolution n a b).op
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
            (Concrete.permGate finFunctionFinEquiv (Concrete.mcNotPerm {a} hbmem)) := by
      rw [show cnotWireEvolution n a b = mcNotWireEvolution n {a} b hbmem from dite_eq_right hbne]
      exact quditGate_op _
    rw [hop, Concrete.permGate_mcNotPerm_singleton_eq_submatrix_cnotWireGate finFunctionFinEquiv
      a b hbmem, Concrete.cnotStep_toMatrix_of_ne hab]

/-- **Faithfulness of the parity `CNOT` fan `V`.** The operator of the register fan
`cnotFanIntoEvolution n c ts` is exactly the matrix fan `Concrete.cnotFanInto c ts`
(`Concrete/PauliNormalizerZClear`), reindexed from bit strings `Fin n → Fin 2` to the flat register
`Fin (2ⁿ)` along `finFunctionFinEquiv` and promoted through `Matrix.toEuclideanCLM`:

`(cnotFanIntoEvolution n c ts).op`
`= Matrix.toEuclideanCLM ((cnotFanInto c ts).toMatrix.submatrix finFunctionFinEquiv.symm
    finFunctionFinEquiv.symm)`.

This is the **faithfulness** of the `Evolution` promotion: the register fan really *is* the
Figure-4.19 parity circuit `V` of `Concrete/PauliStringParityCascade`, not merely some product of
`CNOT`s — it is what chains the Evolution-level fan to the matrix-level parity collapse
`pauliString_exp_smul_conj_cnotFanInto` (the reindex is the same `.submatrix
finFunctionFinEquiv.symm` that `pauliStringStd` / `kronFamilyStd` use, since a bit-string matrix and
the flat register are identified along `finFunctionFinEquiv`). Proved by induction on the control
list: each `cons` splits off the head `CNOT` (`cnotFanIntoEvolution_cons`; the single-gate
faithfulness `cnotWireEvolution_op`)
and matches it against the matrix fan's `cnotFanInto_cons` + `CliffordCircuit.toMatrix_append`,
distributing the reindexing over the product with `Matrix.submatrix_mul_equiv` and the operator
product with `Matrix.toEuclideanCLM`'s `map_mul`; the `nil` base is `map_one`. -/
theorem cnotFanIntoEvolution_op (n : ℕ) (c : Fin n) (ts : List (Fin n)) :
    (cnotFanIntoEvolution n c ts).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          ((Concrete.cnotFanInto c ts).toMatrix.submatrix finFunctionFinEquiv.symm
            finFunctionFinEquiv.symm) := by
  induction ts with
  | nil =>
    rw [cnotFanIntoEvolution_nil, Evolution.one_def, Evolution.id_op, Concrete.cnotFanInto_nil,
      show Concrete.CliffordCircuit.toMatrix ([] : Concrete.CliffordCircuit n) = 1 from rfl,
      Matrix.submatrix_one_equiv]
    exact (map_one _).symm
  | cons t ts ih =>
    have hsub : ((Concrete.CliffordCircuit.toMatrix (Concrete.cnotStep t c)
            * (Concrete.cnotFanInto c ts).toMatrix).submatrix
          finFunctionFinEquiv.symm finFunctionFinEquiv.symm)
        = (Concrete.CliffordCircuit.toMatrix (Concrete.cnotStep t c)).submatrix
              finFunctionFinEquiv.symm finFunctionFinEquiv.symm
            * (Concrete.cnotFanInto c ts).toMatrix.submatrix
                finFunctionFinEquiv.symm finFunctionFinEquiv.symm :=
      (Matrix.submatrix_mul_equiv _ _ finFunctionFinEquiv.symm finFunctionFinEquiv.symm
        finFunctionFinEquiv.symm).symm
    rw [cnotFanIntoEvolution_cons, Evolution.mul_def, Evolution.comp_op, ih, cnotWireEvolution_op,
      Concrete.cnotFanInto_cons, Concrete.CliffordCircuit.toMatrix_append, hsub, map_mul]
    rfl

/-- **Adjoint faithfulness of the parity `CNOT` fan (the uncomputation `V†`).** The operator of
`(cnotFanIntoEvolution n c ts).adjoint` is `Matrix.toEuclideanCLM` of the conjugate transpose of the
reindexed matrix fan `Concrete.cnotFanInto c ts`:

`(cnotFanIntoEvolution n c ts).adjoint.op`
`= Matrix.toEuclideanCLM (((cnotFanInto c ts).toMatrix.submatrix finFunctionFinEquiv.symm
    finFunctionFinEquiv.symm)ᴴ)`.

The adjoint companion of `cnotFanIntoEvolution_op`: the `Evolution` adjoint's operator is the
Hilbert-space adjoint of the fan's operator (`Evolution.adjoint_op`), which `toEuclideanCLM` carries
to the matrix conjugate transpose (`Matrix.toEuclideanCLM_conjTranspose_eq_adjoint`). This is the
faithfulness of the fan's *uncomputation* — the `V†` of the Figure-4.19 compute–rotate–uncompute
cascade (Problem 4.3(3)). -/
theorem cnotFanIntoEvolution_adjoint_op (n : ℕ) (c : Fin n) (ts : List (Fin n)) :
    (cnotFanIntoEvolution n c ts).adjoint.op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          (((Concrete.cnotFanInto c ts).toMatrix.submatrix finFunctionFinEquiv.symm
            finFunctionFinEquiv.symm)ᴴ) := by
  rw [Evolution.adjoint_op, cnotFanIntoEvolution_op]
  exact (Matrix.toEuclideanCLM_conjTranspose_eq_adjoint _).symm

end

end AxQM
