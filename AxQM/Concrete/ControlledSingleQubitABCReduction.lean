/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.ABCDecomposition

/-!
# Concrete: the controlled-`ABC` reduction of the all-`1`-controlled single-qubit gate (N&C §4.3)

(Nielsen & Chuang §4.3, p. 176–182 — Corollary 4.2, lifted to the multiply-controlled setting.)

`Concrete/ControlledSingleQubitNormalisation.lean` brought an arbitrary controlled single-qubit
gate `ctrlSingleQubit enc j c Ũ` to the **all-`1`-controlled** form `ctrlSingleQubit enc j 1 Ũ` (the
gate that applies `Ũ` to wire `j` exactly when *every* other wire is `1`). This file performs the
next step of N&C's §4.3 reduction: it rewrites that all-`1`-controlled gate as a product of
**uncontrolled single-qubit gates on wire `j`** (`singleQubitOnWire`) and
**multiply-controlled-`NOT` gates** (`ctrlSingleQubit enc j 1 X`), together with one residual
multiply-controlled *phase* gate — exactly N&C's Corollary 4.2
(`C(U) = e^{iα} A · CNOT · B · CNOT · C` with `A B C = I`), lifted from a single control wire to the
all-`1` control pattern.

## The fibrewise-gate engine (upstream)

Both `singleQubitOnWire enc j` and `ctrlSingleQubit enc j c` are **fibrewise**: they preserve each
two-dimensional fibre `{x[j↦0], x[j↦1]}` of the `j`-th bit and act on it by a `2 × 2` block
depending only on the *other* bits. That common shape — `wireGate enc j f` and its blockwise
multiplicativity `wireGate_mul` (`wireGate f * wireGate g = wireGate (fun y => f y * g y)`, since
different fibres never mix) — lives in `Concrete/ControlledSingleQubit.lean` (the common ancestor of
both gates), with the two bridges `singleQubitOnWire_eq_wireGate` (a constant block) and
`ctrlSingleQubit_eq_wireGate` (the block is `Ũ` on the controlled fibres, `1` elsewhere). This file
consumes those to derive the reduction below.

## The reduction

* `AxQM.Concrete.ctrlSingleQubit_one_mul` — the all-`1`-controlled gate is **multiplicative
  in its `2 × 2` block**: `ctrlSingleQubit enc j 1 P * ctrlSingleQubit enc j 1 Q =
  ctrlSingleQubit enc j 1 (P * Q)`. (A fixed control pattern acts as one gate then the other on the
  controlled subspace, and as the identity off it.)
* `AxQM.Concrete.ctrlSingleQubit_one_eq_abc` — **the controlled-`ABC` identity** (N&C
  Corollary 4.2, multiply-controlled): for any `2 × 2` matrices `A, B, C, X` with `A B C = I`,
  `ctrlSingleQubit enc j 1 (A X B X C)
      = singleQubitOnWire enc j A · N · singleQubitOnWire enc j B · N · singleQubitOnWire enc j C`,
  where `N = ctrlSingleQubit enc j 1 X` is the multiply-controlled gate with block `X`. On the
  all-`1` fibre both `N`s fire (as `X`), so wire `j` sees `A X B X C`; off it both `N`s are the
  identity, so wire `j` sees `A B C = I` and the gate is trivial — precisely the mechanism by which
  two multiply-controlled-`NOT`s and three *uncontrolled* single-qubit gates realise a controlled
  gate.
* `AxQM.Concrete.exists_abc_reduction_ctrlSingleQubit_one` — **the reduction of a general
  all-`1`-controlled single-qubit gate**: for any `Ũ ∈ U(2)`, the ABC decomposition
  (`exists_abc_decomposition`, `Ũ = e^{iα} A X B X C`, `A B C = I`) gives
  `ctrlSingleQubit enc j 1 Ũ = ctrlSingleQubit enc j 1 (e^{iα} • 1) ·
  (singleQubitOnWire enc j A · N · singleQubitOnWire enc j B · N · singleQubitOnWire enc j C)` with
  `N = ctrlSingleQubit enc j 1 X` (`X = pauliX`, the Pauli `X`/`NOT` block). This exhibits the gate
  as: three uncontrolled single-qubit gates on wire `j`, two
  multiply-controlled-`NOT`s, and one multiply-controlled *phase* gate
  `ctrlSingleQubit enc j 1 (e^{iα} • 1)`. The remaining N&C §4.3 work — reducing the
  multiply-controlled-`NOT` `N` (a `Cⁿ(X)`) to `Toffoli`/`CNOT` gates and the multiply-controlled
  phase to gates — is handled separately.

Used by the §4.3 reduction of Exercise 4.43's `n`-qubit lift; the statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The all-`1`-controlled gate is multiplicative in its `2 × 2` block.**
`ctrlSingleQubit enc j 1 P * ctrlSingleQubit enc j 1 Q = ctrlSingleQubit enc j 1 (P * Q)`: on the
controlled subspace (all other wires `1`) the two gates apply `Q` then `P`, i.e. `P * Q`, and off it
both are the identity. -/
theorem ctrlSingleQubit_one_mul (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlSingleQubit enc j 1 P * ctrlSingleQubit enc j 1 Q = ctrlSingleQubit enc j 1 (P * Q) := by
  simp only [ctrlSingleQubit_eq_wireGate, wireGate_mul]
  congr 1
  funext y
  split_ifs <;> simp

/-- **The controlled-`ABC` identity** (Nielsen & Chuang, Corollary 4.2, lifted to the all-`1`
control pattern). For any `2 × 2` matrices `A, B, C, X` with `A B C = I`,
`ctrlSingleQubit enc j 1 (A X B X C) = singleQubitOnWire enc j A · N · singleQubitOnWire enc j B ·
N · singleQubitOnWire enc j C`, where `N = ctrlSingleQubit enc j 1 X` is the multiply-controlled
gate with block `X`. Two multiply-controlled gates and three *uncontrolled* single-qubit gates
realise the controlled gate: on the all-`1` fibre both `N`s fire (as `X`), so wire `j` sees
`A X B X C`; off it both `N`s are the identity, so wire `j` sees `A B C = I` and nothing happens. -/
theorem ctrlSingleQubit_one_eq_abc (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (A B C X : Matrix (Fin 2) (Fin 2) ℂ) (hABC : A * B * C = 1) :
    ctrlSingleQubit enc j 1 (A * X * B * X * C)
      = singleQubitOnWire enc j A * ctrlSingleQubit enc j 1 X
        * singleQubitOnWire enc j B * ctrlSingleQubit enc j 1 X
        * singleQubitOnWire enc j C := by
  simp only [singleQubitOnWire_eq_wireGate, ctrlSingleQubit_eq_wireGate, wireGate_mul]
  congr 1
  funext y
  by_cases h : ∀ k, k ≠ j → y k = (1 : Fin m → Fin 2) k
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h, mul_one, hABC]

/-- **The reduction of a general all-`1`-controlled single-qubit gate** (Nielsen & Chuang §4.3).
For any single-qubit unitary `Ũ`, the ABC decomposition (`exists_abc_decomposition`) yields real
phase `α` and unitaries `A, B, C` with `A B C = I` such that
`ctrlSingleQubit enc j 1 Ũ = ctrlSingleQubit enc j 1 (e^{iα} • 1) · (singleQubitOnWire enc j A · N ·
singleQubitOnWire enc j B · N · singleQubitOnWire enc j C)`, with
`N = ctrlSingleQubit enc j 1 pauliX` the multiply-controlled-`NOT`. This exhibits the gate as three
uncontrolled single-qubit gates on wire `j`, two multiply-controlled-`NOT`s, and one
multiply-controlled phase gate — the §4.3 reduction to (still-controlled `NOT`s plus uncontrolled
single-qubit gates), leaving only the `Cⁿ(X)` → Toffoli and phase steps, handled separately. -/
theorem exists_abc_reduction_ctrlSingleQubit_one (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    {Ũ : Matrix (Fin 2) (Fin 2) ℂ} (hŨ : Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        ctrlSingleQubit enc j 1 Ũ
          = ctrlSingleQubit enc j 1 (Complex.exp ((α : ℂ) * Complex.I) • 1)
            * (singleQubitOnWire enc j A * ctrlSingleQubit enc j 1 pauliX
              * singleQubitOnWire enc j B * ctrlSingleQubit enc j 1 pauliX
              * singleQubitOnWire enc j C) := by
  obtain ⟨α, A, B, C, hA, hB, hC, hABC, hU⟩ := exists_abc_decomposition Ũ hŨ
  refine ⟨α, A, B, C, hA, hB, hC, ?_⟩
  rw [hU, ← smul_one_mul, ← ctrlSingleQubit_one_mul,
    ctrlSingleQubit_one_eq_abc enc j A B C pauliX hABC]

end AxQM.Concrete
