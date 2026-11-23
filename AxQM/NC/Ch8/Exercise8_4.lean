/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledFlipOperatorSum

/-!
# Nielsen & Chuang, Exercise 8.4 (Measurement — operator-sum of the controlled-flip channel)

*(N&C p. 361.)*

Give operator-sum representation for U=P0⊗I+P1⊗X with environment starting in |0⟩.

## The formalisation

With the environment prepared in `|0⟩`, the process is the quantum operation
`E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)` (N&C eq. 8.6). Its operation elements are `Eₖ = ⟨eₖ| U |0⟩`,
and for this `U` they are exactly the computational-basis projectors `E₀ = P₀`, `E₁ = P₁`, so the
**answer** is the operator-sum representation

`E(ρ) = P₀ ρ P₀ + P₁ ρ P₁`   (N&C eq. 8.7),

the completely dephasing (decoherence) channel — it measures the system in the computational basis
and discards the outcome — with the completeness relation `E₀† E₀ + E₁† E₁ = P₀ + P₁ = I`
(N&C eq. 8.14) certifying that `E` is trace preserving. (`U` is the controlled-`X` — CNOT — of
N&C Fig. 8.4, with the principal system controlling the environment's flip.) The statement is
`AxQM.Concrete.dephasingOperation_eq_operatorSum`.

The object the exercise asks for — the *operator-sum representation* of a specific channel — is a
computation on operators of the qubit's Hilbert space: the operation elements
`Eₖ = ⟨eₖ| U |e₀⟩` and the map `E(ρ) = Σₖ Eₖ ρ Eₖ†` involve `LinearMap`s and the abstract partial
trace. Compare Problem 8.1 (amplitude damping, `AxQM/NC/Ch8/Problem8_1.lean`) and Problem 8.2
(`AxQM/NC/Ch8/Problem8_2.lean`).

## Supporting results

The formalisation uses the following files.

* `ToMathlib/Analysis/InnerProductSpace/OperatorSum.lean` (Exercise 8.3) — the general
  operator-sum machinery used here: the operation elements
  `LinearMap.krausOp b V k` of a dilation `V`, and the reduction
  `LinearMap.partialTraceRight_conj_eq_sum_krausOp` giving `tr_env(V ρ V†) = Σₖ Eₖ ρ Eₖ†`
  (N&C eqs. 8.9–8.10), together with the environment-embedding `LinearMap.embedRight`.
* `AxQM/Concrete/QubitBasisOperators.lean` — abstract-qubit operators over an arbitrary
  2-dimensional `H` with a chosen `b : OrthonormalBasis (Fin 2) ℂ H`: the projectors
  `Concrete.qubitProj` (`Pᵢ = |i⟩⟨i|`) and bit-flip `Concrete.qubitFlip` (`X = |0⟩⟨1| + |1⟩⟨0|`),
  with their algebra `qubitProj_comp_qubitProj` (orthogonal idempotence), `sum_qubitProj`
  (`P₀ + P₁ = I`), `adjoint_qubitProj`, `adjoint_qubitFlip`, and `qubitFlip_comp_qubitFlip`
  (`X² = I`). Also used in Exercises 8.5, 8.20 and 8.24.
* `AxQM/Concrete/ControlledFlipOperatorSum.lean` — the exercise proper:
    - `Concrete.controlledFlip` — the interaction `U = P₀ ⊗ I + P₁ ⊗ X` (eq. 8.16), shown
      self-adjoint (`adjoint_controlledFlip`) and involutive (`controlledFlip_comp_self`), hence
      unitary (`adjoint_controlledFlip_comp_self`) — the exercise's premised unitary interaction;
    - `Concrete.controlledFlipDilation` — the dilation `V = U(· ⊗ |0⟩)`;
    - `Concrete.dephasingOperation` — the quantum operation `E(ρ) = tr_env(V ρ V†)`, with
      `dephasingOperation_eq_envModel` exhibiting it in N&C's eq. (8.6) form
      `tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`;
    - `Concrete.krausOp_controlledFlipDilation_zero` / `_one` — the operation elements
      `E₀ = P₀`, `E₁ = P₁`;
    - `Concrete.dephasingOperation_eq_operatorSum` — **the answer (eq. 8.7):**
      `E(ρ) = P₀ ρ P₀ + P₁ ρ P₁`;
    - `Concrete.sum_adjoint_krausOp_controlledFlipDilation` — **the completeness relation
      (eq. 8.14):** `Σₖ Eₖ† Eₖ = P₀ + P₁ = I`.

## Design notes

* **Abstract qubit, chosen basis.** Everything is stated over an
  *arbitrary* two-dimensional complex inner product space `H` with a chosen computational
  `OrthonormalBasis (Fin 2) ℂ H`, so the result holds for *every* qubit rather than a fixed model
  of `ℂ²`, while the proofs are driven purely by orthonormality of `b`. The operators are defined
  relative to `b`; no dimension is specialised and no simplifying hypothesis is added to the
  channel.
* **Reuse over reinvention.** The reduction to the two projectors is a direct application of the
  Exercise 8.3 operator-sum infrastructure — the dilation `V` is packaged as a single
  `LinearMap H →ₗ H ⊗ H`, and the only genuine work is `krausOp b V 0 = P₀`, `krausOp b V 1 = P₁`.
  The qubit operators are coercions of Mathlib's `InnerProductSpace.rankOne`, not bespoke
  definitions. This is why the formalisation is compact.
* **`E` defined as the environment model; completeness proved directly.** `dephasingOperation` is
  literally `ρ ↦ tr_env(V ρ V†)` (prepare env in `|0⟩`, apply `U`, discard env), and completeness
  `Σₖ Eₖ† Eₖ = I` is obtained directly from `P₀ + P₁ = I` rather than routed through `V` being an
  isometry — cheaper and equally faithful. `U`'s unitarity is nonetheless recorded as a standalone
  certificate.
-/
