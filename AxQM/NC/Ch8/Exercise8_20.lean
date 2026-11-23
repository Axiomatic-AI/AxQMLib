/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingCircuit

/-!
# Nielsen & Chuang, Exercise 8.20 (Circuit model for amplitude damping)

*(N&C p. 380–381.)*

Show the Figure 8.13 circuit models amplitude damping with sin²(θ/2)=γ.

## The formalisation

Figure 8.13 couples the principal qubit (the *system*) to an *environment* qubit prepared in `|0⟩`
through two gates: a **controlled `R_y(θ)`** (`U₁ = P₀ ⊗ I + P₁ ⊗ R_y(θ)`, the system controlling a
`y`-rotation of the environment) followed by a **CNOT** (`U₂ = I ⊗ P₀ + X ⊗ P₁`, the environment
controlling a bit-flip of the system). The circuit unitary is `U = U₂ U₁`
(`Concrete.ampDampCircuit`), and preparing the environment in `|0⟩`, applying `U`, and tracing the
environment out gives the quantum operation `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`.

Reading off the operation elements `Eₖ = ⟨k|U|0⟩` (N&C eqs. 8.9–8.10) gives, for `0 ≤ θ ≤ π`,

`E₀ = |0⟩⟨0| + cos(θ/2)|1⟩⟨1| = diag(1, √(1-γ))`,   `E₁ = sin(θ/2)|0⟩⟨1| = √γ σ₋`,

**exactly the amplitude-damping operation elements** of N&C eq. 8.108 with `γ = sin²(θ/2)` (using
`√(1 - sin²(θ/2)) = cos(θ/2)` and `√(sin²(θ/2)) = sin(θ/2)`, valid precisely on `[0, π]`, N&C's
physical range where `γ ∈ [0,1]`). So the circuit's reduced dynamics equals the amplitude-damping
channel `E_AD` at `γ = sin²(θ/2)` — **the answer the exercise asks for:**

`tr_env(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`,   `γ = sin²(θ/2)`.

The statement is `AxQM.Concrete.ampDampCircuit_reduced_eq_ampDampChannel`. The
circuit is a genuine *unitary* dilation: each named gate is unitary, hence so is `U`
(`Concrete.adjoint_ampDampCircuit_comp_self`).

## Supporting results

The formal content of Exercise 8.20 — the circuit unitary `U`, its operation elements
`Eₖ = ⟨k|U|0⟩`, and the operator-sum reduced dynamics `tr_env(U (ρ ⊗ |0⟩⟨0|) U†)` — is a
computation on `LinearMap`s of the qubits' Hilbert spaces and the abstract partial trace. Compare
the operator-sum exercises 8.4 (`AxQM/Concrete/ControlledFlipOperatorSum.lean`) and 8.5
(`AxQM/Concrete/SpinFlipOperatorSum.lean`), and the amplitude-damping channel itself
(`AxQM/Concrete/AmplitudeDampingChannel.lean`).

The formalisation uses the following files.

* `ToMathlib/Analysis/InnerProductSpace/OperatorSum.lean` (Exercise 8.3) — the operator-sum
  machinery used here: `LinearMap.krausOp b V k` (the operation
  elements of a dilation `V`), `LinearMap.partialTraceRight_conj_eq_sum_krausOp`
  (`tr_env(V ρ V†) = Σₖ Eₖ ρ Eₖ†`), and `LinearMap.embedRight` / `restrictRight`.
* `AxQM/Concrete/QubitBasisOperators.lean` — the abstract-qubit operators used here: the
  projectors `Concrete.qubitProj`, the bit-flip `Concrete.qubitFlip`, and the lowering operator
  `Concrete.qubitLower`, with their algebra.
* `AxQM/Concrete/AmplitudeDampingChannel.lean` — the amplitude-damping channel
  the circuit is shown to realize: the operation elements `Concrete.ampDampKrausZero`,
  `Concrete.ampDampKrausOne`, the channel `Concrete.ampDampChannel`, and completeness
  `Concrete.ampDampKraus_completeness`.
* `AxQM/Concrete/AmplitudeDampingCircuit.lean`:
    - `Concrete.qubitRotY` — the single-qubit `y`-rotation `R_y(θ) = cos(θ/2) I + sin(θ/2) G`
      (generator `Concrete.qubitRotYGen = |1⟩⟨0| - |0⟩⟨1|`), with `qubitRotY_apply_zero` and its
      unitarity `adjoint_qubitRotY_comp_self`;
    - `Concrete.ampDampCRy`, `Concrete.ampDampCNOT` — the Figure 8.13 gates (controlled-`R_y` and
      CNOT), each shown unitary (`adjoint_ampDampCRy_comp_self`, `adjoint_ampDampCNOT_comp_self`);
    - `Concrete.ampDampCircuit` — the circuit unitary `U = CNOT ∘ CRy`, shown unitary
      (`adjoint_ampDampCircuit_comp_self`);
    - `Concrete.ampDampCircuitDilation` — the dilation `V = U(· ⊗ |0⟩)`, with its operation
      elements `krausOp_ampDampCircuitDilation_zero`/`_one` computed to be the amplitude-damping
      `E₀`, `E₁` at `γ = sin²(θ/2)`;
    - `Concrete.ampDampCircuitChannel` — the reduced dynamics `E(ρ) = tr_env(V ρ V†)`, with
      **the answer** `Concrete.ampDampCircuit_reduced_eq_ampDampChannel`:
      `E(ρ) = E_AD(ρ)` at `γ = sin²(θ/2)` (for `0 ≤ θ ≤ π`);
    - `Concrete.sum_adjoint_krausOp_ampDampCircuitDilation` — the completeness relation
      `Σₖ Eₖ† Eₖ = I`, certifying `E` is trace preserving (a genuine quantum operation).
## Design notes
## Design notes

* **Abstract qubit, chosen basis.** Everything is stated over an
  *arbitrary* two-dimensional complex inner product space `H` with a chosen computational
  `OrthonormalBasis (Fin 2) ℂ H`, so the model holds for *every* qubit rather than a fixed `ℂ²`; no
  dimension is specialised and no simplifying hypothesis is added.
* **`0 ≤ θ ≤ π` is N&C's physical range, not a weakening.** The identification of the operation
  elements with amplitude damping needs `√(1 - sin²(θ/2)) = cos(θ/2)` and `√(sin²(θ/2)) = sin(θ/2)`,
  which hold exactly for `θ ∈ [0, π]` — precisely the range over which `γ = sin²(θ/2)` sweeps the
  physical damping probabilities `[0, 1]`. The raw operation-element computation itself is exact for
  all `θ`.
* **Genuine unitary dilation.** The circuit is exhibited as a composition of two *named, unitary*
  gates (controlled-`R_y` and CNOT), each proved unitary, so `U` is a bona-fide two-qubit unitary —
  the essence of a "circuit model" — rather than an ad-hoc operator engineered to give the right
  Kraus operators.
* **Reuse over reinvention.** The reduction to the two operation elements is a direct application of
  the Exercise 8.3 operator-sum infrastructure, and the target channel is the existing
  `ampDampChannel`; the only genuine new work is the `y`-rotation gate and the circuit's action on
  the `env = |0⟩` column.

See the module docstring of `AxQM/Concrete/AmplitudeDampingCircuit.lean` for the full argument.
-/
