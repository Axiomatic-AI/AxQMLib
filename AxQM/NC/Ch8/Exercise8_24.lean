/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SpontaneousEmissionAmplitudeDamping

/-!
# Nielsen & Chuang, Exercise 8.24 (Spontaneous emission is amplitude damping)

*(N&C p. 381–382.)*

Show spontaneous emission (Jaynes-Cummings, δ=0) traced over field gives amplitude damping.

## The formalisation

Model the atom (the principal *system*) and the single field mode (the *environment*) as two
abstract qubits, `H ⊗[ℂ] H` with the atom on the left and the field on the right, each with a chosen
computational `OrthonormalBasis (Fin 2) ℂ H` (`|ij⟩ = |i⟩_atom ⊗ |j⟩_field`). The resonant
Jaynes–Cummings interaction `H_I = g(a†σ₋ + aσ₊)` (N&C eq. 7.71 at `δ = 0`) generates the
vacuum-Rabi unitary `U` of eq. (7.77):

`U = |00⟩⟨00| + |11⟩⟨11| + cos(gt)(|01⟩⟨01| + |10⟩⟨10|) - i sin(gt)(|01⟩⟨10| + |10⟩⟨01|)`

(`Concrete.jaynesCummingsZeroDetuningUnitary`). Prepare the field in the vacuum `|0⟩`, apply `U`,
and trace over the field: this gives the quantum operation `E(ρ) = tr_field(U (ρ ⊗ |0⟩⟨0|) U†)`
(`Concrete.spontaneousEmissionChannel`).

Reading off the operation elements `Eₖ = ⟨k_field|U|0_field⟩` (N&C eqs. 8.9–8.10) gives, from
`U|00⟩ = |00⟩` and `U|10⟩ = cos(gt)|10⟩ - i sin(gt)|01⟩`,

`E₀ = |0⟩⟨0| + cos(gt)|1⟩⟨1| = diag(1, cos gt)`,   `E₁ = -i sin(gt)|0⟩⟨1|`,

**exactly the amplitude-damping operation elements** of N&C eq. 8.108 with `γ = sin²(gt)`: `E₀` is
`ampDampKrausZero` once `√(1 - sin²(gt)) = cos(gt)` (needing `cos(gt) ≥ 0`, N&C's implicit regime),
and `E₁` is `ampDampKrausOne = √γ σ₋` up to the global phase `-i`, which is physically irrelevant —
it washes out of the channel, since `(c σ₋) ρ (c σ₋)† = |c|² σ₋ ρ σ₋†`. So the reduced dynamics
equals the amplitude-damping channel `E_AD` at `γ = sin²(gt)` — **the answer the exercise asks
for:**

`tr_field(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`,   `γ = sin²(gt)`, for `0 ≤ cos(gt)`.

The statement is `AxQM.Concrete.spontaneousEmissionChannel_eq_ampDampChannel`.
The traced map is trace preserving unconditionally
(`Concrete.sum_adjoint_krausOp_spontaneousEmissionDilation`, `∑ₖ Eₖ† Eₖ = I`), as it must be, being
the partial trace of a genuine unitary conjugation (`U` is unitary,
`Concrete.jaynesCummingsZeroDetuningUnitary_isometry`).

## Supporting results

The formal content of Exercise 8.24 — the Jaynes–Cummings unitary `U`, its operation elements
`Eₖ = ⟨k|U|0⟩`, and the operator-sum reduced dynamics `tr_field(U (ρ ⊗ |0⟩⟨0|) U†)` — is a
computation on `LinearMap`s of the qubits' Hilbert spaces and the abstract partial trace. Compare
the circuit model of Exercise 8.20 (`AxQM/Concrete/AmplitudeDampingCircuit.lean`) and the
operator-sum Exercises 8.4 and 8.5.

The formalisation uses the following files.

* `ToMathlib/Analysis/InnerProductSpace/OperatorSum.lean` (Exercise 8.3) — the operator-sum
  machinery used here: `LinearMap.krausOp b V k` (the operation
  elements of a dilation `V`), `LinearMap.partialTraceRight_conj_eq_sum_krausOp`
  (`tr_field(V ρ V†) = Σₖ Eₖ ρ Eₖ†`), and `LinearMap.embedRight` / `restrictRight`.
* `AxQM/Concrete/QubitBasisOperators.lean` — the abstract-qubit operators used here: the
  matrix units `Concrete.qubitUnit`, projectors `Concrete.qubitProj`, and lowering operator
  `Concrete.qubitLower`, with their algebra.
* `AxQM/Concrete/AmplitudeDampingChannel.lean` (Exercise 8.20) — the amplitude-damping channel
  the process is shown to realize: the operation elements `Concrete.ampDampKrausZero`,
  `Concrete.ampDampKrausOne`, and the channel `Concrete.ampDampChannel`.
* `AxQM/Concrete/JaynesCummingsUnitary.lean` — the resonant Jaynes–Cummings
  (vacuum-Rabi) unitary `Concrete.jaynesCummingsZeroDetuningUnitary` (eq. 7.77 at `δ = 0`), built as
  `U = I + (cos gt - 1) Q - i sin(gt) S` from the excitation-exchange coupling `Concrete.jcCoupling`
  and projector `Concrete.jcExchangeProj`, with its computational-basis action
  (`…_apply_zero_zero`, `…_apply_one_zero`, …) and unitarity
  `Concrete.jaynesCummingsZeroDetuningUnitary_isometry` (`U† U = I`). The file also records its
  action on a general product state with the field in the vacuum,
  `Concrete.jaynesCummingsZeroDetuningUnitary_apply_tmul_zero` (`U(x ⊗ |0⟩)`, the tensor computation
  the operation elements are read off from).
* `AxQM/Concrete/SpontaneousEmissionAmplitudeDamping.lean`:
    - `Concrete.spontaneousEmissionDilation` — the dilation `V = U(· ⊗ |0⟩_field)`;
    - `Concrete.krausOp_spontaneousEmissionDilation_zero_eq`/`_one_eq` — the operation elements
      `E₀ = diag(1, cos gt)`, `E₁ = -i sin(gt)|0⟩⟨1|` (both unconditional), and
      `krausOp_spontaneousEmissionDilation_zero_eq_ampDampKrausZero` identifying
      `E₀ = ampDampKrausZero b (sin²(gt))` for `0 ≤ cos(gt)`;
    - `Concrete.smul_comp_conj` — the phase-washout algebra `(c L) ρ (c L)† = |c|² L ρ L†` (for an
      arbitrary operator `L`, instantiated at `L = σ₋`);
    - `Concrete.spontaneousEmissionChannel` — the reduced dynamics `E(ρ) = tr_field(V ρ V†)`, with
      **the answer** `Concrete.spontaneousEmissionChannel_eq_ampDampChannel`:
      `E(ρ) = E_AD(ρ)` at `γ = sin²(gt)` (for `0 ≤ cos(gt)`);
    - `Concrete.sum_adjoint_krausOp_spontaneousEmissionDilation` — the completeness relation
      `Σₖ Eₖ† Eₖ = I` (unconditional), certifying `E` is trace preserving (a genuine quantum
      operation).

## Design notes

* **Abstract qubits, chosen basis.** Everything is stated over an
  *arbitrary* two-dimensional complex inner product space `H` with a chosen computational
  `OrthonormalBasis (Fin 2) ℂ H`, so the model holds for *every* qubit rather than a fixed `ℂ²`; no
  dimension is specialised and no simplifying hypothesis is added.
* **`0 ≤ cos(gt)` is N&C's implicit regime, not a weakening.** The operation elements are exact for
  all `gt`; only the *identification* of `E₀` with `ampDampKrausZero` needs
  `√(1 - sin²(gt)) = cos(gt)`, i.e. `cos(gt) ≥ 0`. This is precisely N&C's amplitude-damping regime
  (§8.3.5 writes `√(1-γ) = cos θ` with `cos θ ≥ 0`); `γ = sin²(gt) ∈ [0,1]` sweeps the full physical
  damping range as `gt` runs over `[0, π/2]`.
* **The `-i` phase is kept honest, not absorbed.** Tracing the field yields `E₁ = -i sin(gt)|0⟩⟨1|`;
  the honest operation element carries the physical phase `-i`, which the formalisation records
  rather than silently dropping to match N&C's `√γ σ₋`. The identification is made at the *channel*
  level (`spontaneousEmissionChannel_eq_ampDampChannel`), where the phase provably washes out
  (`smul_comp_conj`), so both fidelity and the amplitude-damping conclusion are preserved.
* **Reuse over reinvention.** The Jaynes–Cummings unitary is built separately; the reduction to the
  two operation elements is a direct application of the Exercise 8.3 operator-sum infrastructure,
  and the target channel is the Exercise 8.20 `ampDampChannel`; the only genuine new work is the
  single tensor computation `U(x ⊗ |0⟩)` and the phase-washout algebra.

See the module docstring of `AxQM/Concrete/SpontaneousEmissionAmplitudeDamping.lean` for the full
argument.
-/
