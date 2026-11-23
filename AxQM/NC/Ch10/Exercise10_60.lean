/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch5.Exercise5_9
import AxQM.Postulates.API.InvolutiveObservable
import AxQM.Concrete.NineQubitCode
import AxQM.Concrete.FiveQubitCode

/-!
# Nielsen & Chuang, Exercise 10.60 — syndrome-measuring circuits for the nine and five qubit codes

*(N&C §10.5.8, Figure 10.16, p. 474.)*

Construct a syndrome-measuring circuit (like Fig 10.16) for the nine and five qubit codes.

## What the exercise asks

Figure 10.16 is the syndrome-measuring circuit of the seven-qubit Steane code: for each stabilizer
generator `gᵢ` it uses one ancilla, prepared in `|0⟩`, sandwiched by Hadamards around a
*controlled-`gᵢ`*, then measured — the operator-measurement circuit of Figure 10.13 with `M = gᵢ`.
Measuring the ancilla returns the eigenvalue `βᵢ ∈ {0,1}` of `gᵢ` (the syndrome bit); on a code
state (a `+1` eigenstate of every generator) all ancillas read `0`. N&C reads the controlled gates
off the check matrix — an `X` on qubit `j` in generator `i` gives a controlled-`X` from ancilla `i`
to code qubit `j`, a `Z` a controlled-`Z` — so "constructing the circuit for a code" is exactly
*naming its generators and stacking one Figure-10.13 block per generator*. This exercise asks for
that construction for the nine-qubit Shor code (Figure 10.11 generators) and the five-qubit code
(Figure 10.12 generators).

## What is formalised

The Figure-10.13 block is already available as `measureObservableCircuit U`
(`(H ⊗ 1) · C(U) · (H ⊗ 1)`, Exercise 5.9), whose measurement semantics are proved there: on a `±1`
eigenstate of the `±1`-unitary `U`, the ancilla reads `0`/`1` deterministically. The generators of a
stabilizer code are honest (phase `+1`) Pauli strings `g : Fin n → Fin 4`, each a self-adjoint
involution `P_g` (`pauliStringHamiltonian g 1`, with `(P_g)² = I` by
`pauliStringHamiltonian_op_mul_self`), hence promotable to a controllable unitary
(`Observable.toEvolution`). Composing:

* `syndromeMeasureCircuit g` — the **one-generator syndrome block** `measureObservableCircuit (P_g)`
  for a Pauli-string generator `g` on the `n`-qubit register `qudit (2ⁿ)`. This is the general
  Figure-10.13/10.16 building block, reusable for any stabilizer code.
* `syndromeMeasureCircuit_measures` — **the block measures the generator**: if `P_g` has eigenvalue
  `(−1)ᵇ` on `ψ`, the block sends `|0⟩ ⊗ ψ` to `|b⟩ ⊗ ψ`, recording the syndrome bit `b` in the
  ancilla and leaving the register in the eigenstate. (This is Figure 10.13 working "as described",
  the content Exercise 10.58 verifies, instantiated at a Pauli-string `M`.)
* `syndromeMeasureCircuit_stabilized_zero` — on a state stabilised by `g` (`+1` eigenstate) the
  ancilla reads `0`: a codeword produces the trivial syndrome.

The two codes are then thin instantiations at their generator families
(`Concrete.shorGenIdx`, `Concrete.fiveQubitGenIdx`), giving the full eight-block (nine-qubit) and
four-block (five-qubit) syndrome circuits and their per-generator measurement guarantees:

* nine-qubit Shor code — `shorSyndromeCircuit`, `shorSyndromeCircuit_measures`,
  `shorSyndromeCircuit_stabilized_zero` (eight generators, Figure 10.11);
* five-qubit code — `fiveSyndromeCircuit`, `fiveSyndromeCircuit_measures`,
  `fiveSyndromeCircuit_stabilized_zero` (four generators, Figure 10.12).

## Design and fidelity

* **The register is `qudit (2ⁿ)`** — the standard `n`-qubit system — and the generators are the
  honest Pauli strings of Figures 10.11/10.12 (`Concrete.shorGenIdx`, `Concrete.fiveQubitGenIdx`,
  shown to pairwise commute — `Concrete.shorGenIdx_commute` / `Concrete.fiveQubitGen_commute` — so
  all blocks measure jointly). No content is weakened: the circuit measures exactly the code's
  generators.
* **The measurement guarantee is stated for an arbitrary eigenstate `ψ`** of the generator, so the
  correctness is the genuine "the block records the eigenvalue" property (Figure 10.13), independent
  of any particular codeword — the five-qubit code's entangled codewords need not be exhibited. The
  `_stabilized_zero` corollaries specialise it to any code state (a common `+1` eigenstate),
  yielding the all-zero syndrome, without constructing one.
* **Controlled-`gᵢ` versus controlled-`X`/controlled-`Z`.** N&C compiles controlled-`gᵢ` into
  controlled-`X`/controlled-`Z` gates read off the check matrix; here `controlledUnitary (P_g)`
  keeps the multi-qubit Pauli operator whole, exactly as Figure 10.13's caption permits ("`M` an
  arbitrary Hermitian operator with eigenvalues `±1` … products of Pauli operators"). The gate-level
  compilation is the separate circuit-identity content of Exercise 10.59; here the generator's Pauli
  string `g` itself records where the `X`/`Z` gates sit.
-/

open scoped Matrix

namespace AxQM

variable {n : ℕ}

/-- **The one-generator syndrome-measuring block** (Figure 10.13, the building block of Figure
10.16) for an honest Pauli-string generator `g : Fin n → Fin 4`: the operator-measurement circuit
`measureObservableCircuit (P_g) = (H ⊗ 1) · C(P_g) · (H ⊗ 1)` on `qubit ⊗ qudit (2ⁿ)`, with the
generator `P_g = pauliStringHamiltonian g 1` promoted to a controllable unitary via its involutivity
`(P_g)² = I`. Stacking one such block, on its own ancilla, per generator of a stabilizer code gives
the code's syndrome-measuring circuit. -/
noncomputable def syndromeMeasureCircuit (g : Fin n → Fin 4) :
    Evolution (qubit.compose (qudit (2 ^ n))) :=
  measureObservableCircuit ((pauliStringHamiltonian g 1).toEvolution
    (pauliStringHamiltonian_op_mul_self g))

/-- **The syndrome block measures its generator.** If the generator `P_g` has eigenvalue `(−1)ᵇ` on
the register state `ψ` (`b : Fin 2` the syndrome bit), the block sends `|0⟩ ⊗ ψ` to `|b⟩ ⊗ ψ`: the
ancilla is measured `b`, and the register is left in the eigenstate `ψ`. This is Figure 10.13
"working as described" for `M = P_g`. -/
theorem syndromeMeasureCircuit_measures (g : Fin n → Fin 4) (ψ : PureState (qudit (2 ^ n)))
    (b : Fin 2) (hψ : (pauliStringHamiltonian g 1).HasEigenstate ((-1 : ℝ) ^ (b : ℕ)) ψ) :
    (syndromeMeasureCircuit g).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis b).tmul ψ := by
  have h := (pauliStringHamiltonian g 1).toEvolution_hasEigenstate
    (pauliStringHamiltonian_op_mul_self g) hψ
  fin_cases b
  · refine measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_one _ ?_
    simpa using h
  · refine measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_neg_one _ ?_
    simpa using h

/-- **A stabilised state gives the trivial syndrome.** If `ψ` is a `+1` eigenstate of the generator
`P_g` (i.e. `g` stabilises `ψ`, as every generator does a code state), the block leaves `|0⟩ ⊗ ψ`
unchanged — the ancilla reads syndrome bit `0`. -/
theorem syndromeMeasureCircuit_stabilized_zero (g : Fin n → Fin 4) (ψ : PureState (qudit (2 ^ n)))
    (hψ : (pauliStringHamiltonian g 1).HasEigenstate 1 ψ) :
    (syndromeMeasureCircuit g).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis 0).tmul ψ := by
  have := syndromeMeasureCircuit_measures g ψ 0 (by simpa using hψ)
  simpa using this

/-! ### The nine-qubit Shor code (Figure 10.11 generators) -/

/-- **The nine-qubit Shor code syndrome-measuring circuit**, `Fin 8 → Evolution (qubit ⊗ qudit
512)`: one block per Figure-10.11 generator (`Concrete.shorGenIdx`) — six `Z`-type bit-flip
checks and two `X`-type phase-flip checks, on eight ancillas. This is the Figure-10.16 analogue for
the Shor code. -/
noncomputable def shorSyndromeCircuit (i : Fin 8) :
    Evolution (qubit.compose (qudit (2 ^ 9))) :=
  syndromeMeasureCircuit (Concrete.shorGenIdx i)

/-- **Each Shor-code block measures its generator.** Block `i` records the eigenvalue `(−1)ᵇ` of the
`i`-th Figure-10.11 generator as its ancilla's syndrome bit `b`. -/
theorem shorSyndromeCircuit_measures (i : Fin 8) (ψ : PureState (qudit (2 ^ 9))) (b : Fin 2)
    (hψ : (pauliStringHamiltonian (Concrete.shorGenIdx i) 1).HasEigenstate ((-1 : ℝ) ^ (b : ℕ)) ψ) :
    (shorSyndromeCircuit i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis b).tmul ψ :=
  syndromeMeasureCircuit_measures _ ψ b hψ

/-- **A Shor code state gives the all-zero syndrome.** A state `ψ` stabilised by all eight
Figure-10.11 generators (a Shor codeword) leaves every block's ancilla reading `0`. -/
theorem shorSyndromeCircuit_stabilized_zero (ψ : PureState (qudit (2 ^ 9)))
    (hψ : ∀ i, (pauliStringHamiltonian (Concrete.shorGenIdx i) 1).HasEigenstate 1 ψ) (i : Fin 8) :
    (shorSyndromeCircuit i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis 0).tmul ψ :=
  syndromeMeasureCircuit_stabilized_zero _ ψ (hψ i)

/-! ### The five-qubit code (Figure 10.12 generators) -/

/-- **The five-qubit code syndrome-measuring circuit**, `Fin 4 → Evolution (qubit ⊗ qudit 32)`: one
Figure-10.13 block per Figure-10.12 generator (`Concrete.fiveQubitGenIdx`, the four cyclic
`XZZXI`-type generators), on four ancillas. This is the Figure-10.16 analogue for the five-qubit
code. -/
noncomputable def fiveSyndromeCircuit (i : Fin 4) :
    Evolution (qubit.compose (qudit (2 ^ 5))) :=
  syndromeMeasureCircuit (Concrete.fiveQubitGenIdx i)

/-- **Each five-qubit-code block measures its generator.** Block `i` records the eigenvalue `(−1)ᵇ`
of the `i`-th Figure-10.12 generator as its ancilla's syndrome bit `b`. -/
theorem fiveSyndromeCircuit_measures (i : Fin 4) (ψ : PureState (qudit (2 ^ 5))) (b : Fin 2)
    (hψ : (pauliStringHamiltonian (Concrete.fiveQubitGenIdx i) 1).HasEigenstate
      ((-1 : ℝ) ^ (b : ℕ)) ψ) :
    (fiveSyndromeCircuit i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis b).tmul ψ :=
  syndromeMeasureCircuit_measures _ ψ b hψ

/-- **A five-qubit code state gives the all-zero syndrome.** A state `ψ` stabilised by all four
Figure-10.12 generators (a five-qubit codeword) leaves every block's ancilla reading `0`. -/
theorem fiveSyndromeCircuit_stabilized_zero (ψ : PureState (qudit (2 ^ 5)))
    (hψ : ∀ i, (pauliStringHamiltonian (Concrete.fiveQubitGenIdx i) 1).HasEigenstate 1 ψ)
    (i : Fin 4) :
    (fiveSyndromeCircuit i).evolvePure ((qubitBasis 0).tmul ψ) = (qubitBasis 0).tmul ψ :=
  syndromeMeasureCircuit_stabilized_zero _ ψ (hψ i)

end AxQM
