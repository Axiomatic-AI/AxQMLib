/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_63
import AxQM.Postulates.API.SteaneCodeSpace

/-!
# Nielsen & Chuang, Exercise 10.73 — fault-tolerant construction of the Steane encoded `|0⟩`

*(N&C §10.6.3, Fig 10.30, p. 493.)*

Show the Steane code encoded |0> can be constructed fault-tolerantly (cat-state ancillas, verify,
error prob).

## What is, and is not, formalised

The exercise is a *circuit-design* recipe for **fault-tolerantly** preparing the encoded `|0⟩`.
Its parts (1), (3), (4) — the cat-state ancilla circuit, the `O(p²)` error-probability arithmetic
(with and without threefold repetition + majority voting), and the enumeration/fault-tolerance of
the conditional recovery operations — are the fault-tolerance *engineering*: they turn on an
error/cost model (a per-component failure probability `p`, majority voting, error propagation
through the circuit) that the postulate library does not, and cannot, express. In keeping with the
library's treatment of the fault-tolerance exercises (10.64, 10.67, 10.69 — which formalise the
exact algebraic mechanism an FT argument turns on rather than a cost model), this file formalises
the **verifiable mathematical kernel** the construction rests on: the *specification correctness* of
the measurement-based preparation.

N&C's construction (§10.5.1 and this exercise) prepares `|0_L⟩` by **measuring the six stabilizer
generators `g₁,…,g₆` of Figure 10.6 together with the encoded `Z̄` operator, and fixing all signs to
`+1`.** For this to prepare `|0_L⟩` — and nothing else — the state so specified must be uniquely
determined. That is exactly the two facts proved here:

* the target `|0_L⟩` **is** a common `+1`-eigenstate of all seven observables `⟨g₁,…,g₆, Z̄⟩`
  (`steaneZeroStabilizer_hasEigenstate_one_logicalZero`) — the construction's all-`+1` outcome is
  physically realised by `|0_L⟩` (*soundness*); and
* `|0_L⟩` is the **only** such state, up to a global phase (`steaneLogicalZero_eq_of_stabilized`) —
  post-selecting the `+1` outcome on every measured observable pins the prepared state to `|0_L⟩`
  (*completeness*), with **no auxiliary hypothesis**: the six generator conditions themselves force
  the register into the code space, so all seven observables are load-bearing.

Together: the seven observables `⟨g₁,…,g₆, Z̄⟩` form a full stabilizer group whose unique
`+1`-eigenstate is `|0_L⟩`, so measuring them and fixing the signs prepares exactly `|0_L⟩` — the
mathematical content of the construction, independent of the fault-tolerance overlay.

## The two stages, both proved outright

The circuit has two stages, and each is a proof step of the completeness theorem
`steaneLogicalZero_eq_of_stabilized`:

* **Stage 1 — the six generator measurements (part 1).** Measuring `g₁,…,g₆` and fixing their signs
  to `+1` projects the register onto the two-dimensional Steane **code space**
  `span{|0_L⟩, |1_L⟩}` (the stabilizer-projector fact of §10.5.1 / Proposition 10.4). This is
  `steaneStabilizer_inSteaneCode`: fixing under `g₁,…,g₆` forces `InSteaneCode ψ`. It is the CSS
  code-space identification (Exercise 10.51, `cssStabilizedSpace_eq_cssCodeSpace`) in *generator
  form* — the six generators are the X/Z Pauli strings on the rows of the Hamming parity-check
  matrix, which generate the dual code `C⊥` — followed by the index-`2` coset collapse of the
  `[7,4]` Hamming code, which identifies the CSS code space `cssCodeSpace C C⊥` with `span{|0_L⟩,
  |1_L⟩}` (`Postulates/API/SteaneCodeSpace`).
* **Stage 2 — the `Z̄` measurement (part 2).** On the code space `Z̄` acts as the logical `Z`
  (Exercise 10.52): `Z̄|0_L⟩ = +|0_L⟩`, `Z̄|1_L⟩ = −|1_L⟩`. So its `+1`-eigenspace within the
  code is exactly the `|0_L⟩` line; measuring `Z̄` and post-selecting `+1` collapses any code
  state onto `|0_L⟩`. This is `steaneLogicalZero_eq_of_stabilized_inCode`, the Stage-2 kernel.

The earlier `InSteaneCode ψ` is thus **derived, not assumed**: the completeness statement
hypothesises only that `ψ` passes the seven measurements — exactly the raw outcome of the circuit —
and every
generator condition is load-bearing (`g₁,…,g₆` produce code membership, `Z̄` selects `|0_L⟩` within
it). The Stage-2 kernel `steaneLogicalZero_eq_of_stabilized_inCode`, which still takes `InSteaneCode
ψ` as a hypothesis, is retained as a reusable lemma (uniqueness *within the code space*, which uses
only the `Z̄` component); the headline `steaneLogicalZero_eq_of_stabilized` chains Stage 1 into it.

## Ingredients

Everything is assembled from existing Steane infrastructure: the generator family `steaneStabilizer`
and its stabilization of the codewords (`steaneStabilizer_hasEigenstate_one_logicalZero`,
Exercise 10.32); the logical operator `steaneLogicalZBar` and its eigen-actions
`steaneLogicalZBar_hasEigenstate_logicalZero` / `…_logicalOne` (Exercise 10.52); the code-space
predicate `InSteaneCode` and codeword orthogonality `steaneLogical_overlap_eq_zero`
(Exercise 10.63); the CSS code-space identification (Exercise 10.51) in generator form and the
Steane index-`2` coset collapse `cssCodeSpace_steaneDualCode_le_span`
(`Postulates/API/SteaneCodeSpace`, `Concrete/SteaneCode`), which discharge Stage 1; and the
`PureState` density-operator machinery (`Postulates/API`). Only the seven-generator bundle, the
Stage-1 derivation, and the uniqueness step are new.

## Fidelity

The statements use the unitary `Evolution` family `steaneZeroStabilizer` / `steaneStabilizer`, the
eigenstate relation `Evolution.HasEigenstate`, the codeword `PureState` `steaneLogicalZero`, the
code-space predicate `InSteaneCode`, and the density operator `PureState.toState`. The Stage-1
machinery is in `AxQM/Postulates/API/SteaneCodeSpace.lean` and `AxQM/Concrete/SteaneCode.lean`.
"Up to a global phase" is the equality of density operators
`PureState.toState` (which erases the phase), as in Exercise 10.63. Nothing is weakened — indeed the
completeness statement is now *strengthened* to drop the code-membership hypothesis: the observables
are exactly the six Figure-10.6 generators and `Z̄ = Z₁…Z₇`, the target is exactly the codeword
`|0_L⟩` of eq. (10.78), and the only hypothesis is that `ψ` passes the seven measurements.
-/

noncomputable section

namespace AxQM

open AxQM.Concrete

/-- **The seven stabilizer generators of the Steane encoded `|0⟩`.** The observables measured in the
fault-tolerant preparation of `|0_L⟩` (Exercise 10.73): the six code stabilizer generators
`steaneStabilizer` of Figure 10.6 (`g₁,…,g₆`, indices `0–5`) followed by the encoded logical-`Z̄`
operator `steaneLogicalZBar` (index `6`). Together they generate the full stabilizer group
`⟨g₁,…,g₆, Z̄⟩` of the *state* `|0_L⟩` (seven independent generators on seven qubits), as opposed to
the six-generator stabilizer of the two-dimensional code. -/
def steaneZeroStabilizer : Fin 7 → Evolution (bitReg (Fin 7)) :=
  Fin.snoc steaneStabilizer steaneLogicalZBar

/-- **The encoded `|0⟩` passes every measurement of the construction.** The Steane logical zero
`|0_L⟩` is a common `+1`-eigenstate of all seven observables `steaneZeroStabilizer` — the six
Figure-10.6 generators (`steaneStabilizer_hasEigenstate_one_logicalZero`, Exercise 10.32) and the
encoded `Z̄` (`steaneLogicalZBar_hasEigenstate_logicalZero`, Exercise 10.52). Physically: `|0_L⟩`
realises the all-`+1` measurement outcome that the fault-tolerant construction post-selects — the
*soundness* half of "the construction prepares `|0_L⟩`". -/
theorem steaneZeroStabilizer_hasEigenstate_one_logicalZero (i : Fin 7) :
    (steaneZeroStabilizer i).HasEigenstate 1 steaneLogicalZero := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [steaneZeroStabilizer, Fin.snoc_last] using
      steaneLogicalZBar_hasEigenstate_logicalZero
  · simpa only [steaneZeroStabilizer, Fin.snoc_castSucc] using
      steaneStabilizer_hasEigenstate_one_logicalZero j

/-- **Stage 1: the six generator measurements project into the code space.** Any state `ψ` that is a
common `+1`-eigenstate of the six Figure-10.6 generators `g₁,…,g₆` (`steaneStabilizer`) lies in the
two-dimensional Steane code space, `InSteaneCode ψ`. This is the "measuring `g₁,…,g₆` with all
outcomes `+1` prepares a code state" step of the construction — now *proved* rather than assumed.

The mechanism is the CSS code-space identification (Exercise 10.51) in generator form: the six
generators are the X- and Z-type Pauli strings `X^{hᵢ}`, `Z^{hᵢ}` on the three rows `hᵢ` of the
Hamming parity-check matrix, which generate the dual code `C⊥`; fixing under them forces membership
in `cssCodeSpace C C⊥` (`mem_cssCodeSpace_of_hammingParityCheck_op_eq_self`), and the index-`2`
coset collapse (`cssCodeSpace_steaneDualCode_le_span`) identifies that code space with the span of
the two logical codewords `span{ |0_L⟩, |1_L⟩ }`, which is exactly `InSteaneCode`. -/
theorem steaneStabilizer_inSteaneCode {ψ : PureState (bitReg (Fin 7))}
    (hg : ∀ i : Fin 6, (steaneStabilizer i).HasEigenstate 1 ψ) : InSteaneCode ψ := by
  -- The three X-type generators fix `ψ` (extract from the `Fin.append` family, first block).
  have hX : ∀ i : Fin 3, (bitString (hammingParityCheck i)).op ψ.vec = ψ.vec :=
    fun (i : Fin 3) => by
      simpa only [steaneStabilizer, Fin.append_left, steaneGenX, Evolution.HasEigenstate, one_smul]
        using hg (Fin.castAdd 3 i)
  -- The three Z-type generators fix `ψ` (second block of the `Fin.append` family).
  have hZ : ∀ i : Fin 3, (phaseString (hammingParityCheck i)).op ψ.vec = ψ.vec :=
    fun (i : Fin 3) => by
      simpa only [steaneStabilizer, Fin.append_right, steaneGenZ, Evolution.HasEigenstate, one_smul]
        using hg (Fin.natAdd 3 i)
  -- `ψ.vec ∈ cssCodeSpace C C⊥` (Stage-1 projection) collapses onto `span{ |0_L⟩, |1_L⟩ }`.
  have hspan := cssCodeSpace_steaneDualCode_le_span
    (mem_cssCodeSpace_of_hammingParityCheck_op_eq_self hX hZ)
  rw [Submodule.mem_span_pair] at hspan
  obtain ⟨a, b, hab⟩ := hspan
  exact ⟨a, b, hab.symm⟩

/-- **The construction prepares exactly the encoded `|0⟩` (uniqueness).** Any Steane *code* state
`ψ` (produced after the six generator measurements have projected into the code, `InSteaneCode
ψ`) that is a common `+1`-eigenstate of all seven observables `steaneZeroStabilizer` — in particular
of the encoded `Z̄` — equals the logical zero `|0_L⟩` up to a global phase (`ψ.toState =
steaneLogicalZero.toState`). This is the *completeness* half of "the construction prepares `|0_L⟩`":
post-selecting the `+1` outcome on `Z̄` collapses a code state onto the `|0_L⟩` line.

Mechanism (Exercise 10.52): writing `ψ = a|0_L⟩ + b|1_L⟩` (code membership), the `+1`-eigen-equation
for `Z̄` reads `a|0_L⟩ − b|1_L⟩ = a|0_L⟩ + b|1_L⟩` (since `Z̄|0_L⟩ = |0_L⟩`, `Z̄|1_L⟩ = −|1_L⟩`),
whence `(−b − b)|1_L⟩ = 0`; as `|1_L⟩ ≠ 0` this forces `b = 0`, so `ψ = a|0_L⟩` with `‖a‖ = 1` (both
unit vectors) — a global-phase multiple of `|0_L⟩`. Only the `Z̄` (last) component of the seven
hypotheses is load-bearing; the six generator conditions hold automatically on the code space, and
the construction nonetheless measures all seven, which the statement reflects. -/
theorem steaneLogicalZero_eq_of_stabilized_inCode (ψ : PureState (bitReg (Fin 7)))
    (hcode : InSteaneCode ψ)
    (hfix : ∀ i, (steaneZeroStabilizer i).HasEigenstate 1 ψ) :
    ψ.toState = steaneLogicalZero.toState := by
  obtain ⟨a, b, hψ⟩ := hcode
  -- The encoded `Z̄` (index `6 = Fin.last 6`) fixes `ψ`: unfold the eigen-equation `Z̄ ψ = ψ`.
  have hZlast : steaneLogicalZBar.HasEigenstate 1 ψ := by
    simpa only [steaneZeroStabilizer, Fin.snoc_last] using hfix (Fin.last 6)
  have hZ : steaneLogicalZBar.op ψ.vec = ψ.vec := by
    have h : steaneLogicalZBar.op ψ.vec = (1 : ℂ) • ψ.vec := hZlast
    rwa [one_smul] at h
  -- `Z̄`'s eigen-actions on the codewords (Exercise 10.52): `+1` on `|0_L⟩`, `−1` on `|1_L⟩`.
  have hZ0 : steaneLogicalZBar.op steaneLogicalZero.vec = steaneLogicalZero.vec := by
    have h : steaneLogicalZBar.op steaneLogicalZero.vec = (1 : ℂ) • steaneLogicalZero.vec :=
      steaneLogicalZBar_hasEigenstate_logicalZero
    rwa [one_smul] at h
  have hZ1 : steaneLogicalZBar.op steaneLogicalOne.vec = -steaneLogicalOne.vec := by
    have h : steaneLogicalZBar.op steaneLogicalOne.vec = (-1 : ℂ) • steaneLogicalOne.vec :=
      steaneLogicalZBar_hasEigenstate_logicalOne
    rwa [neg_one_smul] at h
  -- Expand `Z̄ ψ = ψ` in the codeword basis; the `|1_L⟩` amplitude satisfies `(−b − b)|1_L⟩ = 0`.
  have hb : b = 0 := by
    have h := hZ
    rw [hψ, map_add, map_smul, map_smul, hZ0, hZ1, smul_neg, ← neg_smul] at h
    have h2 : (-b) • steaneLogicalOne.vec = b • steaneLogicalOne.vec := add_left_cancel h
    have h3 : (-b - b) • steaneLogicalOne.vec = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with hbb | hv
    · linear_combination (-1 / 2 : ℂ) * hbb
    · exact absurd hv steaneLogicalOne.vec_ne_zero
  -- Hence `ψ = a|0_L⟩` with `‖a‖ = 1`: a global-phase multiple of `|0_L⟩`.
  rw [hb, zero_smul, add_zero] at hψ
  have hanorm : ‖a‖ = 1 := by
    have h1 := ψ.normalized
    rwa [hψ, norm_smul, steaneLogicalZero.normalized, mul_one] at h1
  exact PureState.toState_eq_of_vec_eq_smul hanorm hψ

/-- **The construction prepares exactly the encoded `|0⟩` (uniqueness, full statement).** Any state
`ψ` that is a common `+1`-eigenstate of *all seven* observables `steaneZeroStabilizer` — the six
Figure-10.6 generators `g₁,…,g₆` **and** the encoded `Z̄` — equals the logical zero `|0_L⟩` up to a
global phase (`ψ.toState = steaneLogicalZero.toState`). This is the *completeness* half of "the
construction prepares `|0_L⟩`": post-selecting the `+1` outcome on every measured observable pins
the prepared state to `|0_L⟩`, with **no auxiliary code-membership hypothesis** — the six generator
conditions are load-bearing.

The two stages of the construction appear as the two proof steps: the six generator conditions
project `ψ` into the code (`steaneStabilizer_inSteaneCode`, Stage 1), and on the code the `Z̄`
condition singles out `|0_L⟩` (`steaneLogicalZero_eq_of_stabilized_inCode`, Stage 2). Together they
give the uniqueness for the *raw* measurement outcome, faithful to N&C's circuit: the state produced
by measuring `g₁,…,g₆, Z̄` and fixing all signs to `+1` is exactly `|0_L⟩`. -/
theorem steaneLogicalZero_eq_of_stabilized (ψ : PureState (bitReg (Fin 7)))
    (hfix : ∀ i, (steaneZeroStabilizer i).HasEigenstate 1 ψ) :
    ψ.toState = steaneLogicalZero.toState := by
  refine steaneLogicalZero_eq_of_stabilized_inCode ψ ?_ hfix
  refine steaneStabilizer_inSteaneCode (fun i => ?_)
  simpa only [steaneZeroStabilizer, Fin.snoc_castSucc] using hfix i.castSucc

end AxQM
