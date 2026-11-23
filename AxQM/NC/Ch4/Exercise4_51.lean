/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliStringSimulation

/-!
# Nielsen & Chuang, Exercise 4.51 — simulating `H = X₁ ⊗ Y₂ ⊗ Z₃`

Construct a circuit to simulate H=X1 (x) Y2 (x) Z3, giving e^{-i dt H}.

## The construction (N&C §4.7.3, p. 210)

For the all-`Z` string `Z₁ ⊗ Z₂ ⊗ Z₃` the propagator `e^{-iΔt Z⊗Z⊗Z}` is the compute-parity /
conditional-phase / uncompute circuit of Figure 4.19. A general Pauli string is brought to this form
by single-qubit gates: an `X` factor is `H Z H` (Hadamard conjugation) and a `Y` factor is
`(SH) Z (SH)†`. So with the single-qubit **basis change** `B = H ⊗ (SH) ⊗ I`,

`H = X ⊗ Y ⊗ Z = B (Z ⊗ Z ⊗ Z) B†`,  hence  `e^{-iΔt H} = B · e^{-iΔt (Z⊗Z⊗Z)} · B†`.

The circuit is therefore the composition `B ∘ e^{-iΔt (Z⊗Z⊗Z)} ∘ B†`: acting on a state, apply the
single-qubit layer `B†`, then the Figure 4.19 parity circuit for `Z ⊗ Z ⊗ Z`, then the layer `B`.

## What this file formalises

The result is the **`Evolution`-level** correctness of that circuit:

* `pauliStringHamiltonian_xyz_propagator_eq_conj` — the propagator (gate) `e^{-iΔt H}` of
  `H = X₁ ⊗ Y₂ ⊗ Z₃` equals the basis-change gate `B` composed with the all-`Z` propagator and then
  `B†`:
  `(pauliStringHamiltonian ![1,2,3] 1).propagator ℏ t₁ t₂`
  `  = B.comp ((pauliStringHamiltonian ![3,3,3] 1).propagator ℏ t₁ t₂ |>.comp B.adjoint)`,
  for arbitrary `ℏ, t₁, t₂` (the exercise's `e^{-iΔt H}` is `ℏ = 1`, `Δt = t₂ - t₁`). Here
  `pauliStringHamiltonian ![1,2,3] 1` is the Hamiltonian `X⊗Y⊗Z` and `pauliStringHamiltonian
  ![3,3,3] 1` is `Z⊗Z⊗Z`, both on the register `qudit (2³)`. The statement uses
  `Observable.propagator`, `Evolution.comp`/`.adjoint` and the definitions
  `pauliStringHamiltonian` / `xyzBasisChangeGate`.

## Scope of the item, and where the pieces live

N&C's Exercise 4.51 comes *after* the Figure 4.19 circuit for the all-`Z` string `Z₁ ⊗ ⋯ ⊗ Zₙ`
(eq. 4.113) has been constructed, and the surrounding text (eq. 4.114) states its own method
verbatim: "the `X` or `Y` terms can be transformed by single qubit gates to `Z` operations. This
leaves us with a Hamiltonian of the form (4.113), which is simulated as described above." The
distinctive content of the exercise is therefore precisely this **single-qubit basis-change
reduction**; the all-`Z` propagator is the given Figure-4.19 building block, here supplied as the
`Evolution` `(pauliStringHamiltonian ![3,3,3] 1).propagator ℏ t₁ t₂`. The theorem exhibits
`e^{-iΔt H}` as `[single-qubit gates] ∘ [all-Z circuit] ∘ [single-qubit gates]` — the circuit the
exercise asks for — with `B = H ⊗ (SH) ⊗ I` a genuine tensor of single-qubit gates.

The construction — the single-qubit gate layer and the propagator conjugation — is in
`AxQM/Postulates/API/PauliStringSimulation.lean`:

* `AxQM.xyzBasisChangeGate` — the basis change `B = H ⊗ (SH) ⊗ I` as a unitary
  `Evolution (qudit (2³))`;
* `AxQM.pauliStringHamiltonian_propagator_xyz_op_eq_conj` — the same conjugation on the
  underlying operators, `(H.propagator).op = B.op · (H_Z.propagator).op · B.adjoint.op`, from which
  the `Evolution` equality below follows by extensionality.

The matrix-level core (the reduction `X⊗Y⊗Z = B (Z⊗Z⊗Z) Bᴴ` and its exponential) is pure
mathematics in `AxQM/Concrete/PauliStringBasisChange.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.51.** The propagator `e^{-iΔt H}` of `H = X₁ ⊗ Y₂ ⊗ Z₃` is
implemented by the single-qubit basis-change gate `B = H ⊗ (SH) ⊗ I`, the all-`Z` propagator
`e^{-iΔt (Z⊗Z⊗Z)}` (the Figure 4.19 parity circuit), and the inverse gate `B†`:

`(pauliStringHamiltonian ![1,2,3] 1).propagator ℏ t₁ t₂`
`  = xyzBasisChangeGate.comp`
`      (((pauliStringHamiltonian ![3,3,3] 1).propagator ℏ t₁ t₂).comp xyzBasisChangeGate.adjoint)`,

for arbitrary `ℏ, t₁, t₂` (the exercise is `ℏ = 1`, `Δt = t₂ - t₁`). Here `pauliStringHamiltonian
![1,2,3] 1` is the Hamiltonian `X⊗Y⊗Z` and `pauliStringHamiltonian ![3,3,3] 1` is `Z⊗Z⊗Z`. This is
an *exact* equality of gates (not merely up to a global phase): the underlying operators agree by
`pauliStringHamiltonian_propagator_xyz_op_eq_conj`, so the `Evolution`s agree by `Evolution.ext`.
The composition unfolds to operator composition (`Evolution.comp_op`, right-associated), matched
to the conjugation of operators by `mul_assoc`. -/
theorem pauliStringHamiltonian_xyz_propagator_eq_conj (ℏ t₁ t₂ : ℝ) :
    (pauliStringHamiltonian ![1, 2, 3] 1).propagator ℏ t₁ t₂
      = xyzBasisChangeGate.comp
          (((pauliStringHamiltonian ![3, 3, 3] 1).propagator ℏ t₁ t₂).comp
            xyzBasisChangeGate.adjoint) := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.comp_op, ← ContinuousLinearMap.mul_def,
    ← ContinuousLinearMap.mul_def, pauliStringHamiltonian_propagator_xyz_op_eq_conj, mul_assoc]

end AxQM
