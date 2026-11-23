/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotter
import AxQM.Postulates.API.Evolution
import AxQM.Concrete.PauliStringBasisChange

/-!
# AxQM.Postulates.API — simulating `X₁ ⊗ Y₂ ⊗ Z₃` by a single-qubit basis change

The matrix-level construction for **Nielsen & Chuang, Exercise 4.51** (§4.7.3, p. 210): construct a
circuit implementing the propagator `e^{-iΔt H}` of the three-qubit Hamiltonian
`H = X₁ ⊗ Y₂ ⊗ Z₃`. N&C's construction turns each non-`Z` factor into a `Z` by a single-qubit gate,
leaving the all-`Z` string `Z₁ ⊗ Z₂ ⊗ Z₃`, whose propagator is the compute-parity / phase /
uncompute circuit of Figure 4.19. Concretely `H = B (Z⊗Z⊗Z) Bᴴ` with `B = H ⊗ (SH) ⊗ I`, so

`e^{-iΔt H} = B · e^{-iΔt (Z⊗Z⊗Z)} · B†`,

the all-`Z` propagator conjugated by the basis change.

This file promotes the matrix-level core of `Concrete/PauliStringBasisChange.lean` to
evolutions and observables. It provides:

* `xyzBasisChangeGate` — the basis change `B = H ⊗ (SH) ⊗ I` as a unitary `Evolution (qudit (2³))`
  (the "single-qubit gate layer" of the circuit), with its operator `xyzBasisChangeGate_op`.
* `exp_smul_toEuclideanCLM_pauliStringStd_xyz_eq_conj` — the **operator-level** exponential
  conjugation `exp(z · (X⊗Y⊗Z)ᵒᵖ) = B (exp(z · (Z⊗Z⊗Z)ᵒᵖ)) B†` for every scalar `z`, obtained by
  carrying the matrix conjugation `Concrete.kronFamilyStd_basisChangeFamily_conj_pauliStringStd`
  across the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` and applying
  `NormedSpace.exp_units_conj` in the operator algebra.
* `pauliStringHamiltonian_propagator_xyz_op_eq_conj` — the same identity read on the **propagators**
  of the Pauli-string Hamiltonians `pauliStringHamiltonian ![1,2,3] 1` (`= X⊗Y⊗Z`) and
  `pauliStringHamiltonian ![3,3,3] 1` (`= Z⊗Z⊗Z`):
  `(H.propagator ℏ t₁ t₂).op = B.op · (H_Z.propagator ℏ t₁ t₂).op · B.adjoint.op`.

The `Evolution`-level statement `pauliStringHamiltonian_xyz_propagator_eq_conj` of Exercise 4.51
is proved from the last of these in `AxQM/NC/Ch4/Exercise4_51.lean`.

## Design notes

* **Why the operator-level route (`exp_units_conj`), not `map_exp`.** The natural plan is to
  transport the matrix identity `Concrete.pauliString_exp_smul_conj_kronFamily` (which already
  contains the `exp`) through `Matrix.toEuclideanCLM` with `map_exp`. That is blocked: `map_exp`
  requires unifying the `RingHomClass`/`NormedRing` structure on `Matrix (Fin (2³)) (Fin (2³)) ℂ`,
  whose L²-operator-norm `NormedRing` instance (from `CStarAlgebra.Matrix`) makes `whnf` diverge.
  Instead this file carries only the *non-exponential* conjugation
  `Concrete.kronFamilyStd_basisChangeFamily_conj_pauliStringStd` across `toEuclideanCLM` (pure
  `map_mul` / `map_star`, no norm reasoning), reaching `Hᵒᵖ = B (Z⊗Z⊗Z)ᵒᵖ Bᴴ` at the operator
  level, and then applies the operator-algebra lemma `NormedSpace.exp_units_conj` (with `B.op` a
  unit via its unitarity). The `exp` never leaves the single operator algebra
  `EuclideanSpace ℂ (Fin (2³)) →L[ℂ] EuclideanSpace ℂ (Fin (2³))`.
* **The rational-algebra and scalar-tower instances.** `NormedSpace.exp_units_conj` lives in the
  `ℚ`-algebra section of Mathlib's exponential API, and the scalar reshaping needs
  `IsScalarTower ℂ · ·` for the `ContinuousLinearMap` scalar action; neither is a default instance
  on the operator algebra. They are supplied locally — `NormedAlgebra ℚ` by
  `NormedAlgebra.restrictScalars ℚ ℝ` (as in Mathlib's own `LieTrotter`), the scalar tower from
  `ContinuousLinearMap.smul_comp` — inside the proof, so they do not leak into any statement.
-/

open Matrix NormedSpace AxQM.Concrete

noncomputable section

namespace AxQM

/-- The **basis-change gate** `B = H ⊗ (SH) ⊗ I` of Exercise 4.51, as a unitary
`Evolution (qudit (2³))` on the three-qubit register: the layer of single-qubit gates that turns
`Z ⊗ Z ⊗ Z` into `X ⊗ Y ⊗ Z` under conjugation (Hadamard on qubit `0`, `SH` on qubit `1`, identity
on qubit `2`). Its operator is the concrete unitary matrix
`Concrete.kronFamilyStd basisChangeFamily`
promoted through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; unitarity — the `Evolution`
proof obligation — is transported from the matrix unitarity
`Concrete.kronFamilyStd_basisChangeFamily_mul_conjTranspose` by `Unitary.map_mem`. -/
def xyzBasisChangeGate : Evolution (qudit (2 ^ 3)) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)) (kronFamilyStd basisChangeFamily)
  unitary := Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)))
    (Matrix.mem_unitaryGroup_iff.mpr kronFamilyStd_basisChangeFamily_mul_conjTranspose)

/-- The underlying operator of `xyzBasisChangeGate` is the `Matrix.toEuclideanCLM` image of the
concrete basis-change matrix `Concrete.kronFamilyStd basisChangeFamily`. A `simp` lemma exposing the
matrix for the propagator conjugation below. -/
@[simp]
theorem xyzBasisChangeGate_op :
    xyzBasisChangeGate.op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)) (kronFamilyStd basisChangeFamily) := rfl

/-- **Operator-level exponential conjugation for `X ⊗ Y ⊗ Z`.** For every scalar `z`,

`exp(z · toEuclideanCLM(X⊗Y⊗Z)) = B · exp(z · toEuclideanCLM(Z⊗Z⊗Z)) · B†`,

where `B = toEuclideanCLM(kronFamilyStd basisChangeFamily)`. This is Exercise 4.51's propagator
conjugation at the level of operators on `EuclideanSpace ℂ (Fin (2³))`: specialising `z = -iΔt/ℏ`
gives the propagator `e^{-iΔt X⊗Y⊗Z}` as the all-`Z` propagator conjugated by the single-qubit
basis change.

The proof carries the matrix conjugation
`Concrete.kronFamilyStd_basisChangeFamily_conj_pauliStringStd`
(`B (Z⊗Z⊗Z) Bᴴ = X⊗Y⊗Z`) across the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (`map_mul`,
`map_star`) — reaching an operator conjugation with no `exp` — and then applies
`NormedSpace.exp_units_conj`, with `toEuclideanCLM(kronFamilyStd basisChangeFamily)` a unit (its
unitarity is the image of the matrix unitarity). The scalar is moved onto the middle factor by
`smul_mul_assoc` / `mul_smul_comm`. See the module docstring for why this route (not `map_exp`) is
used and how the required `ℚ`-algebra and scalar-tower instances are supplied. -/
theorem exp_smul_toEuclideanCLM_pauliStringStd_xyz_eq_conj (z : ℂ) :
    exp (z • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)) (pauliStringStd ![1, 2, 3]))
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)) (kronFamilyStd basisChangeFamily)
        * exp (z • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3)) (pauliStringStd ![3, 3, 3]))
        * star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3))
            (kronFamilyStd basisChangeFamily)) := by
  set Φ := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ 3))
  let E := EuclideanSpace ℂ (Fin (2 ^ 3)) →L[ℂ] EuclideanSpace ℂ (Fin (2 ^ 3))
  have : CompleteSpace (EuclideanSpace ℂ (Fin (2 ^ 3))) := FiniteDimensional.completeSpace ℂ _
  -- `exp_units_conj` lives in the `ℚ`-algebra section; provide `NormedAlgebra ℚ` by restriction.
  have : NormedAlgebra ℝ E := NormedAlgebra.restrictScalars ℝ ℂ _
  have : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ _
  -- The `ContinuousLinearMap` scalar action is a scalar tower over its own composition.
  have : IsScalarTower ℂ E E :=
    ⟨fun x f g => by
      change (x • f) * g = x • (f * g)
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.smul_comp]⟩
  -- `B.op` is unitary: transport the matrix unitarity across `Φ` (`map_mul` / `map_star`).
  have hBBs : Φ (kronFamilyStd basisChangeFamily)
      * star (Φ (kronFamilyStd basisChangeFamily)) = 1 := by
    rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose,
      kronFamilyStd_basisChangeFamily_mul_conjTranspose, map_one]
  have hsBB : star (Φ (kronFamilyStd basisChangeFamily))
      * Φ (kronFamilyStd basisChangeFamily) = 1 := by
    rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose,
      kronFamilyStd_basisChangeFamily_conjTranspose_mul, map_one]
  -- The conjugation `X⊗Y⊗Z = B (Z⊗Z⊗Z) Bᴴ`, transported to operators (no `exp` involved).
  have hconj : Φ (pauliStringStd ![1, 2, 3])
      = Φ (kronFamilyStd basisChangeFamily) * Φ (pauliStringStd ![3, 3, 3])
        * star (Φ (kronFamilyStd basisChangeFamily)) := by
    rw [← map_star, Matrix.star_eq_conjTranspose, ← map_mul, ← map_mul,
      kronFamilyStd_basisChangeFamily_conj_pauliStringStd]
  -- Package `B.op` as a unit and conjugate the exponential.
  let y : Eˣ := ⟨Φ (kronFamilyStd basisChangeFamily), star (Φ (kronFamilyStd basisChangeFamily)),
    hBBs, hsBB⟩
  have hy : (↑y : E) = Φ (kronFamilyStd basisChangeFamily) := rfl
  have hyinv : (↑y⁻¹ : E) = star (Φ (kronFamilyStd basisChangeFamily)) := rfl
  rw [hconj, ← smul_mul_assoc, ← mul_smul_comm, ← hy, ← hyinv, NormedSpace.exp_units_conj,
    hy, hyinv]

/-- **Exercise 4.51, propagator form (operator level).** The propagator of `X ⊗ Y ⊗ Z` is the
propagator of `Z ⊗ Z ⊗ Z` conjugated by the single-qubit basis-change gate `B`, at the level of
operators:

`((pauliStringHamiltonian ![1,2,3] 1).propagator ℏ t₁ t₂).op`
`  = B.op · ((pauliStringHamiltonian ![3,3,3] 1).propagator ℏ t₁ t₂).op · B.adjoint.op`,

for all `ℏ, t₁, t₂`. Here `pauliStringHamiltonian ![1,2,3] 1` is the Hamiltonian `X⊗Y⊗Z` and
`pauliStringHamiltonian ![3,3,3] 1` is `Z⊗Z⊗Z`. Reading
`(H.propagator ℏ t₁ t₂).op = exp(-iH(t₂-t₁)/ℏ)` (`Observable.propagator_op`) and
`(pauliStringHamiltonian g 1).op = toEuclideanCLM(g)` (`pauliStringHamiltonian_op`, with the
coefficient `1`), this is exactly `exp_smul_toEuclideanCLM_pauliStringStd_xyz_eq_conj` at
`z = -i(t₂-t₁)/ℏ`, with `B.adjoint.op = B.op† = star B.op`. -/
theorem pauliStringHamiltonian_propagator_xyz_op_eq_conj (ℏ t₁ t₂ : ℝ) :
    ((pauliStringHamiltonian ![1, 2, 3] 1).propagator ℏ t₁ t₂).op
      = xyzBasisChangeGate.op * ((pauliStringHamiltonian ![3, 3, 3] 1).propagator ℏ t₁ t₂).op
        * xyzBasisChangeGate.adjoint.op := by
  -- `qudit (2 ^ 3) := QSystem.ofModel (EuclideanSpace ℂ (Fin (2 ^ 3)))`, so `(qudit _).space`
  -- reduces to the bare `EuclideanSpace` by `rfl`, but `xyzBasisChangeGate_op`'s `toEuclideanCLM`
  -- carries the bare instances directly — `erw` (not `rw`) bridges that diamond.
  rw [Observable.propagator_op, Observable.propagator_op, Evolution.adjoint_op]
  rw [pauliStringHamiltonian_op, pauliStringHamiltonian_op]
  erw [xyzBasisChangeGate_op]
  simp only [Complex.ofReal_one, one_smul]
  have h := exp_smul_toEuclideanCLM_pauliStringStd_xyz_eq_conj (-Complex.I * ↑(t₂ - t₁) / ↑ℏ)
  rw [ContinuousLinearMap.star_eq_adjoint] at h
  exact h

end AxQM
