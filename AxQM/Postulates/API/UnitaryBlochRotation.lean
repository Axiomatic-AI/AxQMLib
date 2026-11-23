/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Evolution
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.BlochRotationGate
import AxQM.Concrete.BlochUnitaryRotation
import AxQM.Concrete.SpecialOrthogonalAxisAngle
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Postulates.API — unitary gates rotate the Bloch sphere (N&C Exercise 8.13)

This file promotes the concrete `SU(2) → SO(3)` core (`Concrete.BlochUnitaryRotation`, N&C
Exercise 8.13) to `Evolution`/`State`: a single-qubit unitary gate, acting on qubit states by
conjugation `ρ ↦ U ρ U†` (`Evolution.evolve`), rotates the Bloch vector by a *proper rotation*
`R ∈ SO(3)`. This is the grounded reading of Exercise 8.13 — *unitary transformations correspond to
rotations of the Bloch sphere* — as a statement about state evolution, not a bare matrix
conjugation.

## What is formalized

* `unitaryGate hU` — for a `2 × 2` unitary `U` (`hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ`), the
  **gate** as an `Evolution qubit`, its operator the promotion `Matrix.toEuclideanCLM U` and its
  unitarity transported from `hU` through the `⋆`-algebra isomorphism (exactly the `rotAxisGate`
  pattern, but for an *arbitrary* single-qubit unitary — it ranges over the whole `SU(2)` cover).
* `unitaryGate_op` — a `simp` bridge exposing the underlying operator `Matrix.toEuclideanCLM U`.
* `unitaryGate_evolve_blochState` — **the worked identity**: evolving the Bloch state
  `blochState r = ½(I + r·σ)` by `unitaryGate hU` gives the Bloch state of the rotated vector,
  `(unitaryGate hU).evolve (blochState r) = blochState ((blochRotationOfUnitary U) r)`. The rotated
  vector stays in the Bloch ball (`Concrete.blochRotationOfUnitary_mulVec_sq_sum`: a unitary
  conjugation preserves the squared Bloch length), so the right-hand `blochState` is well defined.
* `exists_mem_specialOrthogonalGroup_unitaryGate_evolve_blochState` — **Exercise 8.13**: for any
  single-qubit unitary gate there is a proper rotation `R ∈ SO(3)` such that its state evolution
  sends `blochState r` to `blochState (R r)` — unitaries *are* rotations of the Bloch sphere.
* `exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup` — **the converse
  (surjectivity of the `SU(2) → SO(3)` cover)**: *every* proper rotation `O ∈ SO(3)` is the
  Bloch-sphere action of some qubit unitary conjugation `ρ ↦ U ρ U†`. Together with the forward
  statement this shows the single-qubit unitary conjugations realise **exactly** the proper
  rotations of the Bloch sphere. This is the ingredient of the qubit converse of **Nielsen &
  Chuang, Problem 8.3** that turns the pre/post rotations `O₁, O₂` of a unital channel's
  Bloch-matrix SVD `M = O₁ · diag d · O₂` into unitary conjugations.

## Relation to other files

The statement of Exercise 8.13 is in `AxQM/NC/Ch8/Exercise8_13.lean`; compare Exercises 8.11 and
8.12 and Theorem 8.3. The mathematics — the `SU(2) → SO(3)` homomorphism and its norm preservation —
is entirely in `AxQM/Concrete/BlochUnitaryRotation.lean`; this file only *transports* the concrete
conjugation identity `Concrete.blochMatrix_conj_unitary` across `Matrix.toEuclideanCLM` to the
operator channel, matching it to `blochState`'s operator via `State.ext` (the same route as
`AxQM/NC/Ch4/Exercise4_6.lean`; compare `rotAxisGate` / `BlochRotationGate`).

## Design notes

* **Gate over an arbitrary unitary, not an arbitrary `Evolution qubit`.** `unitaryGate` takes the
  matrix `U` with its unitarity proof. Stating the exercise over a general `E : Evolution qubit`
  (extracting `U := toEuclideanCLM.symm E.op`) is equally faithful but needs matrix-extraction
  bridging; the `unitaryGate` form already ranges over *all* single-qubit unitaries and mirrors the
  existing `rotAxisGate`, so it is the natural choice here.
* **Well-definedness certificate.** `blochState` requires the Bloch vector to lie in the closed unit
  ball. `unitaryGate_evolve_blochState` supplies that bound for the rotated vector directly from
  `Concrete.blochRotationOfUnitary_mulVec_sq_sum` (squared length preserved). In the existential
  headline the caller supplies the (always satisfiable) bound `h'` for `R r`; by proof irrelevance
  the resulting `State` does not depend on which proof is used.
-/

noncomputable section

namespace AxQM

/-- The **single-qubit unitary gate** of a `2 × 2` unitary `U` (`hU : U ∈ Matrix.unitaryGroup
(Fin 2) ℂ`), as a closed-system `Evolution` of the `qubit` (N&C Exercise 8.13). Its operator is `U`
promoted through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; the `Evolution` unitarity
obligation is transported from `hU` by `Unitary.map_mem`. This is the general single-qubit unitary,
the `SU(2)`-cover analogue of the axis-specialised `rotAxisGate`. -/
def unitaryGate {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) U
  unitary := Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) hU

@[simp]
theorem unitaryGate_op {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (unitaryGate hU).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) U :=
  rfl

/-- **Unitary evolution rotates the Bloch vector.** Evolving the Bloch state `blochState r =
½(I + r·σ)` of the qubit by the unitary gate `unitaryGate hU` yields the Bloch state of the rotated
vector `(blochRotationOfUnitary U) r`:
`(unitaryGate hU).evolve (blochState r) = blochState ((blochRotationOfUnitary U).mulVec r)`.

The rotated vector stays in the Bloch ball (`Concrete.blochRotationOfUnitary_mulVec_sq_sum`: unitary
conjugation preserves the squared Bloch length), so the right-hand `blochState` is well defined;
that bound is the second argument. The proof transports the concrete conjugation identity
`Concrete.blochMatrix_conj_unitary` (`U · blochMatrix r · U† = blochMatrix ((R U) r)`) through the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM` to the operator channel `ρ ↦ U ρ U†`
(`Evolution.evolve`), matching it to `blochState`'s operator via `State.ext` — the exact route of
the axis-rotation identity `rotAxisGate_evolve_blochState` (N&C Exercise 4.6). -/
theorem unitaryGate_evolve_blochState {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (r : Fin 3 → ℝ)
    (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    (unitaryGate hU).evolve (blochState r h)
      = blochState ((Concrete.blochRotationOfUnitary U).mulVec r)
          ((Concrete.blochRotationOfUnitary_mulVec_sq_sum hU r).trans_le h) := by
  apply State.ext
  simp only [Evolution.evolve_op, unitaryGate_op, blochState_op]
  rw [← Concrete.blochMatrix_conj_unitary hU, map_mul, map_mul, ← Matrix.star_eq_conjTranspose,
    map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  -- both sides are now the operator conjugation `U · (r·σ) · U†`; the remaining `rfl` bridges the
  -- `qubit.space ≡ EuclideanSpace ℂ (Fin 2)` defeq (unfolded only at default transparency).
  rfl

/-- **Nielsen & Chuang, Exercise 8.13 (physics headline) — unitary transformations correspond to
rotations of the Bloch sphere.** For any single-qubit unitary `U`, the state evolution
`ρ ↦ U ρ U†` (`unitaryGate hU |>.evolve`) acts on the Bloch state `blochState r = ½(I + r·σ)` as a
*proper rotation* of its Bloch vector: there is `R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ` with
`(unitaryGate hU).evolve (blochState r) = blochState (R r)` for every Bloch vector `r`. The witness
is `blochRotationOfUnitary U`, the `SU(2) → SO(3)` image of `U`.

The rotated vector `R r` is again in the Bloch ball (its squared length is preserved,
`Concrete.blochRotationOfUnitary_mulVec_sq_sum`), so `blochState (R r)` is always well defined; the
membership proof `h'` is a hypothesis the caller supplies, and by proof irrelevance the equated
`State` does not depend on it. -/
theorem exists_mem_specialOrthogonalGroup_unitaryGate_evolve_blochState
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
        (h' : (R.mulVec r) 0 ^ 2 + (R.mulVec r) 1 ^ 2 + (R.mulVec r) 2 ^ 2 ≤ 1),
        (unitaryGate hU).evolve (blochState r h) = blochState (R.mulVec r) h' :=
  ⟨Concrete.blochRotationOfUnitary U,
    Concrete.blochRotationOfUnitary_mem_specialOrthogonalGroup hU,
    fun r h _ => by rw [unitaryGate_evolve_blochState hU r h]⟩

/-- **Surjectivity of the `SU(2) → SO(3)` cover — every proper rotation is a qubit unitary
conjugation (Nielsen & Chuang, Problem 8.3, qubit converse).** For every `O ∈ SO(3)` there is a
single-qubit unitary `Evolution U` of the `qubit` whose state conjugation `ρ ↦ U ρ U†`
(`Evolution.evolve`) acts on the Bloch sphere exactly as `O`:
`U.evolve (blochState r) = blochState (O r)` for every Bloch vector `r`.

This is the **converse** of the forward headline
`exists_mem_specialOrthogonalGroup_unitaryGate_evolve_blochState` (Exercise 8.13): together they
say the single-qubit unitary conjugations realise *exactly* the proper rotations of the Bloch
sphere. In Problem 8.3's qubit direction a unital channel's Bloch matrix factors as
`M = O₁ · diag d · O₂` (`Concrete.exists_specialOrthogonalGroup_diagonal_factor`); this lemma turns
the outer rotations `O₁, O₂ ∈ SO(3)` into unitary conjugations, so the whole channel becomes a
composition of random-unitary channels.

The witness is the axis rotation gate `rotAxisGate n̂ θ`, where `O = rot3D n̂ θ` is the axis–angle
decomposition of `O` (`Concrete.exists_rot3D_eq_mulVec_of_mem_specialOrthogonalGroup`, Euler's
theorem). Its Bloch action `(rotAxisGate n̂ θ).evolve (blochState r) = blochState (rot3D n̂ θ r)` is
the Exercise 4.6 identity `rotAxisGate_evolve_blochState` (reused from
`BlochRotationGate`); since `O r = rot3D n̂ θ r` the two rotated Bloch states coincide. The caller
supplies the (always satisfiable) membership proof `h'` for `O r`; by proof irrelevance the equated
`State` does not depend on it. -/
theorem exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup
    {O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ U : Evolution qubit,
      ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
        (h' : (O.mulVec r) 0 ^ 2 + (O.mulVec r) 1 ^ 2 + (O.mulVec r) 2 ^ 2 ≤ 1),
        U.evolve (blochState r h) = blochState (O.mulVec r) h' := by
  obtain ⟨n, θ, hn, hOv⟩ := Concrete.exists_rot3D_eq_mulVec_of_mem_specialOrthogonalGroup hO
  refine ⟨rotAxisGate n θ, fun r h h' => ?_⟩
  -- The axis rotation gate's Bloch action (N&C Ex 4.6), reused from `BlochRotationGate`.
  rw [rotAxisGate_evolve_blochState hn θ r h]
  -- `O r = rot3D n̂ θ r`, so the rotated Bloch states coincide (proof irrelevance on the bound).
  apply State.ext
  simp only [blochState_op, hOv r]
  rfl

/-- **A general one-qubit `unitaryGate` acts as its matrix column.** On a computational-basis state
`|z⟩` the one-qubit gate `unitaryGate hM` (`M ∈ Matrix.unitaryGroup (Fin 2) ℂ`) produces the
superposition `∑_w M w z · |w⟩`, the `z`-th column of `M`. The general form of the gate-specific
`hadamardGate_evolvePure_qubitBasis_sum` / `rotZGate_evolvePure_qubitBasis_sum`, read off the column
action `Matrix.toEuclideanCLM_apply_single` through `unitaryGate_op` and `qubitBasis_vec`. This is
the single-wire factor a tower re-expression of a single-qubit register gate matches the register
two-term superposition against (e.g. `Core/PauliDiagWireTower`). -/
theorem unitaryGate_evolvePure_qubitBasis_sum {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) (z : Fin 2) :
    ((unitaryGate hM).evolvePure (qubitBasis z)).vec = ∑ w : Fin 2, M w z • (qubitBasis w).vec := by
  rw [Evolution.evolvePure_vec, unitaryGate_op, qubitBasis_vec]
  refine (Matrix.toEuclideanCLM_apply_single M z).trans (Finset.sum_congr rfl fun w _ => ?_)
  exact congrArg (M w z • ·) (qubitBasis_vec w).symm

end AxQM
