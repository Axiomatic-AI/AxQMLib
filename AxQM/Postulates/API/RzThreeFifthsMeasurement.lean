/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RzThreeFifthsCircuit
import AxQM.Postulates.API.ControlMeasurementCommute
import AxQM.Postulates.API.CascadedMeasurement
import AxQM.Postulates.API.KitaevPhaseEstimation

/-!
# AxQM.Postulates.API — measuring both ancillas of the Figure 4.17 `R_z(θ)` circuit

The **measurement step** of Nielsen & Chuang's Exercise 4.41, after the circuit action of
`AxQM/Postulates/API/RzThreeFifthsCircuit.lean`: the *two-ancilla measurement* as
an explicit `Measurement`, and **the probability that both ancilla outcomes are `0` is
`5/8`** — the exercise's second explicit claim, and the quantity that governs the repeat-until-
success protocol.

```
|0⟩ ─── H ───●─────────●─── H ───⊙   (measure ancilla 1 → this file)
             │         │
|0⟩ ─── H ───●─────────●─── H ───⊙   (measure ancilla 2 → this file)
             │         │
|ψ⟩ ─────────⊕─── S ───⊕──────────
```

## What is formalised

* `rzTwoAncillaMeasurement` — the projective measurement of the **two ancilla qubits** of
  `qubit ⊗ (qubit ⊗ qubit)` in the computational basis, leaving the target untouched. Built as the
  cascade of the two single-qubit control measurements
  (`controlMeasurement (qubit ⊗ qubit)` on ancilla 1, `(controlMeasurement qubit).onRight qubit` on
  ancilla 2), so its operator for outcome `(a', b')` is the projector `|a'⟩⟨a'| ⊗ |b'⟩⟨b'| ⊗ 1`.
* `rzTwoAncillaMeasurement_op_zeroZero_qubitBasis` — the success projector `|0⟩⟨0| ⊗ |0⟩⟨0| ⊗ 1`
  scales `|a,b,t⟩` by `⟨0|a⟩ ⟨0|b⟩`, keeping the `(0,0)` ancilla branch and annihilating the other
  three.
* `rzTwoAncillaMeasurement_op_rzThreeFifthsCircuit_qubitBasis` — **the success (Kraus) reading on a
  computational basis target.** On `|0,0,t⟩` the projector collapses the four-branch circuit output
  to the single success branch `rzThreeFifthsAmp 0 0 t · |0,0,t⟩`, whose amplitude has
  `‖·‖² = 5/8` (`rzThreeFifthsAmp_apply`).
* `rzTwoAncillaMeasurement_bornProb_normSq` — **the `5/8` for every target `|ψ⟩`.** The squared norm
  of the success operator on `|0,0,ψ⟩` is `5/8` for an arbitrary `|ψ⟩`: expanding `|ψ⟩` in the
  computational basis and pushing the linear circuit + measurement through the sum gives
  `M₀₀|0,0,ψ⟩ = c · |0,0, R_z(θ)ψ⟩` (with `(rotZGate θ).evolvePure ψ` again a unit `PureState`), so
  the probability is `‖c‖² = 5/8` — input-independent because `R_z(θ)` is unitary.

The statement `rzTwoAncillaMeasurement.bornProb (…).toState (0,0) = 5/8` for
arbitrary `|ψ⟩`, over `Measurement.bornProb`, is a direct consequence of
`rzTwoAncillaMeasurement_bornProb_normSq`; it is `rzThreeFifthsCircuit_bothZero_bornProb` in
`AxQM/NC/Ch4/Exercise4_41.lean`. Compare Exercise 4.34 and
`AxQM/Postulates/API/MeasureObservableAncilla.lean`.
-/

open scoped TensorProduct InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The two-ancilla measurement of the Figure 4.17 circuit.** Measuring both control (ancilla)
qubits of `qubit ⊗ (qubit ⊗ qubit)` in the computational basis, leaving the target untouched: the
cascade of `controlMeasurement (qubit ⊗ qubit)` (ancilla 1, the left factor) and
`(controlMeasurement qubit).onRight qubit` (ancilla 2, the left qubit of the right factor). Its
operator for outcome `(a', b')` is the two-ancilla projector `|a'⟩⟨a'| ⊗ (|b'⟩⟨b'| ⊗ 1)`. -/
def rzTwoAncillaMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ (qubit ⊗ qubit)) :=
  (controlMeasurement (qubit ⊗ qubit)).cascade ((controlMeasurement qubit).onRight qubit)

/-- Collect two left-factor scalars in a nested tensor: `(c • x) ⊗ (d • y) ⊗ z = (c d) • x ⊗ y ⊗ z`.
Proved on abstract modules so it applies through the `QSystem.compose` space wrappers by defeq. -/
private theorem smul_tmul_smul_tmul_collect {R M N P : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (x : M) (y : N) (z : P) (c d : R) :
    (c • x) ⊗ₜ[R] ((d • y) ⊗ₜ[R] z) = (c * d) • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]

/-- Pull a scalar into the innermost factor of a nested tensor: `s • x ⊗ y ⊗ z = x ⊗ y ⊗ (s • z)`.
Abstract so it applies through the `QSystem.compose` space wrappers by defeq. -/
private theorem smul_tmul_tmul_inner {R M N P : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (x : M) (y : N) (z : P) (s : R) :
    s • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = x ⊗ₜ[R] (y ⊗ₜ[R] (s • z)) := by
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]

/-- Distribute a nested tensor over a `Finset`-sum of scaled vectors in the innermost factor.
Abstract so it applies through the `QSystem.compose` space wrappers by defeq. -/
private theorem tmul_tmul_sum_smul {ι : Type*} [Fintype ι] {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (x : M) (y : N) (g : ι → R) (v : ι → P) :
    x ⊗ₜ[R] (y ⊗ₜ[R] (∑ i, g i • v i)) = ∑ i, g i • (x ⊗ₜ[R] (y ⊗ₜ[R] v i)) := by
  rw [TensorProduct.tmul_sum, TensorProduct.tmul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]

/-- **The success projector on a computational basis vector.** `M₍₀,₀₎ = |0⟩⟨0| ⊗ (|0⟩⟨0| ⊗ 1)`
scales `|a,b,t⟩` by `⟨0|a⟩ ⟨0|b⟩` and moves both ancillas to `|0⟩`, giving
`⟨0|a⟩ ⟨0|b⟩ · |0,0,t⟩`. Since `⟨0|a⟩ = δ₀ₐ`, the coefficient is `1` on the `(0,0)` branch and `0`
on the other three — the `δ`-functions that collapse the four-branch sum to the success branch. -/
theorem rzTwoAncillaMeasurement_op_zeroZero_qubitBasis (a b t : Fin 2) :
    rzTwoAncillaMeasurement.op (0, 0)
        ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t))).vec
      = (inner ℂ (qubitBasis 0).vec (qubitBasis a).vec *
          inner ℂ (qubitBasis 0).vec (qubitBasis b).vec) •
          ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t))).vec := by
  rw [rzTwoAncillaMeasurement, Measurement.cascade_op, ContinuousLinearMap.comp_apply,
    PureState.tmul_vec, PureState.tmul_vec]
  -- The arguments are given explicitly: `|b⟩ ⊗ |t⟩` is a vector of the bundled `qubit ⊗ qubit`.
  rw [controlMeasurement_op_tmul (S := qubit ⊗ qubit) 0 (qubitBasis a).vec
      ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis t).vec),
    Measurement.onRight_op_tmul (controlMeasurement qubit) qubit 0
      ((InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) (qubitBasis a).vec)
      ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis t).vec),
    controlMeasurement_op_tmul (S := qubit) 0 (qubitBasis b).vec (qubitBasis t).vec,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply, PureState.tmul_vec,
    PureState.tmul_vec]
  exact smul_tmul_smul_tmul_collect _ _ _ _ _

/-- **Exercise 4.41, success branch: the (unnormalised) target operator on a computational basis
target.** When both ancillas are measured `0` and the target starts in `|t⟩`, the success operator
collapses the four-branch output to the single success branch `M₀₀|0,0,t⟩ = rzThreeFifthsAmp 0 0 t ·
|0,0,t⟩`: the two ancilla projectors `⟨0|a'⟩ ⟨0|b'⟩` annihilate every branch but `(a', b') = (0,0)`.
The amplitude `rzThreeFifthsAmp 0 0 t` has `‖·‖² = 5/8` (`rzThreeFifthsAmp_apply`), the Born weight
used in the probability statement of `AxQM/NC/Ch4/Exercise4_41.lean`. -/
theorem rzTwoAncillaMeasurement_op_rzThreeFifthsCircuit_qubitBasis (t : Fin 2) :
    rzTwoAncillaMeasurement.op (0, 0)
        (rzThreeFifthsCircuit.evolvePure
          ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t)))).vec
      = rzThreeFifthsAmp 0 0 t •
          ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t))).vec := by
  rw [rzThreeFifthsCircuit_evolvePure_ketZeroZero_qubitBasis]
  simp only [Fin.sum_univ_two, map_add, map_smul, rzTwoAncillaMeasurement_op_zeroZero_qubitBasis,
    qubitBasis_inner_qubitBasis]
  -- Only the coefficient arithmetic: unfolding the `.vec`s would leave the bundled smul behind.
  norm_num only [ite_true, Fin.zero_eq_one_iff, ite_false, mul_one, mul_zero, zero_mul, one_smul,
    zero_smul, smul_zero, add_zero]

/-- **Exercise 4.41, success branch — the Born probability `5/8` for *every* target `|ψ⟩`, in
terms of state vectors.** For an arbitrary (normalised) target `|ψ⟩`, the success operator sends
the circuit output on `|0,0,ψ⟩` to `|0⟩ ⊗ |0⟩ ⊗ (c · R_z(θ)|ψ⟩)` with `c` the success scalar of
`rzThreeFifthsCircuit_success_eq_rotZ` (`‖c‖² = 5/8`); since `R_z(θ)` is unitary this has squared
norm `‖c‖² = 5/8`, independent of `|ψ⟩`. Proved by expanding `|ψ⟩` in the computational basis
(`EuclideanSpace.basisFun`) and pushing the linear circuit + measurement through the sum; the norm
is `‖c‖ · ‖(unit product state)‖` because `(rotZGate θ).evolvePure ψ` is again a `PureState`, so no
tensor-norm computation is needed. The `Measurement.bornProb` statement following from this is in
`AxQM/NC/Ch4/Exercise4_41.lean`. -/
theorem rzTwoAncillaMeasurement_bornProb_normSq (ψ : PureState qubit) :
    ‖rzTwoAncillaMeasurement.op (0, 0)
        (rzThreeFifthsCircuit.evolvePure ((qubitBasis 0).tmul ((qubitBasis 0).tmul ψ))).vec‖ ^ 2
      = 5 / 8 := by
  obtain ⟨c, hcnorm, hc⟩ := rzThreeFifthsCircuit_success_eq_rotZ
  -- Expand `|ψ⟩ = ∑ᵢ ⟨i|ψ⟩ |i⟩`.
  have hexp : ψ.vec = ∑ i : Fin 2, inner ℂ (qubitBasis i).vec ψ.vec • (qubitBasis i).vec := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 2) ℂ).sum_repr ψ.vec]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [qubitBasis_vec, OrthonormalBasis.repr_apply_apply, EuclideanSpace.basisFun_apply]; rfl
  -- Distribute the input `|0,0,ψ⟩` and the target `R_z|ψ⟩` over that basis expansion.
  have hargexp : ((qubitBasis 0).tmul ((qubitBasis 0).tmul ψ)).vec
      = ∑ i : Fin 2, inner ℂ (qubitBasis i).vec ψ.vec •
          ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis i))).vec := by
    simp only [PureState.tmul_vec]
    conv_lhs => rw [hexp]
    exact tmul_tmul_sum_smul _ _ _ _
  have hRexp : ((qubitBasis 0).tmul ((qubitBasis 0).tmul
        ((rotZGate rzThreeFifthsAngle).evolvePure ψ))).vec
      = ∑ i : Fin 2, inner ℂ (qubitBasis i).vec ψ.vec •
          ((qubitBasis 0).tmul ((qubitBasis 0).tmul
            ((rotZGate rzThreeFifthsAngle).evolvePure (qubitBasis i)))).vec := by
    simp only [PureState.tmul_vec, Evolution.evolvePure_vec]
    conv_lhs => rw [hexp, map_sum]
    simp only [map_smul]
    exact tmul_tmul_sum_smul _ _ _ _
  -- The success operator sends `|0,0,ψ⟩` to `c • |0,0, R_z ψ⟩` (an honest product `PureState`).
  have hproj : rzTwoAncillaMeasurement.op (0, 0)
        (rzThreeFifthsCircuit.evolvePure ((qubitBasis 0).tmul ((qubitBasis 0).tmul ψ))).vec
      = c • ((qubitBasis 0).tmul ((qubitBasis 0).tmul
          ((rotZGate rzThreeFifthsAngle).evolvePure ψ))).vec := by
    rw [Evolution.evolvePure_vec, hargexp, map_sum, map_sum, hRexp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, ← Evolution.evolvePure_vec,
      rzTwoAncillaMeasurement_op_rzThreeFifthsCircuit_qubitBasis i,
      smul_comm c (inner ℂ (qubitBasis i).vec ψ.vec)]
    congr 1
    rw [PureState.tmul_vec, PureState.tmul_vec, PureState.tmul_vec, PureState.tmul_vec,
      Evolution.evolvePure_vec]
    calc rzThreeFifthsAmp 0 0 i •
            ((qubitBasis 0).vec ⊗ₜ[ℂ] ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis i).vec))
        = (qubitBasis 0).vec ⊗ₜ[ℂ]
            ((qubitBasis 0).vec ⊗ₜ[ℂ] (rzThreeFifthsAmp 0 0 i • (qubitBasis i).vec)) :=
          smul_tmul_tmul_inner _ _ _ _
      _ = (qubitBasis 0).vec ⊗ₜ[ℂ] ((qubitBasis 0).vec ⊗ₜ[ℂ]
            (c • (rotZGate rzThreeFifthsAngle).op (qubitBasis i).vec)) := by rw [hc i]
      _ = c • ((qubitBasis 0).vec ⊗ₜ[ℂ] ((qubitBasis 0).vec ⊗ₜ[ℂ]
            (rotZGate rzThreeFifthsAngle).op (qubitBasis i).vec)) :=
          (smul_tmul_tmul_inner _ _ _ _).symm
  rw [hproj, norm_smul, mul_pow,
    ((qubitBasis 0).tmul ((qubitBasis 0).tmul
      ((rotZGate rzThreeFifthsAngle).evolvePure ψ))).normalized, one_pow, mul_one, hcnorm]

end AxQM
