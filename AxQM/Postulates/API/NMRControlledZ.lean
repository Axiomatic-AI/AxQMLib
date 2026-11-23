/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRCoupledSpinFID
import AxQM.Postulates.API.ControlledZ
import AxQM.Postulates.API.ContinuousSearchHamiltonian
import AxQM.Postulates.API.CnotRotationCommutation

/-!
# AxQM.Postulates.API — the NMR controlled-`Z` (N&C Ex 7.41)

The realisation of the **controlled-`Z` gate** from the two-spin NMR
Hamiltonian (N&C eq. 7.147, `Hsys = a Z₁ + b Z₂ + c Z₁Z₂`) by one period of `Z₁Z₂`-coupled
evolution and a few single-qubit `z`-rotations (Nielsen & Chuang Exercise 7.41). The statement of
Exercise 7.41 is in `AxQM/NC/Ch7/Exercise7_41.lean`.

## What is here

* `globalPhaseGate α` — the **global-phase gate** `e^{iα} · 1` as an `Evolution` on any system,
  with its operator (`globalPhaseGate_op`), pointwise action (`globalPhaseGate_op_apply`), and the
  physics fact that pre-composing it does not change the induced channel
  (`globalPhaseGate_comp_evolve`): a global phase is physically unobservable. It reifies the scalar
  `√i` of N&C's construction (7.152).
* `couplingZZHamiltonian_op_apply_qubitBasis` — the coupling Hamiltonian `c Z₁Z₂` acts on
  `|a⟩⊗|b⟩` as the eigenvalue `c·(-1)ᵃ·(-1)ᵇ`; the input the propagator eigenvector lemma needs to
  evaluate the coupled evolution on the computational basis.
* `nmrControlledZSequence c t` — the **explicit gate sequence**: one period of evolution under the
  `Z₁Z₂` coupling `(couplingZZHamiltonian c).propagator 1 0 t` followed by a `90°` `z`-rotation
  `R_z(-π/2)` on each spin. When `c·t = π/4` this equals the controlled-`Z` up to the global phase
  `e^{-iπ/4}` — proved in `AxQM/NC/Ch7/Exercise7_41.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The global-phase gate -/

/-- **The global-phase gate** `e^{iα} · 1` as an `Evolution` on a quantum system `S`: the unitary
that multiplies every state vector by the fixed unit-modulus scalar `e^{iα}`. It reifies the
scalar prefactor `√i = e^{iπ/4}` appearing in N&C's controlled-`Z` construction (eq. 7.152). -/
def globalPhaseGate (α : ℝ) : Evolution S where
  op := Complex.exp ((α : ℂ) * Complex.I) • (1 : S.space →L[ℂ] S.space)
  unitary := by
    rw [Unitary.mem_iff]
    have hconj : (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I))
        = Complex.exp (-((α : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_I, mul_comm]
    have hmul : (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I))
        * Complex.exp ((α : ℂ) * Complex.I) = 1 := by
      rw [hconj, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hmul' : Complex.exp ((α : ℂ) * Complex.I)
        * (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I)) = 1 := by
      rw [mul_comm]; exact hmul
    constructor
    · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, ← starRingEnd_apply, hmul, one_smul]
    · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, ← starRingEnd_apply, hmul', one_smul]

/-- The operator of `globalPhaseGate α` is `e^{iα} · 1`. -/
@[simp]
theorem globalPhaseGate_op (α : ℝ) :
    (globalPhaseGate (S := S) α).op
      = Complex.exp ((α : ℂ) * Complex.I) • (1 : S.space →L[ℂ] S.space) :=
  rfl

/-- The pointwise action of `globalPhaseGate α`: `(e^{iα} · 1) v = e^{iα} • v`. -/
theorem globalPhaseGate_op_apply (α : ℝ) (v : S.space) :
    (globalPhaseGate (S := S) α).op v = Complex.exp ((α : ℂ) * Complex.I) • v := by
  rw [globalPhaseGate_op, smul_apply, one_apply_eq_self]

/-- **A global phase on the right tensor factor is the same global phase on the composite:**
`1 ⊗ (e^{iα}·1) = e^{iα}·1`, i.e. `(globalPhaseGate α).onRight S = globalPhaseGate α`. The scalar
`e^{iα}` factors out of the `TensorProduct.mapL` and `mapL 1 1 = 1`. -/
theorem globalPhaseGate_onRight (α : ℝ) (S T : QSystem) :
    ((globalPhaseGate α : Evolution T)).onRight S = globalPhaseGate α := by
  apply Evolution.ext
  rw [Evolution.onRight, Evolution.tmul_op, Evolution.id_op, globalPhaseGate_op,
    TensorProduct.mapL_smul_right, TensorProduct.mapL_one, globalPhaseGate_op]
  rfl

/-- **A global phase on the left tensor factor is the same global phase on the composite:**
`(e^{iα}·1) ⊗ 1 = e^{iα}·1`, i.e. `(globalPhaseGate α).onLeft T = globalPhaseGate α`. Mirror of
`globalPhaseGate_onRight`. -/
theorem globalPhaseGate_onLeft (α : ℝ) (S T : QSystem) :
    ((globalPhaseGate α : Evolution S)).onLeft T = globalPhaseGate α := by
  apply Evolution.ext
  rw [Evolution.onLeft, Evolution.tmul_op, Evolution.id_op, globalPhaseGate_op,
    TensorProduct.mapL_smul_left, TensorProduct.mapL_one, globalPhaseGate_op]
  rfl

/-- **The zero global phase is the identity gate:** `globalPhaseGate 0 = 1`, since `e^{i·0} = 1`. -/
theorem globalPhaseGate_zero {S : QSystem} : globalPhaseGate (S := S) 0 = Evolution.id := by
  apply Evolution.ext
  simp only [globalPhaseGate_op, Evolution.id_op, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul]

/-- **The global phase is invariant under transport along a system isomorphism.** For any
`e : S ≃ₛ T`, `Evolution.congr e (globalPhaseGate α) = globalPhaseGate α`. Transport conjugates the
operator by the unital ℂ-linear `⋆`-algebra equivalence `e.toIsometry.conjStarAlgEquiv`, and
conjugating the scalar `e^{iα} · 1` fixes it: `conjStarAlgEquiv (e^{iα} • 1) = e^{iα} • 1` by
`map_smul` and `map_one`. The global-phase companion of `Evolution.congr_one`. -/
theorem Evolution.congr_globalPhaseGate {S T : QSystem} (e : S ≃ₛ T) (α : ℝ) :
    Evolution.congr e (globalPhaseGate α) = (globalPhaseGate α : Evolution T) := by
  apply Evolution.ext
  rw [Evolution.congr_op, globalPhaseGate_op, map_smul, map_one, globalPhaseGate_op]

/-- **A global phase does not change the induced channel.** Pre-composing any evolution `E` with the
global-phase gate `e^{iα} · 1` leaves the density-operator evolution `ρ ↦ E ρ E†` unchanged — the
phase cancels in the conjugation, the precise sense in which a global phase is unobservable. -/
theorem globalPhaseGate_comp_evolve (α : ℝ) (E : Evolution S) (ρ : State S) :
    ((globalPhaseGate α).comp E).evolve ρ = E.evolve ρ := by
  refine Evolution.evolve_eq_of_op_eq_phase_smul ((globalPhaseGate α).comp E) E
    (c := Complex.exp ((α : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I α) ?_ ρ
  rw [Evolution.comp_op, globalPhaseGate_op, ContinuousLinearMap.smul_comp,
    ← ContinuousLinearMap.mul_def, one_mul]

/-! ### Computational-basis eigenvalues of the coupling Hamiltonian -/

/-- **The `Z₁Z₂` coupling Hamiltonian acts diagonally on the computational basis.** For coupling
strength `c`, `(c Z₁Z₂)` sends `|a⟩⊗|b⟩` to the eigenvalue `c·(-1)ᵃ·(-1)ᵇ`, because each factor
contributes its own Pauli-`Z` eigenvalue. This is the eigenvector hypothesis the propagator lemma
`Observable.propagator_op_apply_of_apply_eq_smul` needs to evaluate the coupled evolution
`exp(-i c Z₁Z₂ t)` on `|a⟩⊗|b⟩`. -/
theorem couplingZZHamiltonian_op_apply_qubitBasis (c : ℝ) (a b : Fin 2) :
    (couplingZZHamiltonian c).op ((qubitBasis a) ⊗ (qubitBasis b)).vec
      = ((c : ℂ) * (-1) ^ (a : ℕ) * (-1) ^ (b : ℕ)) • ((qubitBasis a) ⊗ (qubitBasis b)).vec := by
  -- Retype the (defeq) `QSystem.compose` state space to the raw tensor `qubit.space ⊗ qubit.space`
  -- and `(Z ⊗ Z).op` to its `TensorProduct.mapL` form, so the scalar `↑c` and the `TensorProduct`
  -- lemmas share one module (a bare `rw [Observable.tmul_op]` leaves the map at the unreduced
  -- projection, where neither `mapL_tmul` nor the scalar combines fire).
  rw [couplingZZHamiltonian_op, PureState.tmul_vec]
  change (c : ℂ) • (TensorProduct.mapL pauliZObservable.op pauliZObservable.op)
      ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
    = ((c : ℂ) * (-1) ^ (a : ℕ) * (-1) ^ (b : ℕ)) • ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
  rw [TensorProduct.mapL_tmul, pauliZObservable_op_apply_qubitBasis,
    pauliZObservable_op_apply_qubitBasis]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 2
  ring

/-! ### The explicit gate sequence -/

/-- **The NMR controlled-`Z` gate sequence** (Nielsen & Chuang Exercise 7.41): one period of
evolution under the `Z₁Z₂` coupling `(couplingZZHamiltonian c).propagator 1 0 t = exp(-i c Z₁Z₂ t)`,
followed by a `90°` `z`-rotation `R_z(-π/2)` on each of the two spins. When `c · t = π/4`, this
equals the controlled-`Z` gate up to the global phase `e^{-iπ/4}` (see
`AxQM/NC/Ch7/Exercise7_41.lean`). -/
def nmrControlledZSequence (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((couplingZZHamiltonian c).propagator 1 0 t).comp
    (((rotZGate (-(Real.pi / 2))).onLeft qubit).comp
      ((rotZGate (-(Real.pi / 2))).onRight qubit))

/-- **Diagonal action of the gate sequence on the computational basis.** On `|a⟩⊗|b⟩` the sequence
`nmrControlledZSequence c t` acts by the scalar
`R_z(-π/2)ₐₐ · R_z(-π/2)_bb · e^{-i c (-1)ᵃ(-1)ᵇ t}` — the two single-qubit `z`-rotation phases
times the coupled-evolution phase (from `Observable.propagator_op_apply_of_apply_eq_smul` applied to
`couplingZZHamiltonian_op_apply_qubitBasis`). -/
theorem nmrControlledZSequence_op_apply_qubitBasis (c t : ℝ) (a b : Fin 2) :
    (nmrControlledZSequence c t).op ((qubitBasis a) ⊗ (qubitBasis b)).vec
      = (Concrete.rotZ (-(Real.pi / 2)) a a * Concrete.rotZ (-(Real.pi / 2)) b b
          * Complex.exp (-(Complex.I * (((c : ℂ) * (-1) ^ (a : ℕ) * (-1) ^ (b : ℕ)) * (t : ℂ)))))
        • ((qubitBasis a) ⊗ (qubitBasis b)).vec := by
  have hcoupling : ((couplingZZHamiltonian c).propagator 1 0 t).op
        ((qubitBasis a) ⊗ (qubitBasis b)).vec
      = Complex.exp (-(Complex.I * (((c : ℂ) * (-1) ^ (a : ℕ) * (-1) ^ (b : ℕ)) * (t : ℂ))))
        • ((qubitBasis a) ⊗ (qubitBasis b)).vec :=
    Observable.propagator_op_apply_of_apply_eq_smul (couplingZZHamiltonian c) t
      (couplingZZHamiltonian_op_apply_qubitBasis c a b)
  rw [nmrControlledZSequence, Evolution.comp_op, Evolution.comp_op,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, PureState.tmul_vec,
    Evolution.onRight_op_tmul, rotZGate_op_apply_qubitBasis, Evolution.onLeft_op_tmul,
    rotZGate_op_apply_qubitBasis, TensorProduct.smul_tmul_smul, ← PureState.tmul_vec]
  -- Retype the (defeq) `TensorProduct`-level scalar to the propagator's domain
  -- `(qubit ⊗ qubit).space`, so `map_smul` on the linear `.op` fires by a plain `rw`.
  change ((couplingZZHamiltonian c).propagator 1 0 t).op
      ((Concrete.rotZ (-(Real.pi / 2)) a a * Concrete.rotZ (-(Real.pi / 2)) b b)
        • ((qubitBasis a) ⊗ (qubitBasis b)).vec) = _
  rw [map_smul, hcoupling, smul_smul, mul_assoc]

/-- **Diagonal action of the controlled-`Z` gate on the computational basis.** `controlledZGate`
sends `|a⟩⊗|b⟩` to `(-1)^{a·b}·|a⟩⊗|b⟩`, i.e. it flips the sign of `|11⟩` only — the specifying
`diag(1,1,1,-1)`. Derived from the `controlledUnitary` action lemmas and `Z|b⟩ = (-1)ᵇ|b⟩`. -/
theorem controlledZGate_op_apply_qubitBasis (a b : Fin 2) :
    controlledZGate.op ((qubitBasis a) ⊗ (qubitBasis b)).vec
      = (-1 : ℂ) ^ ((a : ℕ) * (b : ℕ)) • ((qubitBasis a) ⊗ (qubitBasis b)).vec := by
  rw [← Evolution.evolvePure_vec, controlledZGate]
  fin_cases a
  · change ((controlledUnitary pauliZGate).evolvePure (qubitBasis 0 ⊗ qubitBasis b)).vec
        = (-1 : ℂ) ^ (((0 : Fin 2) : ℕ) * (b : ℕ)) • (qubitBasis 0 ⊗ qubitBasis b).vec
    rw [controlledUnitary_evolvePure_ketZero, Fin.val_zero, zero_mul, pow_zero, one_smul]
  · change ((controlledUnitary pauliZGate).evolvePure (qubitBasis 1 ⊗ qubitBasis b)).vec
        = (-1 : ℂ) ^ (((1 : Fin 2) : ℕ) * (b : ℕ)) • (qubitBasis 1 ⊗ qubitBasis b).vec
    rw [controlledUnitary_evolvePure_ketOne, PureState.tmul_vec, Evolution.evolvePure_vec,
      pauliZGate_op_apply_qubitBasis, TensorProduct.tmul_smul, ← PureState.tmul_vec]
    congr 1
    rw [Fin.val_one, one_mul]

end AxQM
