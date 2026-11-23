/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliGateTeleportBranches
import AxQM.Postulates.API.GateTeleportMeasurement
import AxQM.Postulates.API.BellLocalMeasurement

/-!
# AxQM.Postulates.API — the three data-qubit measurements of Toffoli gate teleportation

The **measurement readout** of the fault-tolerant Toffoli gate-teleportation circuit of Nielsen &
Chuang **Exercise 10.68** (the Figure on p. 488, part (2)). The pre-measurement state on the
coupled-pairs register `(a₁ ⊗ d_x) ⊗ ((a₂ ⊗ d_y) ⊗ (a₃ ⊗ d_z))` is the eight-outcome branch
superposition `toffoliTeleportCoupling_op_reshape_toffoliAncilla_tmul`
(`AxQM/Postulates/API/ToffoliGateTeleportBranches.lean`). This file measures the three **data**
qubits `d_x, d_y, d_z` (the right qubit of each pair) as a `Measurement` — the Toffoli analogue of
the CNOT Bell-measurement readout `bellPairsMeasurement_op_gateTeleportRegisterGen` (Problem 4.6).

## What is formalised

* `toffoliDataMeasurement` — the **joint measurement of the three data qubits**: the two control
  data qubits `d_x, d_y` in the *computational* (`Z`) basis (`zSignMeasurement`) and the
  target data qubit `d_z` in the `X` basis (`xSignMeasurement`), each acting on the *right* qubit
  of its ancilla↔data pair (identity on the ancilla). A genuine `Measurement` (Postulate 3), from
  the single-qubit basis measurements by `Measurement.onRight` / `Measurement.onLeft` /
  `Measurement.cascade`; the joint outcome is `(m₁, m₂, m₃) : Fin 2 × Fin 2 × Fin 2`.

* `toffoliDataMeasurement_op_tmul` — its measurement operator on a pure tensor: identity on each
  ancilla, the outcome projector on each data qubit,
  `(u₁ ⊗ P^Z_{m₁} v₁) ⊗ ((u₂ ⊗ P^Z_{m₂} v₂) ⊗ (u₃ ⊗ P^X_{m₃} v₃))`.

* `toffoliDataMeasurement_op_toffoliTeleportReshapedInput` — **the collapse identity**
  (the headline, Postulate 4, state update): the measurement operator for outcome `(m₁, m₂, m₃)`
  sends the pre-measurement state (on the abstract coupling input) to the single branch
  `2⁻³ᐟ² (-1)^{m₃·z} (|x⊕m₁, m₁⟩ ⊗ |y⊕m₂, m₂⟩ ⊗ |(x⊕m₁)·(y⊕m₂) ⊕ z, H|m₃⟩⟩)`.
  Orthonormality of the computational / Hadamard bases picks the `(a, b, m₃) = (x⊕m₁, y⊕m₂, m₃)`
  summand out of the eight-branch sum, so measuring the three data qubits collapses the ancilla
  block to `|x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z⟩` — which the propagated-byproduct correction `B_m`
  (`toffoliSwapByproductsPropagated`, `NC/Ch10/Exercise10_68_FTToffoli`) turns into `Toffoli|xyz⟩`
  (the corrected identity is assembled separately).

* `toffoliTeleportPreMeasure` — the pre-measurement gate-teleportation state as an honest
  `PureState` of the coupled-pairs register: prepare the offline resource `toffoliAncilla` beside
  the data `|xyz⟩`, reshape, then apply the coupling `toffoliTeleportCoupling`.
  `toffoliDataMeasurement_op_toffoliTeleportPreMeasure` is the collapse identity on it.

* `toffoliDataMeasurement_bornProb_pos` — **the Born rule (Postulate 3): every outcome is
  possible.** Each of the eight joint outcomes `(m₁, m₂, m₃)` has *positive* Born probability, so
  measuring the
  three data qubits does yield each. By `bornProb = ‖M|ψ⟩‖²`, positivity is `M|ψ⟩ ≠ 0`; the collapse
  identity gives `M|ψ⟩ = 2⁻³ᐟ² (-1)^{m₃·z} (unit tensor)`, nonzero.

Deliberately **not formalised here**: the deterministic *undoing* of the corrections
(applying `B_m†` back, `toffoliSwapByproductCorrection`) to obtain the assembled corrected identity
`reshape(coupling(|xyz⟩ ⊗ |Θ_T⟩)) = 2⁻³ᐟ² Σₘ |m⟩ ⊗ correctionₘ · Toffoli|xyz⟩`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The Hadamard frame is the image of the computational basis under `H`:**
`|x_j⟩ = H|j⟩`. The `X`-eigenbasis vectors `pmQubit` (`|+⟩ = |x₀⟩`, `|−⟩ = |x₁⟩`) are exactly the
Hadamard images of the computational basis states, matching the residual `d_z` states
`hadamardGate.evolvePure (qubitBasis m)` of the eight-branch decomposition. -/
theorem pmQubit_eq_hadamard_qubitBasis (j : Fin 2) :
    pmQubit j = (hadamardGate.evolvePure (qubitBasis j)).vec := by
  fin_cases j
  · change pmQubit 0 = (hadamardGate.evolvePure (qubitBasis 0)).vec
    rw [hadamardGate_evolvePure_qubitBasis_zero]; rfl
  · change pmQubit 1 = (hadamardGate.evolvePure (qubitBasis 1)).vec
    rw [hadamardGate_evolvePure_qubitBasis_one]; rfl

/-- **The computational-basis (`Z`) measurement operator on a basis vector:**
`P^Z_m |k⟩ = δ_{m,k} |m⟩`. The rank-one projector `|m⟩⟨m|` of `zSignMeasurement` fixes `|m⟩`
and kills the orthogonal `|k⟩`, `k ≠ m`. -/
theorem zSignMeasurement_op_qubitBasis (m k : Fin 2) :
    zSignMeasurement.op m (qubitBasis k).vec
      = (if m = k then (1 : ℂ) else 0) • (qubitBasis m).vec := by
  rw [zSignMeasurement_op, rankOne_apply, qubitBasis_inner_qubitBasis]

/-- **The `X`-basis measurement operator on a Hadamard-frame vector:**
`P^X_m H|k⟩ = δ_{m,k} H|m⟩`. The rank-one projector `|x_m⟩⟨x_m|` of `xSignMeasurement` fixes `H|m⟩`
and kills the orthogonal `H|k⟩`, `k ≠ m` — the residual state of an `X`-basis measurement of the
target data qubit. -/
theorem xSignMeasurement_op_hadamard_qubitBasis (m k : Fin 2) :
    xSignMeasurement.op m (hadamardGate.evolvePure (qubitBasis k)).vec
      = (if m = k then (1 : ℂ) else 0) • (hadamardGate.evolvePure (qubitBasis m)).vec := by
  rw [xSignMeasurement_op, rankOne_apply, ← pmQubit_eq_hadamard_qubitBasis k,
    orthonormal_iff_ite.mp pmQubit_orthonormal m k, pmQubit_eq_hadamard_qubitBasis m]

set_option maxHeartbeats 1600000 in
-- Type-checking the two cascades of `onLeft`/`onRight` lifts over the 64-dimensional coupled-pairs
-- register exceeds the default elaboration budget.
/-- **The joint measurement of the three data qubits** (Nielsen & Chuang, Exercise 10.68, the three
data-qubit measurements of the Figure on p. 488). On the coupled-pairs register
`(a₁ ⊗ d_x) ⊗ ((a₂ ⊗ d_y) ⊗ (a₃ ⊗ d_z))`, measure the right (data) qubit of each pair — `d_x, d_y`
in the computational (`Z`) basis (`zSignMeasurement`), `d_z` in the `X` basis
(`xSignMeasurement`) — leaving the ancilla (left) qubits untouched. Assembled from the single-qubit
basis measurements by lifting each to its data slot with `Measurement.onRight` /
`Measurement.onLeft` and cascading; the joint outcome is `(m₁, m₂, m₃) : Fin 2 × Fin 2 × Fin 2`.
A genuine `Measurement`
(Postulate 3). -/
def toffoliDataMeasurement :
    Measurement (Fin 2 × Fin 2 × Fin 2)
      ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  ((zSignMeasurement.onRight qubit).onLeft ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).cascade
    ((((zSignMeasurement.onRight qubit).onLeft (qubit ⊗ qubit)).cascade
        ((xSignMeasurement.onRight qubit).onRight (qubit ⊗ qubit))).onRight (qubit ⊗ qubit))

/-- **The joint data-measurement operator on a pure tensor.** For outcome `(m₁, m₂, m₃)` it is the
identity on each ancilla qubit and the outcome projector on each data qubit:

  `M_{(m₁,m₂,m₃)} ((u₁ ⊗ v₁) ⊗ ((u₂ ⊗ v₂) ⊗ (u₃ ⊗ v₃)))
      = (u₁ ⊗ P^Z_{m₁} v₁) ⊗ ((u₂ ⊗ P^Z_{m₂} v₂) ⊗ (u₃ ⊗ P^X_{m₃} v₃))`.

Unfolding the two cascades and the `onLeft` / `onRight` lifts (`Measurement.cascade_op`,
`Measurement.onLeft_op_tmul`, `Measurement.onRight_op_tmul`); the two `Z` projectors are
`zSignMeasurement.op`, the `X` projector `xSignMeasurement.op`. -/
theorem toffoliDataMeasurement_op_tmul (m₁ m₂ m₃ : Fin 2) (u₁ v₁ u₂ v₂ u₃ v₃ : qubit.space) :
    toffoliDataMeasurement.op (m₁, m₂, m₃)
        ((u₁ ⊗ₜ[ℂ] v₁) ⊗ₜ[ℂ] ((u₂ ⊗ₜ[ℂ] v₂) ⊗ₜ[ℂ] (u₃ ⊗ₜ[ℂ] v₃)))
      = (u₁ ⊗ₜ[ℂ] zSignMeasurement.op m₁ v₁) ⊗ₜ[ℂ]
          ((u₂ ⊗ₜ[ℂ] zSignMeasurement.op m₂ v₂) ⊗ₜ[ℂ]
            (u₃ ⊗ₜ[ℂ] xSignMeasurement.op m₃ v₃)) := by
  simp only [toffoliDataMeasurement, Measurement.cascade_op,
    ]
  rfl

/-- **The collapse identity of the Toffoli gate-teleportation measurement** (Nielsen & Chuang,
Exercise 10.68 part (2), Postulate 4 read of the eight-outcome branch decomposition
`toffoliTeleportCoupling_op_toffoliTeleportReshapedInput_hadamardBranches`). Measuring the three
data qubits with outcome `(m₁, m₂, m₃)` collapses the pre-measurement state to the single branch

  `2⁻³ᐟ² (-1)^{m₃·z} |x⊕m₁, m₁⟩ |y⊕m₂, m₂⟩ |(x⊕m₁)·(y⊕m₂) ⊕ z, H|m₃⟩⟩`.

The two control data qubits collapse to `|m₁⟩, |m₂⟩` (their `Z`-basis outcomes) and the target data
qubit to `H|m₃⟩` (its `X`-basis outcome, with sign `(-1)^{m₃·z}`); the ancilla block is left in
`|x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z⟩`. Orthonormality of the computational and Hadamard bases
(`zSignMeasurement_op_qubitBasis`, `xSignMeasurement_op_hadamard_qubitBasis`) selects the
`(a, b, m₃) = (x⊕m₁, y⊕m₂, m₃)` summand out of the eight-branch sum; the `2⁻³ᐟ²` prefactor is the
branch amplitude. -/
theorem toffoliDataMeasurement_op_toffoliTeleportReshapedInput (x y z m₁ m₂ m₃ : Fin 2) :
    toffoliDataMeasurement.op (m₁, m₂, m₃)
        (toffoliTeleportCoupling.op (toffoliTeleportReshapedInput x y z))
      = Concrete.invSqrt2 ^ 3 • ((-1 : ℂ) ^ (m₃.val * z.val)) •
          (((qubitBasis (x + m₁)).tmul (qubitBasis m₁)).tmul
            (((qubitBasis (y + m₂)).tmul (qubitBasis m₂)).tmul
              ((qubitBasis ((x + m₁) * (y + m₂) + z)).tmul
                (hadamardGate.evolvePure (qubitBasis m₃))))).vec := by
  have hcancel : ∀ p q : Fin 2, p + (p + q) = q := by decide
  have hne : ∀ p q r : Fin 2, r ≠ p + q → q ≠ p + r := by decide
  -- The measurement on one scaled summand; `erw` because the bundled register blocks the
  -- `map_smul`/`toffoliDataMeasurement_op_tmul` rewrites inside the sum.
  have hterm : ∀ (c : ℂ) (u₁ v₁ u₂ v₂ u₃ v₃ : qubit.space),
      toffoliDataMeasurement.op (m₁, m₂, m₃)
          (c • ((u₁ ⊗ₜ[ℂ] v₁) ⊗ₜ[ℂ] ((u₂ ⊗ₜ[ℂ] v₂) ⊗ₜ[ℂ] (u₃ ⊗ₜ[ℂ] v₃))))
        = c • ((u₁ ⊗ₜ[ℂ] zSignMeasurement.op m₁ v₁) ⊗ₜ[ℂ]
            ((u₂ ⊗ₜ[ℂ] zSignMeasurement.op m₂ v₂) ⊗ₜ[ℂ]
              (u₃ ⊗ₜ[ℂ] xSignMeasurement.op m₃ v₃))) := by
    intro c u₁ v₁ u₂ v₂ u₃ v₃
    erw [map_smul, toffoliDataMeasurement_op_tmul]
    rfl
  rw [toffoliTeleportCoupling_op_toffoliTeleportReshapedInput_hadamardBranches]
  simp only [map_smul, map_sum, PureState.tmul_vec]
  refine congrArg (_ • ·) ?_
  rw [Finset.sum_eq_single (x + m₁)]
  · rw [Finset.sum_eq_single (y + m₂)]
    · rw [Finset.sum_eq_single m₃]
      · erw [hterm]
        rw [zSignMeasurement_op_qubitBasis, zSignMeasurement_op_qubitBasis,
          xSignMeasurement_op_hadamard_qubitBasis]
        simp only [hcancel, ↓reduceIte, one_smul]; rfl
      · intro n _ hn
        erw [hterm]
        rw [zSignMeasurement_op_qubitBasis, zSignMeasurement_op_qubitBasis,
          xSignMeasurement_op_hadamard_qubitBasis]
        simp only [ite_eq_right (Ne.symm hn), zero_smul, TensorProduct.tmul_zero]
        rfl
      · intro h; exact absurd (Finset.mem_univ m₃) h
    · intro b _ hb
      refine Finset.sum_eq_zero (fun n _ => ?_)
      erw [hterm]
      rw [zSignMeasurement_op_qubitBasis, zSignMeasurement_op_qubitBasis,
        xSignMeasurement_op_hadamard_qubitBasis]
      simp only [ite_eq_right (hne y m₂ b hb), zero_smul, TensorProduct.tmul_zero,
        TensorProduct.zero_tmul]
      rfl
    · intro h; exact absurd (Finset.mem_univ (y + m₂)) h
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun n _ => ?_))
    erw [hterm]
    rw [zSignMeasurement_op_qubitBasis, zSignMeasurement_op_qubitBasis,
      xSignMeasurement_op_hadamard_qubitBasis]
    simp only [ite_eq_right (hne x m₁ a ha), zero_smul, TensorProduct.tmul_zero,
      TensorProduct.zero_tmul]
    rfl
  · intro h; exact absurd (Finset.mem_univ (x + m₁)) h

set_option maxHeartbeats 800000 in
-- `evolvePure` of the coupling on the 64-dimensional coupled-pairs register exceeds the default
-- elaboration budget.
/-- **The pre-measurement gate-teleportation state**, as an honest `PureState` of the coupled-pairs
register: prepare the offline resource `toffoliAncilla = |Θ_T⟩` beside the data `|xyz⟩`, reshape
into coupled pairs (`toffoliTeleportReshape`), then apply the data↔ancilla coupling
`toffoliTeleportCoupling`. This is the state fed into the three data-qubit measurements in the
fault-tolerant Toffoli circuit of Exercise 10.68 part (2). -/
def toffoliTeleportPreMeasure (x y z : Fin 2) :
    PureState ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  toffoliTeleportCoupling.evolvePure
    (PureState.congr toffoliTeleportReshape (toffoliAncilla.tmul (qubitThreeBasis (x, y, z))))

/-- The pre-measurement state's vector is the coupling applied to the reshaped prepared
resource — hence (by `toffoliTeleportCoupling_op_reshape_toffoliAncilla_tmul`) the eight-branch
superposition. -/
theorem toffoliTeleportPreMeasure_vec (x y z : Fin 2) :
    (toffoliTeleportPreMeasure x y z).vec
      = toffoliTeleportCoupling.op (toffoliTeleportReshape.toIsometry
          (toffoliAncilla.tmul (qubitThreeBasis (x, y, z))).vec) := by
  rw [toffoliTeleportPreMeasure, Evolution.evolvePure_vec, PureState.congr_vec]

set_option maxHeartbeats 800000 in
-- The `.op`/reshape/`.vec` bridge on the 64-dimensional register exceeds the default budget.
/-- **The collapse identity on the honest pre-measurement state.** Measuring the three data qubits
of `toffoliTeleportPreMeasure` (the physical circuit: offline `toffoliAncilla` prep, reshape,
coupling)
with outcome `(m₁, m₂, m₃)` collapses it to the single branch

  `2⁻³ᐟ² (-1)^{m₃·z} |x⊕m₁, m₁⟩ |y⊕m₂, m₂⟩ |(x⊕m₁)·(y⊕m₂) ⊕ z, H|m₃⟩⟩`.

The `PureState` form of `toffoliDataMeasurement_op_toffoliTeleportReshapedInput`, via the reshape
realisation `toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul`
(`toffoliTeleportCoupling.op (reshape(|Θ_T⟩ ⊗ |xyz⟩)) = coupling(toffoliTeleportReshapedInput)`). -/
theorem toffoliDataMeasurement_op_toffoliTeleportPreMeasure (x y z m₁ m₂ m₃ : Fin 2) :
    toffoliDataMeasurement.op (m₁, m₂, m₃) (toffoliTeleportPreMeasure x y z).vec
      = Concrete.invSqrt2 ^ 3 • ((-1 : ℂ) ^ (m₃.val * z.val)) •
          (((qubitBasis (x + m₁)).tmul (qubitBasis m₁)).tmul
            (((qubitBasis (y + m₂)).tmul (qubitBasis m₂)).tmul
              ((qubitBasis ((x + m₁) * (y + m₂) + z)).tmul
                (hadamardGate.evolvePure (qubitBasis m₃))))).vec := by
  rw [toffoliTeleportPreMeasure_vec, toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul,
    toffoliDataMeasurement_op_toffoliTeleportReshapedInput]

set_option maxHeartbeats 800000 in
-- The norm computation runs over the 64-dimensional coupled-pairs register.
/-- **The Born rule for the Toffoli gate-teleportation measurement (Postulate 3): every outcome is
possible.** Each of the eight joint outcomes `(m₁, m₂, m₃)` has *positive* Born probability, so
measuring the three data qubits does yield each. By `bornProb = ‖M|ψ⟩‖²`
(`bornProb_toState_eq_normSq`), positivity is `M|ψ⟩ ≠ 0`; the collapse identity
(`toffoliDataMeasurement_op_toffoliTeleportPreMeasure`) gives
`M|ψ⟩ = 2⁻³ᐟ² (-1)^{m₃·z} • (branch)`, a nonzero scalar (`invSqrt2_ne_zero`, `pow_ne_zero`) times
the unit branch tensor (a `PureState`, so `PureState.normalized`), hence nonzero. -/
theorem toffoliDataMeasurement_bornProb_pos (x y z m₁ m₂ m₃ : Fin 2) :
    0 < toffoliDataMeasurement.bornProb (toffoliTeleportPreMeasure x y z).toState (m₁, m₂, m₃) := by
  rw [Measurement.bornProb_toState_eq_normSq]
  refine pow_pos ?_ 2
  rw [norm_pos_iff, toffoliDataMeasurement_op_toffoliTeleportPreMeasure]
  refine smul_ne_zero (pow_ne_zero _ Concrete.invSqrt2_ne_zero)
    (smul_ne_zero (pow_ne_zero _ (by norm_num)) ?_)
  rw [← norm_ne_zero_iff, PureState.normalized]
  norm_num

end AxQM
