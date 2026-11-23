/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.Eigenstate
import AxQM.Concrete.PauliEigenstateBloch

/-!
# Nielsen & Chuang, Exercise 4.1 — Bloch-sphere points of the Pauli eigenvectors

*(N&C p. 174.)*

Find Bloch-sphere points for the normalized eigenvectors of the Pauli matrices.

The Bloch-sphere point of a single-qubit pure state `|ψ⟩` is the vector `r⃗` for which its density
operator is `|ψ⟩⟨ψ| = ½(I + r⃗·σ⃗)` — the (physics) Bloch vector of Exercise 2.72(1), unique by
`blochState_injective`. This file computes it for the six normalized eigenvectors of `X, Y, Z`
(Exercise 2.11), given as the library's standard qubit pure states:

* `qubitPlus`, `qubitMinus` (`|±⟩ = (|0⟩ ± |1⟩)/√2`, the `±1` eigenvectors of `X`) → `±x̂`;
* `qubitPlusI`, `qubitMinusI` (`|±i⟩ = (|0⟩ ± i|1⟩)/√2`, the `±1` eigenvectors of `Y`) → `±ŷ`;
* `qubitKet0`, `qubitBasis 1` (`|0⟩`, `|1⟩`, the `+1`/`-1` eigenvectors of `Z`) → `±ẑ`.

## What is proved

For each eigenvector, a theorem `*_blochVector` stating `(state).toState = blochState axis`, i.e.
its density operator is `½(I + axis·σ⃗)`, pinning its Bloch vector (unique by
`blochState_injective`) to the coordinate axis. This is the exercise's answer.

Complementing this, a theorem `*_hasEigenstate_pauli*` certifies — at the level of
observables — that each of these six states genuinely *is* a `±1` eigenstate of the corresponding
Pauli vector observable `n⃗·σ⃗` (`Observable.HasEigenstate`), so that "the eigenvectors of the Pauli
matrices" is a theorem about states and observables, not merely a matrix fact asserted in prose:

* `qubitPlus`/`qubitMinus` are the `±1` eigenstates of `pauliXObservable` (`X`);
* `qubitPlusI`/`qubitMinusI` are the `±1` eigenstates of `pauliYObservable` (`Y`);
* `qubitKet0`/`qubitBasis 1` are the `±1` eigenstates of `pauliZObservable` (`Z`).

Together with the Bloch points, this is the full content of Exercise 4.1: these states are
the Pauli eigenstates, *and* their Bloch points are `±x̂ / ±ŷ / ±ẑ`.

## Design

* **Standard qubit states.** The eigenvectors are stated as the standard
  states — `qubitPlus`/`qubitMinus` (`AxQM/Postulates/API/RelativePhase.lean`), `qubitKet0` /
  `qubitBasis` (`AxQM/Postulates/API/Qubit.lean`) — so they come with the inner-product,
  orthonormality and Pauli-expectation results for those states. The `Y` eigenstates `|±i⟩` are
  `qubitPlusI` / `qubitMinusI` (in `RelativePhase.lean`, defined like `qubitPlus` / `qubitMinus`).
* **The `*_eq_blochPureState` bridges** identify each canonical state with the §1.2 pure state
  `blochPureState θ φ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩` (eq. 1.4) at the appropriate `(θ,φ)`. Each
  is proved by `PureState.ext` from `Concrete.blochKet_* = xPlus/xMinus/yPlus/yMinus/ket 0/ket 1`
  (`AxQM/Concrete/PauliEigenstateBloch.lean`).
* **The Bloch points** then use the identity `blochPureState_toState_op` (Exercise
  2.72(4): `|ψ(θ,φ)⟩⟨ψ(θ,φ)| = Matrix.toEuclideanCLM (blochMatrix (blochSphereVector θ φ))`) and
  the axis evaluations `Concrete.blochSphereVector_* = ![±1, …]`; no new operator computation.
* The statements are for `PureState` and `State` (the state `blochState`), the Bloch vector being a
  plain `Fin 3 → ℝ`.
* **The eigenstate certifications** are term-mode applications of `Observable.hasEigenstate_of_smul`
  to two lemmas each: the `PureState`'s `_vec` identity and the operator eigenvalue equation
  `pauli*Observable_apply_* : σ (toLp v) = ±1 • toLp v` — mirroring Exercise 2.53's Hadamard
  eigenstates. The supporting lemmas are in `AxQM/Postulates/API/Qubit.lean`:
  * `pauliYObservable` (`n = (0, 1, 0)`) and its `_op` lemma, beside `pauliXObservable` /
    `pauliZObservable`;
  * the `pauli*Observable_apply_toLp` bridges (`σ (toLp v) = toLp (σ *ᵥ v)`, fixing the `↑qubit`-vs-
    `EuclideanSpace` operator-coercion mismatch via `exact`);
  * the six `pauli*Observable_apply_*` operator eigenvalue equations, transporting Exercise 2.11's
    concrete `Concrete.pauli*_mulVec_*` (`M *ᵥ v = μ • v`) through those bridges.
-/

noncomputable section

namespace AxQM

/-! ### The canonical eigenstates as §1.2 pure states

Each bridge is `PureState.ext` composed from the canonical state's `_vec` lemma and the
`Concrete.blochKet_* = …` eigenvector identification. -/

/-- `|+⟩` is the §1.2 pure state at `(θ,φ) = (π/2, 0)`. -/
theorem qubitPlus_eq_blochPureState : qubitPlus = blochPureState (Real.pi / 2) 0 := by
  apply PureState.ext
  simp only [qubitPlus_vec, blochPureState_vec, Concrete.blochKet_pi_div_two_zero]
  rfl

/-- `|-⟩` is the §1.2 pure state at `(θ,φ) = (π/2, π)`. -/
theorem qubitMinus_eq_blochPureState : qubitMinus = blochPureState (Real.pi / 2) Real.pi := by
  apply PureState.ext
  simp only [qubitMinus_vec, blochPureState_vec, Concrete.blochKet_pi_div_two_pi]
  rfl

/-- `|+i⟩` is the §1.2 pure state at `(θ,φ) = (π/2, π/2)`. -/
theorem qubitPlusI_eq_blochPureState :
    qubitPlusI = blochPureState (Real.pi / 2) (Real.pi / 2) := by
  apply PureState.ext
  simp only [qubitPlusI_vec, blochPureState_vec, Concrete.blochKet_pi_div_two_pi_div_two]
  rfl

/-- `|-i⟩` is the §1.2 pure state at `(θ,φ) = (π/2, 3π/2)`. -/
theorem qubitMinusI_eq_blochPureState :
    qubitMinusI = blochPureState (Real.pi / 2) (3 * Real.pi / 2) := by
  apply PureState.ext
  simp only [qubitMinusI_vec, blochPureState_vec, Concrete.blochKet_pi_div_two_three_pi_div_two]
  rfl

/-- `|0⟩` is the §1.2 pure state at the north pole `(θ,φ) = (0, 0)`. -/
theorem qubitKet0_eq_blochPureState : qubitKet0 = blochPureState 0 0 := by
  apply PureState.ext
  simp only [qubitKet0_vec, blochPureState_vec, Concrete.blochKet_zero_zero]
  rfl

/-- `|1⟩` is the §1.2 pure state at the south pole `(θ,φ) = (π, 0)`. -/
theorem qubitBasis_one_eq_blochPureState : qubitBasis 1 = blochPureState Real.pi 0 := by
  apply PureState.ext
  rw [qubitBasis_vec, blochPureState_vec, Concrete.blochKet_pi_zero]
  rfl

/-! ### The Bloch points — the answer to Exercise 4.1

Each eigenvector's density operator is `blochState axis = ½(I + axis·σ⃗)`, so (by
`blochState_injective`) its Bloch vector is the coordinate axis. Via the `*_eq_blochPureState`
bridges, `blochPureState_toState_op` (Exercise 2.72(4)) and the `Concrete.blochSphereVector_*`
axis evaluations. -/

/-- **The Bloch point of `|+⟩` is `+x̂ = (1, 0, 0)`.** -/
theorem qubitPlus_blochVector :
    qubitPlus.toState = blochState ![1, 0, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := by
  rw [qubitPlus_eq_blochPureState]
  apply State.ext
  rw [blochPureState_toState_op, blochState_op, Concrete.blochSphereVector_pi_div_two_zero]

/-- **The Bloch point of `|-⟩` is `-x̂ = (-1, 0, 0)`.** -/
theorem qubitMinus_blochVector :
    qubitMinus.toState = blochState ![-1, 0, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := by
  rw [qubitMinus_eq_blochPureState]
  apply State.ext
  rw [blochPureState_toState_op, blochState_op, Concrete.blochSphereVector_pi_div_two_pi]

/-- **The Bloch point of `|+i⟩` is `+ŷ = (0, 1, 0)`.** -/
theorem qubitPlusI_blochVector :
    qubitPlusI.toState = blochState ![0, 1, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := by
  rw [qubitPlusI_eq_blochPureState]
  apply State.ext
  rw [blochPureState_toState_op, blochState_op, Concrete.blochSphereVector_pi_div_two_pi_div_two]

/-- **The Bloch point of `|-i⟩` is `-ŷ = (0, -1, 0)`.** -/
theorem qubitMinusI_blochVector :
    qubitMinusI.toState = blochState ![0, -1, 0]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := by
  rw [qubitMinusI_eq_blochPureState]
  apply State.ext
  rw [blochPureState_toState_op, blochState_op,
    Concrete.blochSphereVector_pi_div_two_three_pi_div_two]

/-- **The Bloch point of `|0⟩` is `+ẑ = (0, 0, 1)`.** -/
theorem qubitKet0_blochVector :
    qubitKet0.toState = blochState ![0, 0, 1]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := by
  rw [qubitKet0_eq_blochPureState]
  apply State.ext
  rw [blochPureState_toState_op, blochState_op, Concrete.blochSphereVector_zero_zero]

/-- **The Bloch point of `|1⟩` is `-ẑ = (0, 0, -1)`.** -/
theorem qubitBasis_one_blochVector :
    (qubitBasis 1).toState = blochState ![0, 0, -1]
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]) := by
  rw [qubitBasis_one_eq_blochPureState]
  apply State.ext
  rw [blochPureState_toState_op, blochState_op, Concrete.blochSphereVector_pi_zero]

/-! ### The states are the ±1 eigenstates of the Pauli observables

The observable-level reading of "the eigenvectors of the Pauli matrices": each of the six
states is a `±1` eigenstate of the Pauli vector observable `n⃗·σ⃗`
(`Observable.HasEigenstate`). Each is a term-mode application of `Observable.hasEigenstate_of_smul`
to the state's `_vec` identity (the state is already normalized, so `c = 1`) and the
operator eigenvalue equation `pauli*Observable_apply_*` (in `AxQM/Postulates/API/Qubit.lean`). -/

/-- **`|+⟩` is the `+1` eigenstate of `X`:** `X |+⟩ = |+⟩`. -/
theorem qubitPlus_hasEigenstate_pauliX : pauliXObservable.HasEigenstate 1 qubitPlus :=
  pauliXObservable.hasEigenstate_of_smul (qubitPlus_vec.trans (one_smul _ _).symm)
    pauliXObservable_apply_xPlus

/-- **`|-⟩` is the `-1` eigenstate of `X`:** `X |-⟩ = -|-⟩`. -/
theorem qubitMinus_hasEigenstate_pauliX : pauliXObservable.HasEigenstate (-1) qubitMinus :=
  pauliXObservable.hasEigenstate_of_smul (qubitMinus_vec.trans (one_smul _ _).symm)
    pauliXObservable_apply_xMinus

/-- **`|+i⟩` is the `+1` eigenstate of `Y`:** `Y |+i⟩ = |+i⟩`. -/
theorem qubitPlusI_hasEigenstate_pauliY : pauliYObservable.HasEigenstate 1 qubitPlusI :=
  pauliYObservable.hasEigenstate_of_smul (qubitPlusI_vec.trans (one_smul _ _).symm)
    pauliYObservable_apply_yPlus

/-- **`|-i⟩` is the `-1` eigenstate of `Y`:** `Y |-i⟩ = -|-i⟩`. -/
theorem qubitMinusI_hasEigenstate_pauliY : pauliYObservable.HasEigenstate (-1) qubitMinusI :=
  pauliYObservable.hasEigenstate_of_smul (qubitMinusI_vec.trans (one_smul _ _).symm)
    pauliYObservable_apply_yMinus

/-- **`|0⟩` is the `+1` eigenstate of `Z`:** `Z |0⟩ = |0⟩`. -/
theorem qubitKet0_hasEigenstate_pauliZ : pauliZObservable.HasEigenstate 1 qubitKet0 :=
  pauliZObservable.hasEigenstate_of_smul (qubitKet0_vec.trans (one_smul _ _).symm)
    pauliZObservable_apply_ket0

/-- **`|1⟩` is the `-1` eigenstate of `Z`:** `Z |1⟩ = -|1⟩`. -/
theorem qubitBasis_one_hasEigenstate_pauliZ :
    pauliZObservable.HasEigenstate (-1) (qubitBasis 1) :=
  pauliZObservable.hasEigenstate_of_smul ((qubitBasis_vec 1).trans (one_smul _ _).symm)
    pauliZObservable_apply_ket1

/-- **`|0⟩` is the `+1` eigenstate of `Z`:** `Z |0⟩ = |0⟩`, phrased on the `qubitBasis`-indexed ket
(the `+1` companion of `qubitBasis_one_hasEigenstate_pauliZ`; cf. `qubitKet0_hasEigenstate_pauliZ`
on `qubitKet0`). -/
theorem qubitBasis_zero_hasEigenstate_pauliZ :
    pauliZObservable.HasEigenstate 1 (qubitBasis 0) :=
  pauliZObservable.hasEigenstate_of_smul ((qubitBasis_vec 0).trans (one_smul _ _).symm)
    pauliZObservable_apply_ket0

end AxQM
