/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PiEighthGate

/-!
# Nielsen & Chuang, Exercise 4.3 — up to a global phase, the π/8 gate satisfies `T = R_z(π/4)`

*(N&C p. 175.)*

Show that up to global phase the pi/8 gate satisfies T=R_z(pi/4).

The π/8 gate is `T = diag(1, e^{iπ/4})` (eq. 4.2) and
`R_z(θ) = exp(-iθZ/2) = diag(e^{-iθ/2}, e^{iθ/2})`
(eq. 4.6), so `R_z(π/4) = diag(e^{-iπ/8}, e^{iπ/8})` and (eq. 4.3)
`T = e^{iπ/8} · diag(e^{-iπ/8}, e^{iπ/8}) = e^{iπ/8} R_z(π/4)`.
The two gates differ only by the scalar `e^{iπ/8}`, a **global phase**.

## The physics: what "up to a global phase" means, and what the theorem states

A global phase is physically unobservable precisely because it cancels in the map a gate induces on
*states* (density operators), `ρ ↦ U ρ U†`: for `U = e^{iπ/8} R_z(π/4)`,
`U ρ U† = e^{iπ/8} R_z(π/4) ρ (e^{iπ/8})^* R_z(π/4)† = |e^{iπ/8}|² R_z(π/4) ρ R_z(π/4)†`,
which equals `R_z(π/4) ρ R_z(π/4)†` since `|e^{iπ/8}|² = 1`.
So `T` and `R_z(π/4)`, *as quantum operations*, are the **same gate** — even though as operators on
vectors they differ by the phase.

The theorem of this file is exactly that physical statement:

* `tGate_evolve_eq_rotZGate_evolve` — for every state `ρ` of the qubit,
  `T.evolve ρ = R_z(π/4).evolve ρ`, i.e. the π/8 gate and `R_z(π/4)` induce the *same* state
  evolution.

## Where the pieces live

The exercise's underlying matrix identity and the gates are in:

* **`AxQM.Concrete.tMatrix`** and **`Concrete.tMatrix_eq_expPiDivEight_smul_rotZ`**
  (`AxQM/Concrete/PiEighthGate.lean`) — the T gate matrix (eq. 4.2) and the pure `2 × 2` matrix
  identity `T = e^{iπ/8} • R_z(π/4)` (eq. 4.3), built on the §4.2 rotation matrices
  (`AxQM/Concrete/Rotation.lean`).
* **`AxQM.tGate`, `rotZGate`** and **`tGate_op_eq_expPiDivEight_smul_rotZGate`**
  (`AxQM/Postulates/API/PiEighthGate.lean`) — the gates as `Evolution qubit`, and the operator-level
  form `T = e^{iπ/8} • R_z(π/4)` of Exercise 4.3.
* **`Evolution.evolve_eq_of_op_eq_phase_smul`** (`AxQM/Postulates/API/Evolution.lean`, valid
  for any gate) — the lemma that a unit-modulus global phase
  leaves the induced channel unchanged; the theorem below is that lemma applied to the operator
  identity with `c = e^{iπ/8}` (`‖e^{iπ/8}‖ = 1`).
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.3.** Up to a global phase, the π/8 gate `T` equals `R_z(π/4)`:
as quantum operations they are the *same* gate — for every state `ρ` of the qubit, `T` and
`R_z(π/4)` induce the identical state evolution `ρ ↦ U ρ U†`. The global phase `e^{iπ/8}` relating
the two operators (`tGate_op_eq_expPiDivEight_smul_rotZGate`, eq. 4.3) has unit modulus, so it
cancels in the conjugation defining `Evolution.evolve` (`Evolution.evolve_eq_of_op_eq_phase_smul`);
this is the precise sense in which a global phase is physically unobservable. -/
theorem tGate_evolve_eq_rotZGate_evolve (ρ : State qubit) :
    tGate.evolve ρ = (rotZGate (Real.pi / 4)).evolve ρ :=
  Evolution.evolve_eq_of_op_eq_phase_smul tGate (rotZGate (Real.pi / 4))
    (Complex.norm_exp_ofReal_mul_I _) tGate_op_eq_expPiDivEight_smul_rotZGate ρ

end AxQM
