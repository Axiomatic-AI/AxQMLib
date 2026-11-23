/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardABC
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.PureState

/-!
# The `|0⟩`-column of the `ŷ`-rotation gate

The action of the `ŷ`-rotation gate `R_y(θ)` on the computational ground state `|0⟩` and the two
amplitudes it produces:

* `rotYGate_op_qubitBasisZero` — `R_y(θ)|0⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩`, the `0`-th column of the
  matrix `R_y(θ) = !![cos(θ/2), −sin(θ/2); sin(θ/2), cos(θ/2)]` (Nielsen & Chuang, eq. 4.5),
  transported through `Matrix.toEuclideanCLM` (`rotYGate_op`).
* `rotYGate_evolvePure_qubitBasisZero_overlap` — the resulting amplitudes as an `overlap`:
  `⟨b | R_y(θ)|0⟩⟩ = cos(θ/2)` for `b = 0` and `sin(θ/2)` for `b = 1`, read off the column via
  orthonormality of the computational basis (`qubitBasis_inner_qubitBasis`).

Both are the general-`θ` companions of the specific `R_y(−π/2)` columns in
`Postulates/API/NMRBellPrep.lean`. They are reused wherever a single-qubit amplitude against a
`ŷ`-rotated basis is needed — e.g. the Schumacher-compression typical basis of N&C Box 12.4
(Exercise 12.6).
-/

open scoped InnerProductSpace

namespace AxQM

/-- **`R_y(θ)|0⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩`.** The `0`-th column of the `ŷ`-rotation matrix
`R_y(θ) = !![cos(θ/2), −sin(θ/2); sin(θ/2), cos(θ/2)]` (Nielsen & Chuang, eq. 4.5), obtained from
`rotYGate_op` (`(rotYGate θ).op = toEuclideanCLM (Concrete.rotY θ)`) and `Concrete.rotY_eq`. -/
theorem rotYGate_op_qubitBasisZero (θ : ℝ) :
    (rotYGate θ).op (qubitBasis 0).vec
      = (Real.cos (θ / 2) : ℂ) • (qubitBasis 0).vec
        + (Real.sin (θ / 2) : ℂ) • (qubitBasis 1).vec := by
  rw [rotYGate_op]
  simp only [qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotY θ))
        (EuclideanSpace.single 0 1)).ofLp
      = ((Real.cos (θ / 2) : ℂ) • (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2))
          + (Real.sin (θ / 2) : ℂ) • EuclideanSpace.single 1 1).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.rotY_eq, Matrix.mulVec, dotProduct, EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The amplitudes of `R_y(θ)|0⟩` in the computational basis.** For `b : Fin 2`,
`⟨b | R_y(θ)|0⟩⟩ = cos(θ/2)` when `b = 0` and `sin(θ/2)` when `b = 1`. Read off the `0`-th column
`rotYGate_op_qubitBasisZero` via orthonormality of `{|0⟩, |1⟩}` (`qubitBasis_inner_qubitBasis`).
Both amplitudes are real (the `ŷ`-rotation has a real matrix). -/
theorem rotYGate_evolvePure_qubitBasisZero_overlap (θ : ℝ) (b : Fin 2) :
    (qubitBasis b).overlap ((rotYGate θ).evolvePure (qubitBasis 0))
      = if b = 0 then (Real.cos (θ / 2) : ℂ) else (Real.sin (θ / 2) : ℂ) := by
  rw [PureState.overlap_def, Evolution.evolvePure_vec, rotYGate_op_qubitBasisZero,
    inner_add_right, inner_smul_right, inner_smul_right, qubitBasis_inner_qubitBasis,
    qubitBasis_inner_qubitBasis]
  fin_cases b <;> simp

end AxQM
