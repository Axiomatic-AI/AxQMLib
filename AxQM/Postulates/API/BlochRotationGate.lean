/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PiEighthGate
import AxQM.Postulates.API.BlochState
import AxQM.Concrete.Rotation
import AxQM.Concrete.BlochRotation

/-!
# AxQM.Postulates.API — the axis rotation gate `R_n̂(θ)` as a qubit evolution

The single-qubit rotation about an arbitrary axis, Nielsen & Chuang
eq. 4.8: the rotation `R_n̂(θ) = exp(−iθ n̂·σ/2)` promoted from its concrete `2 × 2` unitary matrix
`Concrete.rotAxis n θ` to an `Evolution` of the `qubit`, alongside `rotZGate`/`rotXGate`.

* `rotAxisGate n θ` — the gate as `Evolution qubit`. An `Evolution` bundles the
  unitarity obligation, discharged from the matrix-level unitarity
  `Concrete.rotAxis_mem_unitaryGroup` transported through the `⋆`-algebra isomorphism
  `Matrix.toEuclideanCLM`, exactly as for `rotZGate`/`rotXGate`/`hadamardGate`. Unlike those axis
  specializations (`Concrete.rotZ`/`Concrete.rotX`), this is the *general* axis rotation for any
  three-vector `n`, needed by the Bloch-sphere interpretation of rotations (Exercise 4.6).
* `rotAxisGate_op` — a `simp` bridge exposing the underlying operator
  `Matrix.toEuclideanCLM (Concrete.rotAxis n θ)`.
* `rotAxisGate_evolve_blochState` — **the Bloch-sphere action of the gate (Nielsen & Chuang,
  Exercise 4.6)**: for a unit axis `n̂`, the state conjugation `ρ ↦ R_n̂(θ) ρ R_n̂(θ)†`
  (`Evolution.evolve`) rotates the Bloch vector of `blochState v` by `θ` about `n̂`,
  `(rotAxisGate n̂ θ).evolve (blochState v) = blochState (Concrete.rot3D n̂ θ v)`.
  The statement of Exercise 4.6 is in `AxQM/NC/Ch4/Exercise4_6.lean`; the identity is also used by
  the general single-qubit `unitaryGate_evolve_blochState`, the Problem 8.3 Pauli channel and the
  `SU(2) → SO(3)` cover surjectivity.
-/

noncomputable section

namespace AxQM

/-- The **axis rotation gate** `R_n̂(θ) = exp(−iθ n̂·σ/2)` as a closed-system evolution of the
`qubit` (Nielsen & Chuang, eq. 4.8), for an arbitrary three-vector `n`. Its operator is the concrete
rotation matrix `Concrete.rotAxis n θ` promoted through the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM`; unitarity — the `Evolution` proof obligation — is transported from
`Concrete.rotAxis_mem_unitaryGroup` (which holds for *any* axis, the exponential of an
anti-Hermitian matrix). The `z`- and `x`-axis specializations `rotZGate`/`rotXGate` use the
dedicated matrices `Concrete.rotZ`/`Concrete.rotX`; this is the general-axis rotation. -/
def rotAxisGate (n : Fin 3 → ℝ) (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotAxis n θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
      (Concrete.rotAxis_mem_unitaryGroup n θ)

@[simp]
theorem rotAxisGate_op (n : Fin 3 → ℝ) (θ : ℝ) :
    (rotAxisGate n θ).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotAxis n θ) :=
  rfl

/-- **Nielsen & Chuang, Exercise 4.6 — the Bloch-sphere interpretation of rotations.** For a unit
axis `n̂` (`hn`), evolving the Bloch state `blochState v` — the qubit density operator
`½(I + v·σ)` — by the rotation gate `rotAxisGate n̂ θ = R_n̂(θ)` rotates its Bloch vector `v` by the
angle `θ` about `n̂`:
`(rotAxisGate n̂ θ).evolve (blochState v) = blochState (Concrete.rot3D n̂ θ v)`.

The rotated vector stays in the Bloch ball (`Concrete.rot3D_sq_sum`: a rotation preserves the
squared length), so the right-hand `blochState` is well defined; that bound is the second argument.
The proof transports the concrete matrix conjugation identity `Concrete.blochMatrix_conj_rotAxis`
(`R_n̂(θ) · blochMatrix v · R_n̂(θ)ᴴ = blochMatrix (rot3D n̂ θ v)`)
through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` to the operator channel
`ρ ↦ R_n̂(θ) ρ R_n̂(θ)†` (`Evolution.evolve`), matching it to `blochState`'s operator via
`State.ext`.

The unit-axis hypothesis `hn` is genuine (N&C's `n̂` is the rotation *axis*); `θ` and the Bloch
vector `v` are fully general. This is the general-axis
analogue of `unitaryGate_evolve_blochState`; it is used in the Problem 8.3 Pauli channel and the
`SU(2) → SO(3)` cover surjectivity, and is the statement of Exercise 4.6
(`AxQM/NC/Ch4/Exercise4_6.lean`). -/
theorem rotAxisGate_evolve_blochState {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) (v : Fin 3 → ℝ)
    (h : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≤ 1) :
    (rotAxisGate n θ).evolve (blochState v h)
      = blochState (Concrete.rot3D n θ v) ((Concrete.rot3D_sq_sum hn θ v).trans_le h) := by
  apply State.ext
  simp only [Evolution.evolve_op, rotAxisGate_op, blochState_op]
  rw [← Concrete.blochMatrix_conj_rotAxis hn, map_mul, map_mul, ← Matrix.star_eq_conjTranspose,
    map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  -- both sides are now the operator conjugation `R · (v·σ) · R†`; the remaining `rfl` bridges the
  -- `qubit.space ≡ EuclideanSpace ℂ (Fin 2)` defeq (unfolded only at default transparency).
  rfl

end AxQM
