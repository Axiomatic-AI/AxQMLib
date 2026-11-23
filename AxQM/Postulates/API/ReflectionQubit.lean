/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Reflection
import AxQM.Postulates.API.Qubit
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Postulates.API — the qubit reflection `R_ψ` as a concrete matrix

Identities specializing the state reflection `R_ψ = I − 2|ψ⟩⟨ψ|`
(`AxQM.Postulates.API.Reflection`) to the qubit `EuclideanSpace ℂ (Fin 2)`, where the
rank-one projector `|ψ⟩⟨ψ|` is the concrete outer product `Concrete.outerSelf ψ.vec.ofLp` and the
whole reflection is a `2 × 2` matrix promoted through the `⋆`-algebra map `Matrix.toEuclideanCLM`.

* `rankOne_self_eq_toEuclideanCLM_outerSelf` — for any `v : EuclideanSpace ℂ (Fin 2)`, the abstract
  rank-one projector `|v⟩⟨v|` equals the concrete outer product `outerSelf v.ofLp = vecMulVec v
  (star v)` promoted via `Matrix.toEuclideanCLM`. A thin qubit specialization of the general
  bridge `Matrix.toEuclideanCLM_vecMulVec`, needed for the `X`/`Y`-eigenstates `|-⟩`, `|-i⟩`.
* `reflectionEvolution_qubit_op_eq_toEuclideanCLM` — the reflection `R_ψ` on the qubit has operator
  `toEuclideanCLM (I − 2 · outerSelf ψ.vec.ofLp)`, obtained by pushing the `1` and the scalar `2`
  through the `⋆`-algebra map. This reduces the identity `R_ψ = Pauli` (Nielsen & Chuang, Problem
  6.2(2)) to a `2 × 2` matrix identity.
-/

open scoped InnerProductSpace
open InnerProductSpace

noncomputable section

namespace AxQM

/-- **Bridge (rank-one projector of a Euclidean vector).** For any `v : EuclideanSpace ℂ (Fin 2)`,
the abstract rank-one projector `|v⟩⟨v|` equals the concrete outer product `outerSelf v.ofLp =
vecMulVec v (star v)` promoted through `Matrix.toEuclideanCLM`. This generalizes
`toEuclideanCLM_outerSelf_ket` from the computational-basis kets to an arbitrary vector, so it
applies to the `X`/`Y`-eigenstates `|-⟩`, `|-i⟩` (as well as any qubit pure state via `ψ.vec`). -/
theorem rankOne_self_eq_toEuclideanCLM_outerSelf (v : EuclideanSpace ℂ (Fin 2)) :
    rankOne ℂ v v = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.outerSelf v.ofLp) := by
  rw [Concrete.outerSelf, Matrix.toEuclideanCLM_vecMulVec]

/-- **Bridge (the qubit reflection as a matrix).** The reflection `R_ψ = I − 2|ψ⟩⟨ψ|` on the qubit
has operator `toEuclideanCLM (I − 2 · outerSelf ψ.vec.ofLp)` — the `2 × 2` matrix `I − 2|ψ⟩⟨ψ|`
promoted to the qubit space. Combined with the `Concrete/` matrix identities `I − 2 · outerSelf • =
Pauli`, this yields `R_ψ = Pauli` for the Pauli `−1`-eigenstates (N&C Problem 6.2(2)). -/
theorem reflectionEvolution_qubit_op_eq_toEuclideanCLM (ψ : PureState qubit) :
    (reflectionEvolution ψ).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (1 - (2 : ℂ) • Concrete.outerSelf ψ.vec.ofLp) := by
  -- Restate the general bridge at `ψ.vec` so its `rankOne` carries the goal's `qubit.space`
  -- instances (the abbreviation `qubit.space = EuclideanSpace ℂ (Fin 2)` makes the two defeq),
  -- letting the rewrite fire; then push `1` and `2 •` through the `⋆`-algebra map.
  have h : rankOne ℂ ψ.vec ψ.vec
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.outerSelf ψ.vec.ofLp) :=
    rankOne_self_eq_toEuclideanCLM_outerSelf ψ.vec
  rw [reflectionEvolution_op, h, map_sub, map_one, map_smul]
  rfl

end AxQM
