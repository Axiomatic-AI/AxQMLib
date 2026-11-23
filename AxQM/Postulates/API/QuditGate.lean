/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qudit
import ToMathlib.Analysis.CStarAlgebra.Matrix
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Postulates.API — a unitary matrix as an `Evolution` gate on `qudit d`

The construction promoting a `d × d` unitary matrix to a closed-system
`Evolution (qudit d)`. It is the arbitrary-dimension analogue of the single-qubit
`unitaryGate` (`AxQM/Postulates/API/UnitaryBlochRotation.lean`, `qubit = qudit 2`): the register
model of Nielsen & Chuang's circuits is `qudit (2ⁿ)`, and many gates are naturally specified
as concrete `d × d` unitary matrices (e.g. the beamsplitter / phase-shifter matrices of
Problem 7.2).

* `quditGate hU` — the `Evolution (qudit d)` whose operator is the unitary matrix `U`
  (`hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ`) promoted through the `⋆`-algebra isomorphism
  `Matrix.toEuclideanCLM`. Unitarity of the operator is transported from `hU` by
  `Unitary.map_mem`, exactly as `qftEvolution` / `pauliZGate` / `unitaryGate` do.
* `quditGate_op` — the `simp` bridge `(quditGate hU).op = Matrix.toEuclideanCLM U` exposing the
  underlying operator (definitionally, `rfl`).
-/

open Matrix

noncomputable section

namespace AxQM

/-- The **unitary gate of a `d × d` unitary matrix** `U` (`hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ`)
as a closed-system `Evolution` of `qudit d`. Its operator is `U` promoted through the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM`; the `Evolution` unitarity obligation is transported from `hU`
by `Unitary.map_mem`. The arbitrary-dimension generalization of the single-qubit `unitaryGate`
(`qubit = qudit 2`); `qftEvolution` and `pauliZGate` are instances of this pattern. -/
def quditGate {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Evolution (qudit d) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) U
  unitary := Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) hU

/-- The operator of `quditGate hU` is `U` promoted through `Matrix.toEuclideanCLM`. -/
@[simp]
theorem quditGate_op {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (quditGate hU).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) U :=
  rfl

/-- **`quditGate` respects matrix equality.** If two unitary matrices on `Fin d` are equal, their
promoted evolutions are equal. This lets a matrix identity be transported through `quditGate` even
though the matrix appears in the type of the unitarity witness: unitary-group membership is a
`Prop`, so once the matrices coincide the two witnesses agree by proof irrelevance. -/
theorem quditGate_congr {d : ℕ} {U V : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h : U = V) : quditGate hU = quditGate hV := by
  subst h; rfl

/-- **The `quditGate` of the identity matrix is the identity evolution.**
`quditGate 1 = Evolution.id` on `qudit d`: both operators are `1` — the left by `quditGate_op` and
`toEuclideanCLM`'s `map_one`, the right by `Evolution.id_op`. -/
theorem quditGate_one_eq_id {d : ℕ}
    (h : (1 : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quditGate h = Evolution.id := by
  apply Evolution.ext
  rw [quditGate_op, Evolution.id_op]
  exact map_one _

/-- **A `quditGate`'s action on a computational basis vector is its matrix column.**
`(quditGate hU).op |z⟩ = ∑ₛ U_{sz} |s⟩`, the `z`-th column of `U` expanded over the computational
basis `quditBasis`. The general "gate on a basis vector" fact from which the column formula of any
`quditGate` is read off. The `qudit`-vs-`EuclideanSpace` identification of the state space is
bridged by `Matrix.toEuclideanCLM_apply_single` (`exact`, at full transparency). -/
theorem quditGate_op_quditBasis_vec {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (z : Fin d) :
    (quditGate hU).op (quditBasis z).vec = ∑ s : Fin d, U s z • (quditBasis s).vec := by
  rw [quditGate_op, quditBasis_vec]
  refine (Matrix.toEuclideanCLM_apply_single U z).trans ?_
  exact Finset.sum_congr rfl (fun s _ => by congr 1)

end AxQM
