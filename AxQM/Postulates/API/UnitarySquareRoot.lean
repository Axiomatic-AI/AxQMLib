/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.UnitarySquareRoot
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.Qubit

/-!
# AxQM.Postulates.API — the square root of a single-qubit gate

Every single-qubit gate `U : Evolution qubit` has a *square-root gate* `V` with `V ∘ V = U`. This
is the gate-level (`Evolution`) form of the matrix square root `Concrete.exists_unitary_sq`, and it
is the input to Nielsen & Chuang's Figure 4.8 construction of `C²(U)` (Exercises 4.21/4.22): that
circuit is built from a `V` with `V² = U`, so the existence of such a `V` for an *arbitrary* gate
`U` is what makes the *"for any single-qubit unitary `U`"* statement of Exercise 4.22 faithful (no
weakening of the hypothesis).

## What is formalised

* `AxQM.Evolution.exists_comp_self_eq` — for every `U : Evolution qubit` there is a
  `V : Evolution qubit` with `V.comp V = U`.

## Design notes

**Construction (lift through `toEuclideanCLM`).** It lifts the matrix square root through the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM`: `M := toEuclideanCLM⁻¹ U.op` is a unitary matrix
(`toEuclideanCLM` is a `⋆`-isomorphism, so it preserves and reflects unitarity),
`Concrete.exists_unitary_sq` gives a unitary `√M` with `√M * √M = M`, and `V := toEuclideanCLM √M`
is a gate with `V ∘ V = U` because `toEuclideanCLM` carries matrix multiplication to composition
(`map_mul`) and `toEuclideanCLM M = U.op` (`apply_symm_apply`). This is the same operator↔matrix
bridge used by `Evolution.exists_op_eq_phase_smul_rotAxisGate` (Exercise 4.8).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Every single-qubit gate has a square-root gate.** For any `U : Evolution qubit` there is a
`V : Evolution qubit` with `V.comp V = U` (i.e. `V² = U`). The witness is `toEuclideanCLM √M`, where
`√M` is a unitary square root (`Concrete.exists_unitary_sq`) of the matrix `M = toEuclideanCLM⁻¹
U.op` of `U`; `V.comp V = U` follows because the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`
carries matrix multiplication to operator composition. This supplies the `V` with `V² = U` required
by Nielsen & Chuang's Figure 4.8 construction of `C²(U)`. -/
theorem Evolution.exists_comp_self_eq (U : Evolution qubit) :
    ∃ V : Evolution qubit, V.comp V = U := by
  obtain ⟨M, hMmem, hMsq⟩ := Concrete.exists_unitary_sq
    (Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).symm U.unitary)
  refine ⟨⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M,
      Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) hMmem⟩, ?_⟩
  apply Evolution.ext
  rw [Evolution.comp_op]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M).comp
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M) = U.op
  rw [← ContinuousLinearMap.mul_def, ← map_mul, hMsq]
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).apply_symm_apply U.op

end AxQM
