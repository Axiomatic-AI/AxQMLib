/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Purification
public import ToMathlib.Analysis.InnerProductSpace.PurificationFreedom

/-!
# Invariance of purifications under a unitary on the ancilla

`TensorProduct.IsPurification ρ Ψ` records that the bipartite vector `Ψ : E ⊗[ℂ] F` purifies the
density operator `ρ` on the kept factor `E` — i.e. the right-partial-trace of `|Ψ⟩⟨Ψ|` is `ρ`.
Applying a unitary `U` to the **ancilla** factor `F` (via `I_E ⊗ U`) does not change that reduced
operator, so it maps purifications of `ρ` to purifications of `ρ`:

* `TensorProduct.isPurification_mapL_id` : for a unitary `U` on `F`,
  `IsPurification ρ ((I_E ⊗ U) Ψ) ↔ IsPurification ρ Ψ`.

This is the operator-level content of the fact that the *ancilla* of a purification is free up to a
unitary (the companion of Nielsen & Chuang Exercise 2.81, which says two purifications of the same
`ρ` differ by such a unitary). The proof runs through the matricization: `I_E ⊗ U` acts on
`matricize b Ψ` by right-composition with the unitary transpose `b.transposeOp U`
(`TensorProduct.matricize_mapL_id`), and right-composing by a unitary leaves the Gram operator
`M M†` — hence the purification predicate `M M† = ρ`
(`TensorProduct.isPurification_iff_matricize_comp_adjoint`) — unchanged.
-/

@[expose] public section

namespace TensorProduct

variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
  [Fintype ι]

/-- **A unitary on the ancilla preserves the purification predicate.** If `U` is a unitary on the
ancilla factor `F`, then `(I_E ⊗ U) Ψ` purifies `ρ` iff `Ψ` does. Applying `I_E ⊗ U` right-composes
the matricization by the unitary `b.transposeOp U` (`matricize_mapL_id`), which cancels in the Gram
operator `M M†` characterizing the purification predicate. -/
theorem isPurification_mapL_id
    (b : OrthonormalBasis ι ℂ F) {ρ : E →L[ℂ] E} {U : F →L[ℂ] F}
    (hU : U ∈ unitary (F →L[ℂ] F)) (Ψ : E ⊗[ℂ] F) :
    IsPurification ρ (mapL (1 : E →L[ℂ] E) U Ψ) ↔ IsPurification ρ Ψ := by
  have hWWadj :
      (b.transposeOp U).comp (ContinuousLinearMap.adjoint (b.transposeOp U)) = 1 := by
    have h := (Unitary.mem_iff.mp (b.transposeOp_mem_unitary hU)).2
    rwa [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint] at h
  have hop :
      ((matricize b Ψ).comp (b.transposeOp U)).comp
          (ContinuousLinearMap.adjoint ((matricize b Ψ).comp (b.transposeOp U)))
        = (matricize b Ψ).comp (ContinuousLinearMap.adjoint (matricize b Ψ)) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc (b.transposeOp U), hWWadj]; rfl
  rw [isPurification_iff_matricize_comp_adjoint b ρ (mapL (1 : E →L[ℂ] E) U Ψ),
    isPurification_iff_matricize_comp_adjoint b ρ Ψ, matricize_mapL_id, hop]

end TensorProduct
