/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PiL2

/-! # Relating two orthonormal families by a linear isometry equivalence

In a finite-dimensional inner product space `E`, any two orthonormal families of the **same size**
`a, a' : Fin n → E` are related by a linear isometry equivalence of `E`: there is
`L : E ≃ₗᵢ[𝕜] E` with `L (a' i) = a i` for every `i`.

This is the standard "two orthonormal sets of equal cardinality are unitarily equivalent" fact:
because `n ≤ dim E`, each family extends to an orthonormal *basis* of `E` (both indexed by
`Fin (dim E)`, agreeing with the family on the first `n` coordinates via
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`); the isometry equivalence sending one
extended basis to the other (`OrthonormalBasis.equiv`) then carries `a' i` to `a i`.

It underlies, on the physics side, the fact that two bipartite pure states with identical Schmidt
coefficients are related by a local unitary `U ⊗ V` (Nielsen–Chuang, Exercise 2.80).
-/

@[expose] public section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Two orthonormal families of the same size are related by a linear isometry equivalence.**
Given orthonormal families `a a' : Fin n → E` in a finite-dimensional inner product space `E`,
there is a linear isometry equivalence `L : E ≃ₗᵢ[𝕜] E` mapping the second family to the first,
`L (a' i) = a i` for all `i`.

Since an orthonormal family is linearly independent, `n ≤ dim E`, so each family extends to an
orthonormal basis of `E` indexed by `Fin (dim E)` and agreeing with the family on the coordinates
`Fin.castLE : Fin n → Fin (dim E)` (`exists_orthonormalBasis_extension_of_card_eq`). The isometry
`OrthonormalBasis.equiv` between the two extended bases (along the identity reindexing) sends each
extended `a'`-basis vector to the corresponding `a`-basis vector, hence `a' i ↦ a i`. -/
theorem exists_linearIsometryEquiv_apply_eq [FiniteDimensional 𝕜 E] {n : ℕ} {a a' : Fin n → E}
    (ha : Orthonormal 𝕜 a) (ha' : Orthonormal 𝕜 a') :
    ∃ L : E ≃ₗᵢ[𝕜] E, ∀ i, L (a' i) = a i := by
  classical
  have hn : n ≤ Module.finrank 𝕜 E := by
    simpa using ha.linearIndependent.fintype_card_le_finrank
  -- Extend an orthonormal family `c : Fin n → E` to an orthonormal basis of `E` indexed by
  -- `Fin (dim E)`, agreeing with `c` on the coordinates `Fin.castLE hn`.
  have extend : ∀ {c : Fin n → E}, Orthonormal 𝕜 c →
      ∃ B : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E, ∀ i, B (Fin.castLE hn i) = c i := by
    intro c hc
    set d := Module.finrank 𝕜 E with hd
    set emb : Fin n → Fin d := Fin.castLE hn with hemb_def
    have hemb : Function.Injective emb := Fin.castLE_injective hn
    -- Pad `c` to a total function on `Fin d` (zero off the range of `emb`).
    set v : Fin d → E := Function.extend emb c 0 with hv
    have hcard : Module.finrank 𝕜 E = Fintype.card (Fin d) := by simp [hd]
    -- The padded family is orthonormal on `range emb` (it is `c` reindexed there).
    have hrestrict : Orthonormal 𝕜 ((Set.range emb).domRestrict v) := by
      set σ : Fin n ≃ ↥(Set.range emb) := Equiv.ofInjective emb hemb with hσ
      have key : (Set.range emb).domRestrict v = c ∘ σ.symm := by
        funext x
        obtain ⟨i, rfl⟩ := σ.surjective x
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
        change v (σ i : Fin d) = c i
        have hx : (σ i : Fin d) = emb i := rfl
        rw [hx, hv, hemb.extend_apply]
      rw [key]
      exact hc.comp _ σ.symm.injective
    obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hrestrict
    refine ⟨B, fun i => ?_⟩
    rw [hB (emb i) ⟨i, rfl⟩, hv, hemb.extend_apply]
  obtain ⟨bA, hbA⟩ := extend ha
  obtain ⟨bA', hbA'⟩ := extend ha'
  refine ⟨bA'.equiv bA (Equiv.refl _), fun i => ?_⟩
  rw [← hbA' i, ← hbA i]
  simp [OrthonormalBasis.equiv_apply]

end Orthonormal
