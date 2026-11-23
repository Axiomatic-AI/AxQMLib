/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerConcatenation

/-!
# Concrete: the concatenated stabilizer generators are independent (Nielsen & Chuang, Ex 10.62)

This file proves the **independence
half** of Nielsen & Chuang, Exercise 10.62 — the `n₁n₂ − 1` explicit concatenated generators
`concatGen` (built in `AxQM/Concrete/StabilizerConcatenation.lean`) have `𝔽₂`-linearly independent
check rows. Together with the commutation half (`concatGen_commute`, same file) this is exactly
the hypothesis of Proposition 10.5 (`stabilizedSubspace_finrank`): `n₁n₂ − 1` independent
commuting generators on `n₁n₂` qubits cut out a `2¹`-dimensional code — an `[n₁n₂, 1]` stabilizer
code. The dimension assembly is in `AxQM/Concrete/StabilizerConcatenationDimension.lean`.

Everything here is stated for raw matrix / index data (`Matrix`, `Concrete.checkRow`,
`Concrete.checkVec`, `Fin n → Fin 4`, `ZMod 2`) and the concatenation construction.

## The argument (block restriction to the inner code)

Write the check rows in the flat `checkVec`/`checkVecG` form so the `𝔽₂` symplectic toolkit
applies. Independence is proved on the product qubit index `Fin (g₂+1) × Fin (g₁+1)` (block, inner
qubit) via `concatRaw_checkVecG_linearIndependent`, then transported to the flattened `Fin (n₁n₂)`
register (`concatGen_checkVec_linearIndependent`) and to the pair-valued `checkRow` form
(`concatGen_checkRow_linearIndependent`) that Proposition 10.5 consumes.

Suppose a vanishing `𝔽₂`-combination `∑_c e_c · r(concatRaw c) = 0`. For each block `b`, the
**block-restriction** linear map `blockRestr b` (precomposition with the block-`b` inclusion) reads
off block `b`'s inner check row; applied to the combination it yields, per block,

`∑_a e_{(b,a)} · r(C₁.gen a) + (∑_j e_j x_{jb}) · r(X̄) + (∑_j e_j z_{jb}) · r(Z̄) = 0`,

a combination of the **inner** code's generators together with its logical `X̄, Z̄`. Those are
jointly independent (`stabCode1_jointIndep`: `linearIndependent_sumElim_hyperbolic` applied to the
inner code), so every coefficient vanishes: `e_{(b,a)} = 0` (all inner coefficients), and
`∑_j e_j x_{jb} = 0`, `∑_j e_j z_{jb} = 0` for every block `b`. The latter two, ranging over all
blocks, say `∑_j e_j · r(C₂.gen j) = 0`, so the **outer** generators' independence (`C₂.gen_indep`)
forces every `e_j = 0`. All coefficients vanish, so the concatenated generators are independent.

The `checkRow` ⇄ `checkVec` transfer (`checkVec_linearIndependent_of_checkRow`,
`checkRow_linearIndependent_of_checkVec`) is the flattening linear equivalence
`(Fin n → 𝔽₂) × (Fin n → 𝔽₂) ≃ₗ (Fin n ⊕ Fin n → 𝔽₂)` (`LinearEquiv.sumArrowLequivProdArrow`),
which carries `checkVec g` to `checkRow g`; linear independence passes across it
(`LinearIndependent.of_comp` / `LinearIndependent.map'`).
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {g₁ g₂ : ℕ}

/-! ### `checkRow` ⇄ `checkVec` transfer of linear independence -/

/-- **Independence of the pair-valued check rows gives independence of the flat check vectors.** The
flattening map `(Fin N → 𝔽₂) × (Fin N → 𝔽₂) ≃ₗ (Fin N ⊕ Fin N → 𝔽₂)`
(`LinearEquiv.sumArrowLequivProdArrow`) sends `checkVec (f c)` to `checkRow (f c)`; since it is a
linear equivalence, linear independence of `checkRow ∘ f` transfers to `checkVec ∘ f`
(`LinearIndependent.of_comp`). -/
theorem checkVec_linearIndependent_of_checkRow {N : ℕ} {κ : Type*} (f : κ → (Fin N → Fin 4))
    (h : LinearIndependent (ZMod 2) (fun c => checkRow (f c))) :
    LinearIndependent (ZMod 2) (fun c => checkVec (f c)) := by
  set E := LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin N) (ZMod 2) (ZMod 2)
  refine LinearIndependent.of_comp E.toLinearMap ?_
  have hcomp : (E.toLinearMap ∘ fun c => checkVec (f c)) = fun c => checkRow (f c) := by
    funext c; rfl
  rw [hcomp]; exact h

/-- **Independence of the flat check vectors gives independence of the pair-valued check rows.** The
converse transfer, mapping across the same flattening equivalence with `LinearIndependent.map'`.
This is the direction that delivers the `checkRow`-form independence Proposition 10.5 consumes. -/
theorem checkRow_linearIndependent_of_checkVec {N : ℕ} {κ : Type*} (f : κ → (Fin N → Fin 4))
    (h : LinearIndependent (ZMod 2) (fun c => checkVec (f c))) :
    LinearIndependent (ZMod 2) (fun c => checkRow (f c)) := by
  set E := LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin N) (ZMod 2) (ZMod 2)
  have hmap := h.map' E.toLinearMap (LinearMap.ker_eq_bot.mpr E.injective)
  have hcomp : (E.toLinearMap ∘ fun c => checkVec (f c)) = fun c => checkRow (f c) := by
    funext c; rfl
  rwa [hcomp] at hmap

/-! ### The inner code's generators and logical operators are jointly independent -/

/-- **The generators of an `[n, 1]` code together with its logical `X̄, Z̄` are `𝔽₂`-independent.**
For a `StabCode1 g` code `C`, the family `{r(C.gen a)}_a ∪ {r(X̄), r(Z̄)}` (indexed by
`Fin g ⊕ Fin 2`) is linearly independent. The generators' check rows are independent (`C.gen_indep`,
bridged to the flat form); each is symplectically orthogonal to `X̄` and `Z̄` (the logical operators
commute with the generators, `C.logX_commute`/`C.logZ_commute`, via Exercise 10.33); and `(X̄, Z̄)`
is a hyperbolic pair (`logXZ_symplecticForm_one`). Hence `linearIndependent_sumElim_hyperbolic`
extends the generators by the pair. -/
theorem stabCode1_jointIndep {g : ℕ} (C : StabCode1 g) :
    LinearIndependent (ZMod 2)
      (Sum.elim (fun a => checkVec (C.gen a)) ![checkVec C.logX, checkVec C.logZ]) := by
  have hv : LinearIndependent (ZMod 2) (fun a => checkVec (C.gen a)) :=
    checkVec_linearIndependent_of_checkRow _ C.gen_indep
  have hvx : ∀ a, symplecticForm (checkVec (C.gen a)) (checkVec C.logX) = 0 := fun a => by
    rw [symplecticForm_comm]
    exact (pauliString_commute_iff_symplecticForm _ _).mp (C.logX_commute a)
  have hvz : ∀ a, symplecticForm (checkVec (C.gen a)) (checkVec C.logZ) = 0 := fun a => by
    rw [symplecticForm_comm]
    exact (pauliString_commute_iff_symplecticForm _ _).mp (C.logZ_commute a)
  exact linearIndependent_sumElim_hyperbolic _ _ _ hv hvx hvz (logXZ_symplecticForm_one C)

/-! ### Block restriction to a single inner block -/

/-- **The block-`b` restriction of a product-index check vector**, as an `𝔽₂`-linear map:
precomposition with the block-`b` qubit inclusion `Fin (g₁+1) ↪ Fin (g₂+1) × Fin (g₁+1)`,
`i ↦ (b, i)` (on both the `X`- and `Z`-halves). Applied to the check vector of a Pauli string on the
product register it reads off that string's restriction to block `b`. Being a coordinate
precomposition it is manifestly linear, so it carries a vanishing combination of concatenated check
rows to a vanishing combination of the block's inner check rows. -/
def blockRestr (b : Fin (g₂ + 1)) :
    ((Fin (g₂ + 1) × Fin (g₁ + 1)) ⊕ (Fin (g₂ + 1) × Fin (g₁ + 1)) → ZMod 2) →ₗ[ZMod 2]
      (Fin (g₁ + 1) ⊕ Fin (g₁ + 1) → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2)
    (Sum.map (fun i : Fin (g₁ + 1) => (b, i)) (fun i : Fin (g₁ + 1) => (b, i)))

/-- **The block restriction reads off the inner check row of a block.** `blockRestr b` applied to
the product-index check vector `r(f)` is the flat check vector of `f`'s restriction to block `b`,
`i ↦ f (b, i)`. Immediate from the definitions (`checkVecG`/`checkVec` agree coordinatewise on the
block-`b` inclusion). -/
theorem blockRestr_checkVecG (b : Fin (g₂ + 1)) (f : Fin (g₂ + 1) × Fin (g₁ + 1) → Fin 4) :
    blockRestr (g₁ := g₁) b (checkVecG f) = checkVec (fun i => f (b, i)) := by
  funext s; cases s <;> rfl

/-! ### Independence on the product qubit index -/

/-- **The concatenated generators have `𝔽₂`-independent check rows** (product-index form). For each
block `b`, applying `blockRestr b` to a vanishing combination `∑_c e_c · r(concatRaw c) = 0`
yields a vanishing combination of the inner code's generators and its logical `X̄, Z̄`; by their
joint independence (`stabCode1_jointIndep`) every inner coefficient `e_{(b,a)}` vanishes and the two
outer-coefficient block sums `∑_j e_j x_{jb}`, `∑_j e_j z_{jb}` vanish. Ranging over all blocks, the
latter assemble into `∑_j e_j · r(C₂.gen j) = 0`, so the outer generators' independence
(`C₂.gen_indep`) kills every outer coefficient `e_j`. All coefficients vanish. -/
theorem concatRaw_checkVecG_linearIndependent (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    LinearIndependent (ZMod 2) (fun c => checkVecG (concatRaw C₁ C₂ c)) := by
  refine Fintype.linearIndependent_iff.mpr (fun e he => ?_)
  -- Per block `b`: restrict `he` and read off coefficients via the inner joint independence.
  have hblock : ∀ b : Fin (g₂ + 1), ∀ x,
      (Sum.elim (fun a => e (Sum.inl (b, a)))
        ![∑ j, e (Sum.inr j) * (pauliBit (C₂.gen j b)).1,
          ∑ j, e (Sum.inr j) * (pauliBit (C₂.gen j b)).2]) x = 0 := by
    intro b
    have hb := congrArg (blockRestr (g₁ := g₁) b) he
    rw [map_sum, map_zero] at hb
    simp_rw [map_smul, blockRestr_checkVecG] at hb
    set w : Fin g₁ ⊕ Fin 2 → ZMod 2 :=
      Sum.elim (fun a => e (Sum.inl (b, a)))
        ![∑ j, e (Sum.inr j) * (pauliBit (C₂.gen j b)).1,
          ∑ j, e (Sum.inr j) * (pauliBit (C₂.gen j b)).2] with hw_def
    -- The restricted combination is a combination of the inner joint family.
    have hmatch : (∑ x, w x •
          (Sum.elim (fun a => checkVec (C₁.gen a)) ![checkVec C₁.logX, checkVec C₁.logZ]) x)
        = ∑ c, e c • checkVec (fun i => concatRaw C₁ C₂ c (b, i)) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      congr 1
      · -- inner generators: only block `b` survives the `if b = b'`
        symm
        rw [Fintype.sum_prod_type, Fintype.sum_eq_single b (fun b' hb' => ?_)]
        · refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [checkVec_concatRaw_inl, ite_eq_left rfl]; simp [hw_def]
        · refine Finset.sum_eq_zero (fun a _ => ?_)
          rw [checkVec_concatRaw_inl, ite_eq_right (Ne.symm hb'), smul_zero]
      · -- encoded outer generators: `r(encStr p) = x_p r(X̄) + z_p r(Z̄)`, collect coefficients
        rw [Fin.sum_univ_two]
        simp only [checkVec_concatRaw_inr, encStr_checkVec, smul_add, smul_smul]
        rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]; simp [hw_def]
    exact Fintype.linearIndependent_iff.mp (stabCode1_jointIndep C₁) w (hmatch.trans hb)
  -- The outer coefficients assemble into a vanishing combination of `C₂`'s check rows.
  have hgen2 : LinearIndependent (ZMod 2) (fun j => checkVec (C₂.gen j)) :=
    checkVec_linearIndependent_of_checkRow _ C₂.gen_indep
  have houter : ∀ j, e (Sum.inr j) = 0 := by
    refine Fintype.linearIndependent_iff.mp hgen2 (fun j => e (Sum.inr j)) ?_
    funext s
    cases s with
    | inl b =>
      simp only [Finset.sum_apply, Pi.smul_apply, checkVec_inl, smul_eq_mul, Pi.zero_apply]
      exact hblock b (Sum.inr 0)
    | inr b =>
      simp only [Finset.sum_apply, Pi.smul_apply, checkVec_inr, smul_eq_mul, Pi.zero_apply]
      exact hblock b (Sum.inr 1)
  intro c
  obtain (⟨b, a⟩ | j) := c
  · have := hblock b (Sum.inl a); simpa using this
  · exact houter j

/-! ### Independence on the flattened register, and the `checkRow` form -/

/-- **The concatenated generators have `𝔽₂`-independent check vectors on the flattened `Fin (n₁n₂)`
register.** Reindexing back from `Fin (n₁n₂)` to the product qubit index `Fin (g₂+1) × Fin (g₁+1)`
(via `finProdFinEquiv`) is a coordinate relabeling — an injective precomposition linear map
(`LinearMap.funLeft` along the bijection `Sum.map`), across which the product-index independence
`concatRaw_checkVecG_linearIndependent` transfers. -/
theorem concatGen_checkVec_linearIndependent (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    LinearIndependent (ZMod 2) (fun c => checkVec (concatGen C₁ C₂ c)) := by
  set e := (finProdFinEquiv (m := g₂ + 1) (n := g₁ + 1)).symm with he
  have hsurj : Function.Surjective (Sum.map (⇑e) (⇑e)) :=
    Sum.map_surjective.mpr ⟨e.surjective, e.surjective⟩
  have hinj : Function.Injective (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.map (⇑e) (⇑e))) :=
    LinearMap.funLeft_injective_of_surjective _ _ _ hsurj
  have hmap := (concatRaw_checkVecG_linearIndependent C₁ C₂).map'
      (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.map (⇑e) (⇑e)))
      (LinearMap.ker_eq_bot.mpr hinj)
  have hfam : (⇑(LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.map (⇑e) (⇑e)))
        ∘ fun c => checkVecG (concatRaw C₁ C₂ c))
      = fun c => checkVec (concatGen C₁ C₂ c) := by
    funext c s
    rw [Function.comp_apply, LinearMap.funLeft_apply]
    rw [show concatGen C₁ C₂ c = concatRaw C₁ C₂ c ∘ e from rfl, checkVec_comp_equiv]
  rwa [hfam] at hmap

/-- **Nielsen & Chuang, Exercise 10.62 (independence half): the concatenated stabilizer generators
are independent.** The `n₁n₂ − 1` concatenated generators `concatGen` have `𝔽₂`-linearly independent
check-matrix rows (`checkRow`) — Nielsen & Chuang's Proposition 10.3 independence condition. This is
the flat-form independence `concatGen_checkVec_linearIndependent` transported to the pair-valued
`checkRow` form (`checkRow_linearIndependent_of_checkVec`). Together with `concatGen_commute` it
makes `⟨concatGen⟩` an `[n₁n₂, 1]` stabilizer code via Proposition 10.5
(`stabilizedSubspace_finrank`), the subject of the sibling terminal file. -/
theorem concatGen_checkRow_linearIndependent (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    LinearIndependent (ZMod 2) (fun c => checkRow (concatGen C₁ C₂ c)) :=
  checkRow_linearIndependent_of_checkVec _ (concatGen_checkVec_linearIndependent C₁ C₂)

end AxQM.Concrete
