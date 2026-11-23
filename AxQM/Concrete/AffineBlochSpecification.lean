/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Concrete: specifying an affine Bloch-sphere map needs at least four points

This file supplies the mathematical content behind **Nielsen & Chuang, Exercise 8.33 (p. 394)**.

## Context in N&C

For a *trace-preserving* single-qubit quantum operation `E`, N&C (§8.3.2, eq. 8.89) shows the
induced action on the Bloch representation `ρ = ½(I + r·σ)` is an **affine map**

`r ↦ M r + c`   (`M` a real `3 × 3` matrix, `c ∈ ℝ³`),

so `E` is *completely* specified by the `9 + 3 = 12` real parameters of the pair `(M, c)`
(Box 8.5: "there are 12 parameters ... which determine an arbitrary single qubit quantum
operation").

Prove that specifying a single-qubit operation by Bloch-point transforms needs ≥4 points.

## The answer

Knowing how one Bloch point `r_k` transforms records the single vector equation
`r_k ↦ M r_k + c` — three real scalar constraints on `(M, c)`. A set of `N` points therefore
imposes `3N` linear constraints on the `12`-dimensional parameter `(M, c)`. To pin `(M, c)` down
uniquely one needs `3N ≥ 12`, i.e. `N ≥ 4`; three points give only `9 < 12` constraints, leaving
the operation underdetermined. This is a pure statement of linear algebra:

* `four_le_card_of_specifiesAffineBloch` — **the exercise:** any set of Bloch points that
  *specifies* the affine map (two affine maps agreeing on all of them are equal) has at least four
  points. Proved by the dimension count above: the evaluation map `(M, c) ↦ (r ↦ M r + c)` from the
  `12`-dimensional parameter space to the `3·N`-dimensional value space cannot be injective once
  `3N < 12` (`LinearMap.ker_ne_bot_of_finrank_lt`), so a set of `≤ 3` points admits a *nonzero*
  affine map vanishing on all of them, which agrees with the zero map yet differs from it.
* `specifiesAffineBloch_stdFour` / `exists_specifiesAffineBloch_card_four` — **four is enough:** the
  four affinely-independent points `0, e₀, e₁, e₂` (the Bloch-space origin and the three axis
  endpoints) *do* specify the affine map, so the bound `4` is tight.
* `specifiesAffineBloch_sphereFour` / `exists_specifiesAffineBloch_card_four_onSphere` — **four
  points *on the Bloch sphere* are enough:** the exercise speaks of points on the Bloch sphere, and
  the four unit vectors `e₀, -e₀, e₁, e₂` (all pure states, `OnBlochSphere`) already specify the
  affine map — so the tight bound `4` is achieved on the sphere itself, not merely in its interior.

## Related items

Compare the Bloch-affine **Exercise 8.16**
(`AxQM/Concrete/NonTracePreservingBlochExample.lean`). The statement of Exercise 8.33 is in
`AxQM/NC/Ch8/Exercise8_33.lean`.

## Generality of the statement

The claim is stated for an *arbitrary* finite set of Bloch points and the *full* affine family
`r ↦ M r + c` (all real `3 × 3` `M`, all `c ∈ ℝ³`) — the general form of a trace-preserving
single-qubit operation on the Bloch sphere — so `four_le_card_of_specifiesAffineBloch` is precisely
N&C's "the set must contain at least four points", neither more nor less. The `SpecifiesAffineBloch`
predicate is the honest reading of "completely specify": the point-transform data determines the
operation iff two operations with the same transforms on those points coincide.

The lower bound is stated for an *arbitrary* finite set, which is strictly stronger than — and hence
implies — the same bound restricted to sets of Bloch-sphere points (the exercise's setting): a
`≤ 3`-point set fails to specify whether or not its points lie on the sphere. For tightness, N&C's
"points on the Bloch sphere" is honoured on the nose by
`exists_specifiesAffineBloch_card_four_onSphere`, whose witness consists of four genuine unit
vectors (pure states); the interior-point witness `specifiesAffineBloch_stdFour` is retained as an
alternative tightness certificate.
-/

namespace AxQM.Concrete

open Matrix Module

/-- A finite set `s` of Bloch points **specifies** affine Bloch-sphere maps if any two affine maps
`r ↦ M r + c` that transform every point of `s` identically are the same map. This is the formal
reading of Nielsen & Chuang's "completely specify a single qubit operation by describing how a set
of points on the Bloch sphere transform": the point-transform data determines `(M, c)`. -/
def SpecifiesAffineBloch (s : Finset (Fin 3 → ℝ)) : Prop :=
  ∀ (M₁ M₂ : Matrix (Fin 3) (Fin 3) ℝ) (c₁ c₂ : Fin 3 → ℝ),
    (∀ r ∈ s, M₁.mulVec r + c₁ = M₂.mulVec r + c₂) → M₁ = M₂ ∧ c₁ = c₂

/-- The **evaluation map** of the affine family at a finite set of points: it sends the parameter
`(M, c)` of the affine Bloch map `r ↦ M r + c` to the tuple of its values `(r ↦ M r + c)_{r ∈ s}`.
An `ℝ`-linear map from the `12`-dimensional parameter space to the `3 · s.card`-dimensional value
space; its non-injectivity for `s.card ≤ 3` is the engine of Exercise 8.33. -/
noncomputable def evalAffine (s : Finset (Fin 3 → ℝ)) :
    (Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (↥s → (Fin 3 → ℝ)) where
  toFun p := fun r => p.1.mulVec (r : Fin 3 → ℝ) + p.2
  map_add' p q := by
    ext r i
    simp [Matrix.add_mulVec]
    ring
  map_smul' a p := by
    ext r i
    simp [Matrix.smul_mulVec]
    ring

@[simp] theorem evalAffine_apply (s : Finset (Fin 3 → ℝ))
    (p : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) (r : ↥s) :
    evalAffine s p r = p.1.mulVec (r : Fin 3 → ℝ) + p.2 := rfl

/-- The affine-parameter space `(3×3 matrices) × ℝ³` has dimension `9 + 3 = 12`: the `12` real
parameters of Nielsen & Chuang's Box 8.5. -/
theorem finrank_affineParam :
    Module.finrank ℝ (Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) = 12 := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_pi, Module.finrank_self]
  norm_num [Fintype.card_fin]

/-- The value space at `s` — one Bloch vector `ℝ³` per point of `s` — has dimension `3 · s.card`. -/
theorem finrank_values (s : Finset (Fin 3 → ℝ)) :
    Module.finrank ℝ (↥s → (Fin 3 → ℝ)) = 3 * s.card := by
  rw [Module.finrank_pi_fintype]
  simp [mul_comm]

/-- **Underdetermination engine.** A set of at most three Bloch points admits a *nonzero* affine
map `r ↦ M r + c` that annihilates every point of the set. Consequently the point-transform data of
`≤ 3` points cannot distinguish this map from the zero map — the crux of Exercise 8.33. Proved by
the rank–nullity dimension count: the evaluation map from the `12`-dimensional parameter space to
the `3 · s.card ≤ 9`-dimensional value space has nontrivial kernel. -/
theorem exists_affine_ne_zero_vanishing {s : Finset (Fin 3 → ℝ)} (h : s.card ≤ 3) :
    ∃ (M : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ),
      (M, c) ≠ 0 ∧ ∀ r ∈ s, M.mulVec r + c = 0 := by
  have hlt : Module.finrank ℝ (↥s → (Fin 3 → ℝ)) <
      Module.finrank ℝ (Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) := by
    rw [finrank_values, finrank_affineParam]; omega
  have hker : (evalAffine s).ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  rw [Submodule.ne_bot_iff] at hker
  obtain ⟨x, hx_mem, hx_ne⟩ := hker
  refine ⟨x.1, x.2, hx_ne, ?_⟩
  intro r hr
  simpa using congrFun (LinearMap.mem_ker.mp hx_mem) ⟨r, hr⟩

/-- **Nielsen & Chuang, Exercise 8.33.** Any set of Bloch points that completely specifies a single
qubit operation via its point-transforms `r ↦ M r + c` must contain **at least four points**. An
affine map of the Bloch sphere has `12` real parameters (Box 8.5) and each point contributes only
`3` scalar constraints, so `3 · s.card ≥ 12`, i.e. `s.card ≥ 4`. Formally: a set of `≤ 3` points
fails to specify, because (`exists_affine_ne_zero_vanishing`) a nonzero affine map vanishing on it
agrees with the zero map on it yet differs from it. -/
theorem four_le_card_of_specifiesAffineBloch {s : Finset (Fin 3 → ℝ)}
    (h : SpecifiesAffineBloch s) : 4 ≤ s.card := by
  by_contra hlt
  have hle : s.card ≤ 3 := by omega
  obtain ⟨M, c, hne, hvanish⟩ := exists_affine_ne_zero_vanishing hle
  have hagree : ∀ r ∈ s, M.mulVec r + c = (0 : Matrix (Fin 3) (Fin 3) ℝ).mulVec r + 0 := by
    intro r hr; simp [Matrix.zero_mulVec, hvanish r hr]
  obtain ⟨hM, hc⟩ := h M 0 c 0 hagree
  exact hne (Prod.ext_iff.mpr ⟨hM, hc⟩)

/-- **Four points suffice (tightness).** The four affinely-independent Bloch points — the origin
`0` and the three axis endpoints `e₀, e₁, e₂` — *specify* the affine Bloch map: an affine map is
determined by its value at the origin (which fixes the translation `c`) together with its values at
the three axis endpoints (which fix the three columns of `M`, via `Matrix.ext_of_mulVec_single`).
Hence the bound `4` of `four_le_card_of_specifiesAffineBloch` is tight. -/
theorem specifiesAffineBloch_stdFour :
    SpecifiesAffineBloch {0, Pi.single 0 1, Pi.single 1 1, Pi.single 2 1} := by
  intro M₁ M₂ c₁ c₂ hs
  have e0 := hs 0 (by simp)
  have e1 := hs (Pi.single 0 1) (by simp)
  have e2 := hs (Pi.single 1 1) (by simp)
  have e3 := hs (Pi.single 2 1) (by simp)
  simp only [Matrix.mulVec_zero, zero_add] at e0
  subst e0
  refine ⟨Matrix.ext_of_mulVec_single (fun i => ?_), rfl⟩
  fin_cases i
  · exact add_right_cancel e1
  · exact add_right_cancel e2
  · exact add_right_cancel e3

/-- There exists a four-point set specifying the affine Bloch map: together with
`four_le_card_of_specifiesAffineBloch`, this shows **four is the exact minimum** for
Exercise 8.33. -/
theorem exists_specifiesAffineBloch_card_four :
    ∃ s : Finset (Fin 3 → ℝ), SpecifiesAffineBloch s ∧ s.card = 4 := by
  refine ⟨{0, Pi.single 0 1, Pi.single 1 1, Pi.single 2 1}, specifiesAffineBloch_stdFour, ?_⟩
  rw [Finset.card_insert_of_notMem (by simp [funext_iff, Fin.forall_fin_succ, eq_comm]),
      Finset.card_insert_of_notMem (by simp [funext_iff, Fin.forall_fin_succ]),
      Finset.card_insert_of_notMem (by simp [funext_iff, Fin.forall_fin_succ]),
      Finset.card_singleton]

/-- A Bloch vector lies **on the Bloch sphere** (i.e. is a *pure* state `ρ = ½(I + r·σ)`) exactly
when it is a Euclidean unit vector, `‖r‖ = 1`, equivalently `∑ᵢ rᵢ² = 1`. Exercise 8.33 speaks of a
set of points *on the Bloch sphere*, so its tightness witness (`specifiesAffineBloch_sphereFour`)
must use genuine sphere points, not the interior centre `0` (the maximally mixed state). -/
def OnBlochSphere (r : Fin 3 → ℝ) : Prop := ∑ i, (r i) ^ 2 = 1

/-- **Four points on the Bloch sphere suffice (tightness).** The four Bloch-*sphere* points
`e₀ = (1,0,0)`, `-e₀ = (-1,0,0)`, `e₁ = (0,1,0)`, `e₂ = (0,0,1)` — all unit vectors, hence pure
states — *specify* the affine Bloch map. The antipodal pair `e₀, -e₀` fixes the translation `c`
(their two vector equations add to `2c₁ = 2c₂`), after which the three axis endpoints fix the three
columns of `M` (via `Matrix.ext_of_mulVec_single`). Unlike `specifiesAffineBloch_stdFour`, whose
witness uses the interior centre `0`, every point here lies on the Bloch sphere, matching N&C's
wording precisely. -/
theorem specifiesAffineBloch_sphereFour :
    SpecifiesAffineBloch {Pi.single 0 1, -Pi.single 0 1, Pi.single 1 1, Pi.single 2 1} := by
  intro M₁ M₂ c₁ c₂ hs
  have ep := hs (Pi.single 0 1) (by simp)
  have en := hs (-Pi.single 0 1) (by simp)
  have e1 := hs (Pi.single 1 1) (by simp)
  have e2 := hs (Pi.single 2 1) (by simp)
  simp only [Matrix.mulVec_neg] at en
  -- The antipodal pair `e₀, -e₀` pins the translation: adding the two equations cancels `M · e₀`.
  have hc : c₁ = c₂ := by
    funext i
    have hp := congrFun ep i
    have hn := congrFun en i
    simp only [Pi.add_apply, Pi.neg_apply] at hp hn
    linarith [hp, hn]
  subst hc
  -- With `c₁ = c₂` fixed, the three axis endpoints fix the three columns of `M`.
  refine ⟨Matrix.ext_of_mulVec_single (fun i => ?_), rfl⟩
  fin_cases i
  · exact add_right_cancel ep
  · exact add_right_cancel e1
  · exact add_right_cancel e2

/-- There exists a four-point set **all of whose points lie on the Bloch sphere** that specifies the
affine Bloch map. With `four_le_card_of_specifiesAffineBloch` this is Exercise 8.33 in full: at
least four Bloch-sphere points are required, and four Bloch-sphere points already suffice — so four
is the exact minimum, achieved on the sphere itself. -/
theorem exists_specifiesAffineBloch_card_four_onSphere :
    ∃ s : Finset (Fin 3 → ℝ),
      (∀ r ∈ s, OnBlochSphere r) ∧ SpecifiesAffineBloch s ∧ s.card = 4 := by
  refine ⟨{Pi.single 0 1, -Pi.single 0 1, Pi.single 1 1, Pi.single 2 1}, ?_,
    specifiesAffineBloch_sphereFour, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h | h | h <;> subst h <;>
      simp [OnBlochSphere, Pi.single_apply, Pi.neg_apply]
  · rw [Finset.card_insert_of_notMem (by
        norm_num [funext_iff, Fin.forall_fin_succ, Fin.exists_fin_succ,
          Pi.single_apply, Pi.neg_apply]),
      Finset.card_insert_of_notMem (by
        norm_num [funext_iff, Fin.forall_fin_succ, Fin.exists_fin_succ,
          Pi.single_apply, Pi.neg_apply]),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]; intro h; simpa using congrFun h 1),
      Finset.card_singleton]

end AxQM.Concrete
