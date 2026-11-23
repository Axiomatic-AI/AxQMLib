/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFCTensor
public import ToMathlib.Analysis.InnerProductSpace.GeometricMeanMaximality
public import ToMathlib.Analysis.Convex.SierpinskiMidpoint
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Joint operator concavity of `(A, B) ↦ A^q ⊗ B^r` (Lieb's Theorem 1, tensor form)

For strictly positive operators `A : E →L[ℂ] E` and `B : F →L[ℂ] F` on finite-dim complex
Hilbert spaces, the map `(A, B) ↦ A^q ⊗ B^r` is jointly operator-concave whenever `(q, r)` lies
in the Lieb simplex `{(q, r) | 0 ≤ q, 0 ≤ r, q + r ≤ 1}` — Carlen §6.1 / Lieb's Theorem 1.

## Proof structure (Carlen §6.1)

Define `ConcaveAt q r ⊂ Prop` as the predicate that the joint concavity inequality holds at
the exponent pair `(q, r)`.

1. **Base cases**: `ConcaveAt 0 0`, `ConcaveAt 1 0`, `ConcaveAt 0 1`. Each follows
   from `mapL`'s bilinearity.
2. **Midpoint closure**: if `ConcaveAt q₁ r₁` and `ConcaveAt q₂ r₂`,
   then `ConcaveAt ((q₁+q₂)/2) ((r₁+r₂)/2)`. Via the GM-reduction identity + GM concavity
   + GM monotonicity.
3. **Topological closedness**: `{(q, r) | ConcaveAt q r}` is closed in `ℝ × ℝ`
   via joint continuity `Continuous.mapL` + `continuous_const_rpow`.
4. **Sierpinski lift** (via `Convex.of_isClosed_of_midpoint_mem`): closed + midpoint-stable
   ⇒ convex.
5. **Simplex identification**: the convex hull of `{(0,0), (1,0), (0,1)}` is the
   Lieb simplex; combined with convexity of the concavity-set, gives the headline.

## Main results

- `LiebTensor.concaveAt_zero_zero`, `concaveAt_one_zero`, `concaveAt_zero_one`: base cases.
- `LiebTensor.concaveAt_midpoint`: midpoint-closure.
- `LiebTensor.concaveAt_isClosed`: topological closedness.
- `LiebTensor.concaveAt_of_mem_simplex`: joint concavity on the Lieb simplex (headline).
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

/-- The "inner-product against `v`" functional `M ↦ re ⟨v, M v⟩` on a complex Hilbert space
`H`, packaged as a `PositiveLinearMap` over `ℝ`. Real-linear because the inner-product
distributes over `+` and the ℝ-smul on `H` is defeq to the ℂ-smul via `Module.compHom` (the
`change` step in `map_smul'`); Loewner-monotone via `IsPositive.re_inner_nonneg_right` on the
difference `N - M`.

Consumed by `LiebTensor.concaveAt_inner_mapL` (specializing `H := E ⊗[ℂ] F`) to lift γ.1c's
tensor-form Lieb T1 to the v-form. More generally, this is the real part of the vector-state
functional `M ↦ ⟨v, M v⟩`, fundamental in operator-theoretic concavity arguments. -/
noncomputable def innerSelfFunctional {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : H) : (H →L[ℂ] H) →ₚ[ℝ] ℝ where
  toFun M := RCLike.re ⟪v, M v⟫_ℂ
  map_add' M N := by
    rw [_root_.add_apply, inner_add_right, map_add]
  map_smul' c M := by
    -- ℝ-smul on `H` is defeq to ℂ-smul via `(c : ℂ)`-cast (`Module.compHom`).
    -- `change` bridges so `inner_smul_right` (ℂ-form) fires; `simp [smul_eq_mul]`
    -- collapses `↑c * z` and `c • re z` to the common form.
    change RCLike.re ⟪v, ((c : ℂ) • M v : H)⟫_ℂ = c • RCLike.re ⟪v, M v⟫_ℂ
    rw [inner_smul_right]
    simp [smul_eq_mul]
  monotone' M N hMN := by
    -- `M ≤ N → (N - M).IsPositive → 0 ≤ re ⟨v, (N - M) v⟩ → re ⟨v, M v⟩ ≤ re ⟨v, N v⟩`.
    have h_re := (ContinuousLinearMap.le_def.mp hMN).re_inner_nonneg_right v
    rw [_root_.sub_apply, inner_sub_right, map_sub, sub_nonneg] at h_re
    exact h_re

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

namespace LiebTensor

/-- The joint operator concavity inequality at the exponent pair `(q, r) : ℝ × ℝ`: for any
strictly positive `A₁, A₂ : E →L[ℂ] E` and `B₁, B₂ : F →L[ℂ] F`, and any convex coefficients
`t, s ≥ 0` with `t + s = 1`,

  `t • mapL (A₁^q) (B₁^r) + s • mapL (A₂^q) (B₂^r) ≤ mapL ((t•A₁ + s•A₂)^q) ((t•B₁ + s•B₂)^r)`.

The set `{(q, r) | ConcaveAt q r}` will be shown to equal the Lieb simplex
`{(q, r) | 0 ≤ q, 0 ≤ r, q + r ≤ 1}`. -/
def ConcaveAt (q r : ℝ) : Prop :=
    ∀ {A₁ A₂ : E →L[ℂ] E} (_ : IsStrictlyPositive A₁) (_ : IsStrictlyPositive A₂)
      {B₁ B₂ : F →L[ℂ] F} (_ : IsStrictlyPositive B₁) (_ : IsStrictlyPositive B₂)
      {t s : ℝ} (_ : 0 ≤ t) (_ : 0 ≤ s) (_ : t + s = 1),
      t • TensorProduct.mapL (A₁ ^ q) (B₁ ^ r) + s • TensorProduct.mapL (A₂ ^ q) (B₂ ^ r) ≤
        TensorProduct.mapL ((t • A₁ + s • A₂) ^ q) ((t • B₁ + s • B₂) ^ r)

/-- Base case `(0, 0)`: both sides equal `mapL 1 1`. -/
theorem concaveAt_zero_zero : ConcaveAt (E := E) (F := F) 0 0 := by
  intro A₁ A₂ hA₁ hA₂ B₁ B₂ hB₁ hB₂ t s ht hs hts
  rw [CFC.rpow_zero _ hA₁.nonneg, CFC.rpow_zero _ hA₂.nonneg,
    CFC.rpow_zero _ hB₁.nonneg, CFC.rpow_zero _ hB₂.nonneg,
    CFC.rpow_zero _ (convex_isStrictlyPositive hA₁ hA₂ ht hs hts).nonneg,
    CFC.rpow_zero _ (convex_isStrictlyPositive hB₁ hB₂ ht hs hts).nonneg,
    ← add_smul, hts, one_smul]

/-- Base case `(1, 0)`: both sides equal `mapL (t•A₁ + s•A₂) 1` by `mapL`-bilinearity in the
first argument. The `change` bridges ℝ-smul on the ℂ-CLM to ℂ-smul (defeq via the algebra
tower, but `IsScalarTower ℝ ℂ (E →L[ℂ] E)` isn't auto-synthesized for `mapL_smul_left` to fire
on ℝ-smul; per memory `feedback_smul_coercion_change_workaround`). -/
theorem concaveAt_one_zero : ConcaveAt (E := E) (F := F) 1 0 := by
  intro A₁ A₂ hA₁ hA₂ B₁ B₂ hB₁ hB₂ t s ht hs hts
  refine le_of_eq ?_
  rw [CFC.rpow_one _ hA₁.nonneg, CFC.rpow_one _ hA₂.nonneg,
    CFC.rpow_one _ (convex_isStrictlyPositive hA₁ hA₂ ht hs hts).nonneg,
    CFC.rpow_zero _ hB₁.nonneg, CFC.rpow_zero _ hB₂.nonneg,
    CFC.rpow_zero _ (convex_isStrictlyPositive hB₁ hB₂ ht hs hts).nonneg]
  change (t : ℂ) • TensorProduct.mapL A₁ 1 + (s : ℂ) • TensorProduct.mapL A₂ 1 =
    TensorProduct.mapL ((t : ℂ) • A₁ + (s : ℂ) • A₂) 1
  rw [TensorProduct.mapL_add_left, TensorProduct.mapL_smul_left,
    TensorProduct.mapL_smul_left]

/-- Base case `(0, 1)`: both sides equal `mapL 1 (t•B₁ + s•B₂)` by `mapL`-bilinearity in the
second argument. Mirror of `concaveAt_one_zero`. -/
theorem concaveAt_zero_one : ConcaveAt (E := E) (F := F) 0 1 := by
  intro A₁ A₂ hA₁ hA₂ B₁ B₂ hB₁ hB₂ t s ht hs hts
  refine le_of_eq ?_
  rw [CFC.rpow_zero _ hA₁.nonneg, CFC.rpow_zero _ hA₂.nonneg,
    CFC.rpow_zero _ (convex_isStrictlyPositive hA₁ hA₂ ht hs hts).nonneg,
    CFC.rpow_one _ hB₁.nonneg, CFC.rpow_one _ hB₂.nonneg,
    CFC.rpow_one _ (convex_isStrictlyPositive hB₁ hB₂ ht hs hts).nonneg]
  change (t : ℂ) • TensorProduct.mapL (1 : E →L[ℂ] E) B₁ +
      (s : ℂ) • TensorProduct.mapL (1 : E →L[ℂ] E) B₂ =
    TensorProduct.mapL (1 : E →L[ℂ] E) ((t : ℂ) • B₁ + (s : ℂ) • B₂)
  rw [TensorProduct.mapL_add_right, TensorProduct.mapL_smul_right,
    TensorProduct.mapL_smul_right]

/-- **Midpoint-closure of the joint-concavity property** (Carlen §6.1 key step). If joint
operator concavity of `(A, B) ↦ A^q ⊗ B^r` holds at `(q₁, r₁)` and `(q₂, r₂)`, then it holds
at their midpoint. Chain:
1. Rewrite both sides via the midpoint identity `mapL (X^q) (Y^r) = M₀(mapL X^{q₁} Y^{r₁},
   mapL X^{q₂} Y^{r₂})` (`TensorProduct.mapL_rpow_midpoint_eq_geometricMean`).
2. `geometricMean_concave` (β.4) commutes the convex combination past `M₀`.
3. `geometricMean_mono` invokes the `(q₁, r₁)` and `(q₂, r₂)` concavity hypotheses to bound
   each argument by the convex-combined RHS. -/
theorem concaveAt_midpoint {q₁ r₁ q₂ r₂ : ℝ}
    (h₁ : ConcaveAt (E := E) (F := F) q₁ r₁) (h₂ : ConcaveAt (E := E) (F := F) q₂ r₂) :
    ConcaveAt (E := E) (F := F) ((q₁ + q₂) / 2) ((r₁ + r₂) / 2) := by
  intro A₁ A₂ hA₁ hA₂ B₁ B₂ hB₁ hB₂ t s ht hs hts
  have htA := convex_isStrictlyPositive hA₁ hA₂ ht hs hts
  have htB := convex_isStrictlyPositive hB₁ hB₂ ht hs hts
  -- Strict-positivity shortcut: `mapL (X^q) (Y^r)` strict for `X, Y` strict
  -- (`mapL_isStrictlyPositive` + `IsStrictlyPositive.rpow`, both `@[aesop safe apply]`).
  have hmapL : ∀ {X : E →L[ℂ] E} (_ : IsStrictlyPositive X)
      {Y : F →L[ℂ] F} (_ : IsStrictlyPositive Y) (q r : ℝ),
      IsStrictlyPositive (TensorProduct.mapL (X ^ q) (Y ^ r)) := fun _ _ _ _ ↦ by aesop
  rw [TensorProduct.mapL_rpow_midpoint_eq_geometricMean hA₁ hB₁,
    TensorProduct.mapL_rpow_midpoint_eq_geometricMean hA₂ hB₂,
    TensorProduct.mapL_rpow_midpoint_eq_geometricMean htA htB]
  -- Two-step bound: `geometricMean_concave` (β.4) commutes the convex combo past `M₀`;
  -- then `geometricMean_mono` invokes the `(qᵢ, rᵢ)` concavity on each argument.
  refine le_trans (b := CFC.geometricMean
    (t • TensorProduct.mapL (A₁ ^ q₁) (B₁ ^ r₁) + s • TensorProduct.mapL (A₂ ^ q₁) (B₂ ^ r₁))
    (t • TensorProduct.mapL (A₁ ^ q₂) (B₁ ^ r₂) + s • TensorProduct.mapL (A₂ ^ q₂) (B₂ ^ r₂)))
    ?_ ?_
  · -- Convex-combo commutes past `M₀`: strict-pos at `(q₁, r₁)` for the LHS args,
    -- non-negativity at `(q₂, r₂)` for the RHS args.
    refine CFC.geometricMean_concave ?_ ?_ ?_ ?_ ht hs hts
    · exact hmapL hA₁ hB₁ q₁ r₁
    · exact hmapL hA₂ hB₂ q₁ r₁
    · exact (hmapL hA₁ hB₁ q₂ r₂).nonneg
    · exact (hmapL hA₂ hB₂ q₂ r₂).nonneg
  · -- Monotonicity in each `M₀` argument from `(q₁, r₁)` / `(q₂, r₂)` concavity.
    refine CFC.geometricMean_mono ?_ ?_ ?_ ?_ ?_ ?_
    · -- LHS-arg-1 strict-pos via convex-combo of `(q₁, r₁)`-strict.
      exact convex_isStrictlyPositive (hmapL hA₁ hB₁ q₁ r₁) (hmapL hA₂ hB₂ q₁ r₁) ht hs hts
    · -- RHS-arg-1 strict-pos via `mapL_isStrictlyPositive` on the combined base.
      exact hmapL htA htB q₁ r₁
    · -- LHS-arg-2 nonneg via add+smul of `(q₂, r₂)`-strict.nonneg.
      exact add_nonneg (smul_nonneg ht (hmapL hA₁ hB₁ q₂ r₂).nonneg)
        (smul_nonneg hs (hmapL hA₂ hB₂ q₂ r₂).nonneg)
    · -- RHS-arg-2 nonneg.
      exact (hmapL htA htB q₂ r₂).nonneg
    · -- Arg-1 inequality: invoke `(q₁, r₁)` concavity.
      exact h₁ hA₁ hA₂ hB₁ hB₂ ht hs hts
    · -- Arg-2 inequality: invoke `(q₂, r₂)` concavity.
      exact h₂ hA₁ hA₂ hB₁ hB₂ ht hs hts

/-- **Topological closedness**: the set `{(q, r) | ConcaveAt q r}` is closed in `ℝ × ℝ`.
For each fixed `(A₁, A₂, B₁, B₂, t, s)`, the inequality `LHS(q,r) ≤ RHS(q,r)` defines a closed
set via `isClosed_le` (both sides continuous in `(q, r)` via `Continuous.mapL` +
`CFC.continuous_const_rpow`). Sequential closedness then suffices in the first-countable
space `ℝ × ℝ`. -/
theorem concaveAt_isClosed : IsClosed {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2} := by
  apply IsSeqClosed.isClosed
  intro p_n p hp_in hp_lim A₁ A₂ hA₁ hA₂ B₁ B₂ hB₁ hB₂ t s ht hs hts
  refine le_of_tendsto_of_tendsto' (b := Filter.atTop)
    (h := fun n ↦ hp_in n hA₁ hA₂ hB₁ hB₂ ht hs hts) ?_ ?_
  -- Both sides: `refine Tendsto.comp (g := <outer-fn>) ?_ hp_lim` pins the outer function
  -- explicitly (Lean's eta-unification can't recover it from a bare `?_ ∘ p_n`); then
  -- `Continuous.tendsto _ p` lifts a `Continuous` proof, built via `Continuous.mapL`
  -- and `CFC.continuous_const_rpow`.
  · -- LHS: sum of two `t • mapL (A_i ^ ·) (B_i ^ ·)` summands.
    refine Filter.Tendsto.comp (g := fun pp : ℝ × ℝ ↦
      t • TensorProduct.mapL (A₁ ^ pp.1) (B₁ ^ pp.2) +
        s • TensorProduct.mapL (A₂ ^ pp.1) (B₂ ^ pp.2)) ?_ hp_lim
    apply Continuous.tendsto _ p
    refine Continuous.add ?_ ?_
    · exact (((CFC.continuous_const_rpow hA₁).comp continuous_fst).mapL
        ((CFC.continuous_const_rpow hB₁).comp continuous_snd)).const_smul t
    · exact (((CFC.continuous_const_rpow hA₂).comp continuous_fst).mapL
        ((CFC.continuous_const_rpow hB₂).comp continuous_snd)).const_smul s
  · -- RHS: single `mapL ((t•A₁+s•A₂) ^ ·) ((t•B₁+s•B₂) ^ ·)`.
    refine Filter.Tendsto.comp (g := fun pp : ℝ × ℝ ↦
      TensorProduct.mapL ((t • A₁ + s • A₂) ^ pp.1) ((t • B₁ + s • B₂) ^ pp.2))
      ?_ hp_lim
    apply Continuous.tendsto _ p
    refine Continuous.mapL ?_ ?_
    · exact (CFC.continuous_const_rpow (convex_isStrictlyPositive hA₁ hA₂ ht hs hts)).comp
        continuous_fst
    · exact (CFC.continuous_const_rpow (convex_isStrictlyPositive hB₁ hB₂ ht hs hts)).comp
        continuous_snd

/-- **Sierpinski lift** (γ.0 application): the set `{(q, r) | ConcaveAt q r}` is convex in
`ℝ × ℝ`. Combines `concaveAt_isClosed` + midpoint-closure (`concaveAt_midpoint`) via
`Convex.of_isClosed_of_midpoint_mem`. -/
theorem concaveAt_convex : Convex ℝ {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2} := by
  apply Convex.of_isClosed_of_midpoint_mem concaveAt_isClosed
  intro u hu v hv
  have h_mid : midpoint ℝ u v = ((u.1 + v.1) / 2, (u.2 + v.2) / 2) := by
    ext <;> simp [midpoint, AffineMap.lineMap_apply_module] <;> ring
  rw [h_mid]
  -- Unfold `ConcaveAt` via `intro`, then apply `concaveAt_midpoint` fully expanded.
  intro A₁ A₂ hA₁ hA₂ B₁ B₂ hB₁ hB₂ t s ht hs hts
  exact concaveAt_midpoint hu hv hA₁ hA₂ hB₁ hB₂ ht hs hts

/-- **Lieb's Theorem 1 (tensor form)**: for strictly positive `A_i : E →L[ℂ] E` and
`B_i : F →L[ℂ] F`, the function `(A, B) ↦ A^q ⊗ B^r` is jointly operator-concave whenever
`(q, r)` lies in the Lieb simplex `{(q, r) | 0 ≤ q, 0 ≤ r, q + r ≤ 1}`. Carlen §6.1 / Lieb's
Theorem 1.

Proof: the concavity set is convex (`concaveAt_convex`, via Sierpinski) and contains the three
simplex vertices `(0, 0)`, `(1, 0)`, `(0, 1)` (the base cases). Any `(q, r)` in the simplex
factors as a convex combination of the three vertices. -/
theorem concaveAt_of_mem_simplex {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1) :
    ConcaveAt (E := E) (F := F) q r := by
  -- Two-step convex combination using the three γ.1b base cases. Case-split on `q + r = 0`:
  -- the inner combo needs `q + r > 0` for the normalized weights `q/(q+r)`, `r/(q+r)`. The
  -- three vertex memberships AND the inner-combo result each carry an explicit
  -- `(... ∈ {p | ConcaveAt p.1 p.2})` ascription via separate `have`s. The ascriptions stop
  -- the elaborator from η-expanding the strict-implicit `⦃x ∈ s⦄` binders of `Convex` —
  -- which would propagate metavariables through `ConcaveAt`'s `∀ {A B}` and trigger
  -- weight-arg misalignment. Inlining the vertex haves OR nesting the two combos inline
  -- both reproduce this; the explicit have-stack is the cheapest workaround.
  change ((q, r) : ℝ × ℝ) ∈ {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2}
  by_cases hqr0 : q + r = 0
  · obtain ⟨rfl, rfl⟩ : q = 0 ∧ r = 0 := ⟨by linarith, by linarith⟩
    exact concaveAt_zero_zero
  have hqr_pos : 0 < q + r := lt_of_le_of_ne (by linarith) (Ne.symm hqr0)
  have h_v10 : ((1, 0) : ℝ × ℝ) ∈ {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2} :=
    concaveAt_one_zero
  have h_v01 : ((0, 1) : ℝ × ℝ) ∈ {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2} :=
    concaveAt_zero_one
  have h_v00 : ((0, 0) : ℝ × ℝ) ∈ {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2} :=
    concaveAt_zero_zero
  have h_inner :
      (q / (q + r)) • ((1, 0) : ℝ × ℝ) + (r / (q + r)) • ((0, 1) : ℝ × ℝ) ∈
        {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2} :=
    concaveAt_convex h_v10 h_v01 (div_nonneg hq hqr_pos.le) (div_nonneg hr hqr_pos.le)
      (by rw [← add_div, div_self hqr_pos.ne'])
  have h_outer :
      (q + r) • ((q / (q + r)) • ((1, 0) : ℝ × ℝ) + (r / (q + r)) • ((0, 1) : ℝ × ℝ)) +
        (1 - (q + r)) • ((0, 0) : ℝ × ℝ) ∈
        {p : ℝ × ℝ | ConcaveAt (E := E) (F := F) p.1 p.2} :=
    concaveAt_convex h_inner h_v00 hqr_pos.le (by linarith) (by ring)
  have h_simp : (q + r) • ((q / (q + r)) • ((1, 0) : ℝ × ℝ) + (r / (q + r)) • (0, 1)) +
      (1 - (q + r)) • ((0, 0) : ℝ × ℝ) = (q, r) := by
    ext <;> simp <;> field_simp
  rw [h_simp] at h_outer
  exact h_outer

/-! ## Lieb's Theorem 1, trace-form preliminary (v-form)

The trace-form Lieb T1 — that `(A, B) ↦ Tr(K† A^q K B^r)` is jointly concave — reduces, via
Carlen's Theorem 5.12 (Ando's identity), to the **vector form** `(A, B) ↦ re ⟨v, mapL(A^q, B^r)
v⟩` jointly concave for any fixed `v ∈ E ⊗ F`. The K-version specialization through a
basis-dependent Choi-Jamiolkowski vector + transpose-of-B reconciliation is
`TensorProduct.concaveAt_trace` in `ToMathlib/Analysis/InnerProductSpace/LiebConcavityTrace.lean`.

The reduction from `ConcaveAt` (operator-concavity of `mapL(A^q, B^r)`) to real-valued concavity
is via a **`PositiveLinearMap ℝ`**: a real-linear Loewner-monotone functional `Φ` on the CLM
space carries operator concavity through to real concavity. The v-form is the specialization
`Φ_v M := re ⟨v, M v⟩` = `ContinuousLinearMap.innerSelfFunctional v` (defined above at the
generic Hilbert-space level), which is real-linear (inner-product distributivity) and
Loewner-monotone (`IsPositive.re_inner_nonneg_right`). The bundle matches Mathlib's
`LinearMap.tracePositiveLinearMap` precedent for trace-as-PSD-monotone. -/

/-- **Abstract `ConcaveAt`-via-PSD-functional**: a `PositiveLinearMap` `Φ` over `ℝ` (i.e.
real-linear + Loewner-monotone) carries the operator-concavity inequality of `ConcaveAt q r`
through to a real-concavity inequality on the values `Φ (mapL (Aᵢ^q) (Bᵢ^r))`.

This is the bridge from γ.1c's tensor-form Lieb T1 (operator-concavity of
`(A, B) ↦ mapL(A^q, B^r)`) to scalar-concavity statements via Φ. Bundling
`LinearMap` + `Monotone` as a single `PositiveLinearMap` matches Mathlib's
`LinearMap.tracePositiveLinearMap` precedent for trace-as-PSD-monotone. -/
theorem ConcaveAt.concave_via_PSDFunctional {q r : ℝ} (hqr : ConcaveAt (E := E) (F := F) q r)
    (Φ : (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) →ₚ[ℝ] ℝ)
    {A₁ A₂ : E →L[ℂ] E} (hA₁ : IsStrictlyPositive A₁) (hA₂ : IsStrictlyPositive A₂)
    {B₁ B₂ : F →L[ℂ] F} (hB₁ : IsStrictlyPositive B₁) (hB₂ : IsStrictlyPositive B₂)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    t • Φ (TensorProduct.mapL (A₁ ^ q) (B₁ ^ r)) +
        s • Φ (TensorProduct.mapL (A₂ ^ q) (B₂ ^ r)) ≤
      Φ (TensorProduct.mapL ((t • A₁ + s • A₂) ^ q) ((t • B₁ + s • B₂) ^ r)) := by
  rw [← map_smul Φ, ← map_smul Φ, ← map_add Φ]
  exact Φ.monotone' (hqr hA₁ hA₂ hB₁ hB₂ ht hs hts)

/-- **v-form Lieb T1**: for any fixed `v : E ⊗ F` and `(q, r)` in the Lieb simplex
`{(q, r) | 0 ≤ q, 0 ≤ r, q + r ≤ 1}`, the real-valued function
`(A, B) ↦ re ⟨v, mapL (A^q) (B^r) v⟩`
is jointly concave on strictly positive `A : E →L[ℂ] E`, `B : F →L[ℂ] F`.

The functional `M ↦ re ⟨v, M v⟩` is real-linear (inner-product distributivity) and
Loewner-monotone (`ContinuousLinearMap.IsPositive.re_inner_nonneg_right` on `N - M`); the
proof composes this with `ConcaveAt.concave_via_PSDFunctional` and γ.1c's
`concaveAt_of_mem_simplex`.

This is the operator-concavity-to-scalar-concavity bridge used to derive Carlen's trace-form
Lieb T1 (Theorem 5.12 + §6.1). The full Carlen statement `(A, B) ↦ re Tr(K† A^q K B^r)` for
arbitrary `K : F →L[ℂ] E` follows via `v := choiVec K` for a basis-dependent Choi-Jamiolkowski
vector (not done here). -/
theorem concaveAt_inner_mapL (v : E ⊗[ℂ] F) {q r : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1)
    {A₁ A₂ : E →L[ℂ] E} (hA₁ : IsStrictlyPositive A₁) (hA₂ : IsStrictlyPositive A₂)
    {B₁ B₂ : F →L[ℂ] F} (hB₁ : IsStrictlyPositive B₁) (hB₂ : IsStrictlyPositive B₂)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    t • RCLike.re ⟪v, TensorProduct.mapL (A₁ ^ q) (B₁ ^ r) v⟫_ℂ +
        s • RCLike.re ⟪v, TensorProduct.mapL (A₂ ^ q) (B₂ ^ r) v⟫_ℂ ≤
      RCLike.re ⟪v,
        TensorProduct.mapL ((t • A₁ + s • A₂) ^ q) ((t • B₁ + s • B₂) ^ r) v⟫_ℂ :=
  -- Apply `ConcaveAt.concave_via_PSDFunctional` with the bundled `innerSelfFunctional v`. FQN
  -- form (not dot notation) avoids η-expansion of `ConcaveAt`'s `∀ {A B}` implicit binders.
  ConcaveAt.concave_via_PSDFunctional (concaveAt_of_mem_simplex hq hr hqr)
    (innerSelfFunctional v) hA₁ hA₂ hB₁ hB₂ ht hs hts

end LiebTensor

end ContinuousLinearMap
