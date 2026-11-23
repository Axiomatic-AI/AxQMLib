/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.PartialTrace
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyConvexNonfaithful
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyMonotone
import ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality

/-!
# AxQM — quantum relative entropy of two states

The **quantum relative entropy** (Umegaki relative entropy) of a state `ρ` with respect to a state
`σ` (Nielsen–Chuang §11.3.1, eq. (11.55)) is

`S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)`,

the quantum generalization of the classical Kullback–Leibler divergence. It is the central tool of
Nielsen–Chuang §11.3: **Klein's inequality** (Theorem 11.7) `S(ρ ‖ σ) ≥ 0` is the source of
essentially every entropy inequality in the chapter (subadditivity, concavity, and — through the
convexity of the relative entropy and its monotonicity under partial trace — strong subadditivity).

This file defines the relative entropy `State.quantumRelativeEntropy` of states, from the operator
`ContinuousLinearMap.quantumRelativeEntropy` of their density operators, together with the two
halves of Klein's inequality: non-negativity `State.quantumRelativeEntropy_nonneg` and the equality
condition `State.quantumRelativeEntropy_eq_zero_iff`.

## The finite branch (support condition), and faithfulness

Klein's inequality is `S(ρ ‖ σ) ≥ 0`; N&C defines `S(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ` and finite
otherwise. The definition here is the real-valued, finite quantity (`cfc Real.log` sends the zero
eigenvalues of a rank-deficient `σ` to `0` rather than `−∞`), so its natural domain is exactly N&C's
"finite otherwise" branch: the **support condition** `supp ρ ⊆ supp σ`, i.e.
`ρ.op.HasSupportLE σ.op` (`ker σ.op ≤ ker ρ.op`). On that branch Klein's inequality holds in full —
`S(ρ ‖ σ) ≥ 0`, with equality iff `ρ = σ` — with *no* restriction on `σ`'s rank; this is the
faithful statement (`State.quantumRelativeEntropy_nonneg_of_hasSupportLE` and
`…_eq_zero_iff_of_hasSupportLE`), lifting the support-condition lemmas
`ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_{nonneg,eq_zero_iff}_of_hasSupportLE`.

Requiring `σ` **faithful** — every eigenvalue of `σ.op` strictly positive, i.e. `σ` full rank —
is the strictly stronger special case `ker σ.op = ⊥` (a faithful `σ` dominates the support of every
`ρ`); it *narrows* the finite branch (dropping pairs with both `ρ, σ` rank-deficient) and so the
faithful forms `State.quantumRelativeEntropy_nonneg` / `…_eq_zero_iff` are kept only as convenience
corollaries for callers that already carry a strictly positive reference state.

## Main definitions

* `AxQM.State.quantumRelativeEntropy` — the relative entropy `S(ρ ‖ σ)` of states `ρ, σ`.

## Main results

* `AxQM.State.quantumRelativeEntropy_self_eq_zero` — `S(ρ ‖ ρ) = 0`.
* `AxQM.State.quantumRelativeEntropy_nonneg_of_hasSupportLE` — **Klein's inequality** (N&C
  Theorem 11.7), the faithful finite-branch form: `S(ρ ‖ σ) ≥ 0` whenever `supp ρ ⊆ supp σ`
  (`ρ.op.HasSupportLE σ.op`), no faithfulness of `σ`.
* `AxQM.State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE` — **Klein's inequality,
  equality condition** (N&C Theorem 11.7): for `supp ρ ⊆ supp σ`, `S(ρ ‖ σ) = 0 ↔ ρ = σ`.
* `AxQM.State.quantumRelativeEntropy_nonneg` / `…_eq_zero_iff` — the faithful-`σ`
  (`ker σ.op = ⊥`) special cases, kept as convenience corollaries.
* `AxQM.State.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub` — the bridge
  `S(ρ ‖ σ) = −S(ρ) − re tr(ρ log σ)` relating the relative entropy to the von Neumann entropy.
* `AxQM.State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE` — **joint
  convexity of the relative entropy** (N&C Theorem 11.12), the faithful finite-branch form: the
  `n`-ary `S(∑ wₖ ρₖ ‖ ∑ wₖ σₖ) ≤ ∑ wₖ S(ρₖ‖σₖ)` under only the **support condition**
  `(ρₖ).op.HasSupportLE (σₖ).op` on each component — no faithfulness (rank-deficient states
  allowed).
* `AxQM.State.quantumRelativeEntropy_jointly_convex_of_hasSupportLE` — its **two-point
  form** `S(t ρ₁+s ρ₂ ‖ t σ₁+s σ₂) ≤ t S(ρ₁‖σ₁)+s S(ρ₂‖σ₂)`, N&C's literal statement.
* `AxQM.State.quantumRelativeEntropy_jointly_convex_sum` / `…_jointly_convex` — the
  faithful-constituent (`IsStrictlyPositive`) special cases, kept as convenience corollaries; the
  `n`-ary form is the one used in the strong-subadditivity argument.
* `AxQM.State.quantumRelativeEntropy_reduced_le_of_hasSupportLE` — **monotonicity under the
  partial trace** (N&C Theorem 11.17), the **faithful finite-branch form**: tracing out the right
  subsystem cannot increase the relative entropy, `S(ρ_A ‖ σ_A) ≤ S(ρ_AB ‖ σ_AB)`, under only the
  **support condition** `ρ.op.HasSupportLE σ.op` — no faithfulness (rank-deficient states allowed);
  the bridge to strong subadditivity (N&C Theorem 11.14).
* `AxQM.State.quantumRelativeEntropy_reduced_le` — the faithful-states
  (`IsStrictlyPositive`) special case, kept as a convenience corollary.
-/

namespace AxQM

variable {S : QSystem}

/-- The **quantum relative entropy** `S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)` of a state `ρ` with
respect to a state `σ` (Nielsen–Chuang §11.3.1, eq. (11.55)). It is
`ContinuousLinearMap.quantumRelativeEntropy` of the density operators. -/
noncomputable def State.quantumRelativeEntropy (ρ σ : State S) : ℝ :=
  ρ.op.quantumRelativeEntropy σ.op

/-- The `_def` bridge: the states' relative entropy is the operator relative entropy of their
density operators. Holds definitionally; provided so proofs can rewrite
between `State.quantumRelativeEntropy` and `ContinuousLinearMap.quantumRelativeEntropy`. -/
theorem State.quantumRelativeEntropy_def (ρ σ : State S) :
    ρ.quantumRelativeEntropy σ = ρ.op.quantumRelativeEntropy σ.op :=
  rfl

/-- **The relative entropy of a state with itself vanishes**: `S(ρ ‖ ρ) = 0`. Immediate from the
`tr(ρ log ρ) − tr(ρ log ρ)` shape of the definition (no faithfulness needed). -/
@[simp] theorem State.quantumRelativeEntropy_self_eq_zero (ρ : State S) :
    ρ.quantumRelativeEntropy ρ = 0 :=
  ContinuousLinearMap.quantumRelativeEntropy_self ρ.op

/-- **Klein's inequality** (Nielsen–Chuang Theorem 11.7), on the finite branch. The quantum relative
entropy of two states is non-negative, `S(ρ ‖ σ) ≥ 0`, whenever the **support condition**
`supp ρ ⊆ supp σ` holds — `ρ.op.HasSupportLE σ.op`, i.e. `ker σ.op ≤ ker ρ.op` — with **no
faithfulness of `σ` required**.

This is N&C's theorem stated on exactly the branch where the relative entropy is finite: N&C define
`S(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ` and finite otherwise, and the support condition
`ρ.op.HasSupportLE σ.op` is precisely that "finite otherwise" clause — the natural domain of the
real-valued quantity, not an added hypothesis narrowing the claim. It is therefore the faithful
statement of Klein's inequality; the faithful-`σ` form `State.quantumRelativeEntropy_nonneg` below
is the special case `ker σ.op = ⊥`, which genuinely *narrows* the theorem (it excludes finite-branch
pairs with both `ρ, σ` rank-deficient), so it is only a convenience corollary.

Lifts the operator inequality
`ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg_of_hasSupportLE` through the `_def`
bridge. -/
theorem State.quantumRelativeEntropy_nonneg_of_hasSupportLE (ρ σ : State S)
    (h : ρ.op.HasSupportLE σ.op) : 0 ≤ ρ.quantumRelativeEntropy σ :=
  ρ.isDensity.quantumRelativeEntropy_nonneg_of_hasSupportLE σ.isDensity h

/-- **Klein's inequality, equality condition** (Nielsen–Chuang Theorem 11.7), on the finite branch.
For states satisfying the **support condition** `supp ρ ⊆ supp σ` (`ρ.op.HasSupportLE σ.op`, i.e.
`ker σ.op ≤ ker ρ.op`), the quantum relative entropy vanishes iff the states coincide,
`S(ρ ‖ σ) = 0 ↔ ρ = σ` — with **no faithfulness of `σ` required**. Together with
`State.quantumRelativeEntropy_nonneg_of_hasSupportLE` this is the full content of Klein's inequality
on the finite branch: `S(ρ ‖ σ) ≥ 0`, with equality exactly when `ρ = σ`.

The faithful statement of the equality condition (see
`State.quantumRelativeEntropy_nonneg_of_hasSupportLE` for why the support condition — N&C's own
"finite otherwise" branch — is the right hypothesis and not a weakening); the faithful-`σ` form
`State.quantumRelativeEntropy_eq_zero_iff` below is the special case `ker σ.op = ⊥`.

Lifts the operator equality condition
`ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE` through the
`_def` bridge and `State.ext` (a state is determined by its density operator `.op`). -/
theorem State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE (ρ σ : State S)
    (h : ρ.op.HasSupportLE σ.op) : ρ.quantumRelativeEntropy σ = 0 ↔ ρ = σ := by
  rw [State.quantumRelativeEntropy_def,
    ρ.isDensity.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE σ.isDensity h]
  exact ⟨fun hop => State.ext hop, fun hst => by rw [hst]⟩

/-- **Klein's inequality for a faithful `σ`** (Nielsen–Chuang Theorem 11.7): the quantum relative
entropy of two states is non-negative, `S(ρ ‖ σ) ≥ 0`, provided `σ` is **faithful** (all eigenvalues
of `σ.op` strictly positive). The `ker σ.op = ⊥` special case of the general finite-branch statement
`State.quantumRelativeEntropy_nonneg_of_hasSupportLE` (a faithful `σ` dominates the support of every
`ρ`); retained as a convenience corollary for the many callers that already work with a strictly
positive reference state. Grounds the operator Klein–Gibbs inequality
`ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg`. -/
theorem State.quantumRelativeEntropy_nonneg (ρ σ : State S)
    (hσ_pos : ∀ j, 0 < σ.isDensity.isSymmetric.eigenvalues rfl j) :
    0 ≤ ρ.quantumRelativeEntropy σ :=
  ρ.isDensity.quantumRelativeEntropy_nonneg σ.isDensity hσ_pos

/-- **Klein's inequality equality condition, for a faithful `σ`** (Nielsen–Chuang Theorem 11.7): for
a **faithful** state `σ` (all eigenvalues of `σ.op` strictly positive), the quantum relative entropy
vanishes iff the states coincide, `S(ρ ‖ σ) = 0 ↔ ρ = σ`. The `ker σ.op = ⊥` special case of the
general finite-branch statement `State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE`; retained
as a convenience corollary. Together with `State.quantumRelativeEntropy_nonneg` this is the full
content of Klein's inequality for a faithful reference: `S(ρ ‖ σ) ≥ 0`, with equality exactly when
`ρ = σ`.

Lifts the operator equality condition
`ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_eq_zero_iff` to states: the
`_def` bridge turns the equation into the operator one `S(ρ.op ‖ σ.op) = 0 ↔ ρ.op = σ.op`,
and `State.ext_iff` (a state is determined by its density operator `.op`, the remaining field being
a proof) equates operator equality `ρ.op = σ.op` with state equality `ρ = σ`. Only `σ` need be
faithful; `ρ` may be rank-deficient. -/
theorem State.quantumRelativeEntropy_eq_zero_iff (ρ σ : State S)
    (hσ_pos : ∀ j, 0 < σ.isDensity.isSymmetric.eigenvalues rfl j) :
    ρ.quantumRelativeEntropy σ = 0 ↔ ρ = σ := by
  rw [State.quantumRelativeEntropy_def,
    ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_eq_zero_iff ρ.isDensity σ.isDensity
      hσ_pos]
  exact State.ext_iff.symm

/-- **Relative entropy in terms of the von Neumann entropy**:
`S(ρ ‖ σ) = −S(ρ) − re tr(ρ log σ)`, for any states `ρ, σ` (no faithfulness needed). Lifts
`ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub`; the
form in which the relative entropy enters the entropy inequalities (e.g. subadditivity
`S(A:B) = S(ρ_AB ‖ ρ_A ⊗ ρ_B)`). -/
theorem State.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub (ρ σ : State S) :
    ρ.quantumRelativeEntropy σ = -ρ.vonNeumannEntropy -
      RCLike.re (LinearMap.trace ℂ S.space ((cfc Real.log σ.op).toLinearMap ∘ₗ ρ.op.toLinearMap)) :=
  ρ.isDensity.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub

/-- **Joint convexity of the quantum relative entropy, `n`-ary form** (Nielsen–Chuang
Theorem 11.12), the **faithful finite-branch statement**: for families of states
`ρs, σs : κ → State S` and convex weights `w` (`w k ≥ 0`, `∑ w k = 1`) with the **support
condition** `(ρs k).op.HasSupportLE (σs k).op` (`ker (σs k).op ≤ ker (ρs k).op`) on every
component, if the mixed states `ρ, σ` are the convex combinations `ρ = ∑ₖ wₖ ρsₖ` and
`σ = ∑ₖ wₖ σsₖ` of the density
operators, then `S(ρ ‖ σ) ≤ ∑ₖ wₖ S(ρsₖ ‖ σsₖ)`.

This is N&C's theorem stated on exactly the branch where the relative entropy is finite — N&C's
`S(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ`, finite otherwise — with **no faithfulness (strict
positivity) required**; rank-deficient constituents are allowed. The support condition is precisely
that "finite otherwise" clause, the natural domain of the real-valued quantity (`cfc Real.log`
sends the zero eigenvalues of a rank-deficient operator to `0` rather than `−∞`), not a hypothesis
narrowing the claim. The `IsStrictlyPositive` form `State.quantumRelativeEntropy_jointly_convex_sum`
below is the strictly stronger special case (`ker (σs k).op = ⊥`), which excludes rank-deficient
pairs and so is only a convenience corollary.

Lifts `ContinuousLinearMap.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE`
(Lindblad's theorem with faithfulness removed by the `ε → 0⁺` perturbation-and-limit argument,
itself built on Lieb's theorem, N&C Theorem 11.11) to states. The two positivity hypotheses
the operator inequality needs hold for any state (`isDensity.isPositive`); only the
support condition is a genuine hypothesis. The convex combination is supplied through the
`ρ.op = ∑ …` / `σ.op = ∑ …` hypotheses because `State` has no mixing operation.
This is the form used in the strong-subadditivity argument (N&C Theorem 11.14): monotonicity of the
relative entropy under partial trace averages a twirl over a unitary 1-design, a convex combination
of unitary conjugates.

That inequality lives on an abstract finite-dimensional complex inner product space but needs
the real–complex scalar tower on the operator algebra; it is not a global instance for the space of
a `QSystem`, so it is supplied here via `NormedSpace.complexToReal`. -/
theorem State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE
    {κ : Type*} (u : Finset κ) (ρ σ : State S) (ρs σs : κ → State S) (w : κ → ℝ)
    (hsupp : ∀ k ∈ u, (ρs k).op.HasSupportLE (σs k).op)
    (hw₀ : ∀ k ∈ u, 0 ≤ w k) (hw₁ : ∑ k ∈ u, w k = 1)
    (hρ : ρ.op = ∑ k ∈ u, w k • (ρs k).op)
    (hσ : σ.op = ∑ k ∈ u, w k • (σs k).op) :
    ρ.quantumRelativeEntropy σ ≤ ∑ k ∈ u, w k * (ρs k).quantumRelativeEntropy (σs k) := by
  have : NormedSpace ℝ (S.space →L[ℂ] S.space) := NormedSpace.complexToReal
  have : IsScalarTower ℝ ℂ (S.space →L[ℂ] S.space) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  simp only [State.quantumRelativeEntropy_def]
  rw [hρ, hσ]
  exact ContinuousLinearMap.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE u
    (fun k _ => (ρs k).isDensity.isPositive) (fun k _ => (σs k).isDensity.isPositive)
    hsupp hw₀ hw₁

/-- **Joint convexity of the quantum relative entropy, two-point form** (Nielsen–Chuang
Theorem 11.12), the **faithful finite-branch statement** and N&C's literal two-point claim: for
states with the **support conditions** `ρ₁.op.HasSupportLE σ₁.op` and `ρ₂.op.HasSupportLE σ₂.op` and
probabilities `t, s ≥ 0`, `t + s = 1`, if `ρ = t ρ₁ + s ρ₂` and `σ = t σ₁ + s σ₂` (as density
operators), then `S(ρ ‖ σ) ≤ t · S(ρ₁ ‖ σ₁) + s · S(ρ₂ ‖ σ₂)`.

The two-point specialization of `State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE`
over a two-element (`Fin 2`) index. **No strict positivity is required** — only the support
condition, N&C's "finite otherwise" branch; the `IsStrictlyPositive` form
`State.quantumRelativeEntropy_jointly_convex` below is a convenience corollary. -/
theorem State.quantumRelativeEntropy_jointly_convex_of_hasSupportLE
    (ρ σ ρ₁ ρ₂ σ₁ σ₂ : State S)
    (hs₁ : ρ₁.op.HasSupportLE σ₁.op) (hs₂ : ρ₂.op.HasSupportLE σ₂.op)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1)
    (hρ : ρ.op = t • ρ₁.op + s • ρ₂.op)
    (hσ : σ.op = t • σ₁.op + s • σ₂.op) :
    ρ.quantumRelativeEntropy σ ≤
      t * ρ₁.quantumRelativeEntropy σ₁ + s * ρ₂.quantumRelativeEntropy σ₂ := by
  have key := State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE
    (Finset.univ : Finset (Fin 2)) ρ σ ![ρ₁, ρ₂] ![σ₁, σ₂] ![t, s]
    (by intro k _; fin_cases k <;> simpa)
    (by intro k _; fin_cases k <;> simpa)
    (by simp [Fin.sum_univ_two, hts])
    (by rw [hρ]; simp [Fin.sum_univ_two])
    (by rw [hσ]; simp [Fin.sum_univ_two])
  simpa [Fin.sum_univ_two] using key

/-- **Joint convexity for faithful constituents, `n`-ary form** (Nielsen–Chuang Theorem 11.12): the
`IsStrictlyPositive` (full-rank) special case of the faithful finite-branch statement
`State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE`. When every `ρsₖ, σsₖ` is faithful
(strictly positive spectrum), each support condition `(ρs k).op.HasSupportLE (σs k).op` holds
unconditionally (`ker (σs k).op = ⊥`), so the general statement specializes to
`S(∑ₖ wₖ ρsₖ ‖ ∑ₖ wₖ σsₖ) ≤ ∑ₖ wₖ S(ρsₖ ‖ σsₖ)`.

Requiring strict positivity *narrows* the theorem (it excludes rank-deficient constituents that the
support condition admits), so this is only a convenience corollary; it is retained because it is the
form used in the strong-subadditivity argument (N&C Theorem 11.14), whose twirl constituents are
faithful. It lifts the strict-positivity operator inequality
`ContinuousLinearMap.quantumRelativeEntropy_jointly_convex_sum`. -/
theorem State.quantumRelativeEntropy_jointly_convex_sum
    {κ : Type*} (u : Finset κ) (ρ σ : State S) (ρs σs : κ → State S) (w : κ → ℝ)
    (hρs : ∀ k ∈ u, IsStrictlyPositive (ρs k).op)
    (hσs : ∀ k ∈ u, IsStrictlyPositive (σs k).op)
    (hw₀ : ∀ k ∈ u, 0 ≤ w k) (hw₁ : ∑ k ∈ u, w k = 1)
    (hρ : ρ.op = ∑ k ∈ u, w k • (ρs k).op)
    (hσ : σ.op = ∑ k ∈ u, w k • (σs k).op) :
    ρ.quantumRelativeEntropy σ ≤ ∑ k ∈ u, w k * (ρs k).quantumRelativeEntropy (σs k) := by
  have : NormedSpace ℝ (S.space →L[ℂ] S.space) := NormedSpace.complexToReal
  have : IsScalarTower ℝ ℂ (S.space →L[ℂ] S.space) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  simp only [State.quantumRelativeEntropy_def]
  rw [hρ, hσ]
  exact ContinuousLinearMap.quantumRelativeEntropy_jointly_convex_sum u hρs hσs hw₀ hw₁

/-- **Joint convexity for faithful constituents, two-point form** (Nielsen–Chuang Theorem 11.12):
the `IsStrictlyPositive` (full-rank) special case of the faithful two-point statement
`State.quantumRelativeEntropy_jointly_convex_of_hasSupportLE`. For probabilities `t, s ≥ 0` with
`t + s = 1` and **faithful** states `ρ₁, ρ₂, σ₁, σ₂` whose density operators satisfy
`ρ = t ρ₁ + s ρ₂` and `σ = t σ₁ + s σ₂`, `S(ρ ‖ σ) ≤ t · S(ρ₁ ‖ σ₁) + s · S(ρ₂ ‖ σ₂)`.

Requiring strict positivity narrows the finite-branch two-point statement (each faithful pair
satisfies the support condition unconditionally, `ker σᵢ.op = ⊥`), so this is only a convenience
corollary, kept for callers already working with strictly positive states; obtained from the `n`-ary
`State.quantumRelativeEntropy_jointly_convex_sum` over a two-element index. -/
theorem State.quantumRelativeEntropy_jointly_convex
    (ρ σ ρ₁ ρ₂ σ₁ σ₂ : State S)
    (hρ₁ : IsStrictlyPositive ρ₁.op) (hρ₂ : IsStrictlyPositive ρ₂.op)
    (hσ₁ : IsStrictlyPositive σ₁.op) (hσ₂ : IsStrictlyPositive σ₂.op)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1)
    (hρ : ρ.op = t • ρ₁.op + s • ρ₂.op)
    (hσ : σ.op = t • σ₁.op + s • σ₂.op) :
    ρ.quantumRelativeEntropy σ ≤
      t * ρ₁.quantumRelativeEntropy σ₁ + s * ρ₂.quantumRelativeEntropy σ₂ := by
  have key := State.quantumRelativeEntropy_jointly_convex_sum
    (Finset.univ : Finset (Fin 2)) ρ σ ![ρ₁, ρ₂] ![σ₁, σ₂] ![t, s]
    (by intro k _; fin_cases k <;> simpa)
    (by intro k _; fin_cases k <;> simpa)
    (by intro k _; fin_cases k <;> simpa)
    (by simp [Fin.sum_univ_two, hts])
    (by rw [hρ]; simp [Fin.sum_univ_two])
    (by rw [hσ]; simp [Fin.sum_univ_two])
  simpa [Fin.sum_univ_two] using key

/-- **Monotonicity of the quantum relative entropy under the partial trace, on the support
condition** (Nielsen–Chuang Theorem 11.17), the **faithful finite-branch statement**. Tracing out
the right subsystem cannot increase the relative entropy,

`S(ρ_A ‖ σ_A) ≤ S(ρ_AB ‖ σ_AB)`,

where `ρ_A = Tr_T ρ = ρ.reducedLeft` (and likewise for `σ`), whenever the **support condition**
`supp ρ ⊆ supp σ` holds — `ρ.op.HasSupportLE σ.op` (`ker σ.op ≤ ker ρ.op`) — with **no faithfulness
(strict positivity) of either state required**.

This is N&C's theorem stated on exactly the branch where the relative entropy is finite: N&C define
`S(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ` and finite otherwise, and the support condition
`ρ.op.HasSupportLE σ.op` is precisely that "finite otherwise" clause — the natural domain of the
real-valued quantity (`cfc Real.log` sends the zero eigenvalues of a rank-deficient operator to `0`
rather than `−∞`), not a hypothesis narrowing the claim. Rank-deficient `ρ, σ` are admitted; the
marginal support condition `supp ρ_A ⊆ supp σ_A` needed for the left-hand side descends from the
joint one automatically inside the operator-level proof. The `IsStrictlyPositive` form
`State.quantumRelativeEntropy_reduced_le` below is the strictly stronger special case
(`ker σ.op = ⊥`, both states full rank), so it is only a convenience corollary.

Lifts `ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le_of_hasSupportLE`
to states through `State.reducedLeft`. The two positivity hypotheses the operator
inequality needs hold for any state (`isDensity.isPositive`); only the support
condition is a genuine hypothesis. Following N&C's proof, the completely depolarizing partial-trace
channel `τ ↦ (Tr_T τ) ⊗ I/d` is exhibited as a uniform mixed-unitary average over a unitary
`1`-design (N&C Ex 11.19) and fed into the mixed-unitary data-processing inequality, whose engine is
the **support-condition joint convexity** (N&C Theorem 11.12); the maximally mixed `I/d` factor is
cancelled by the common-right-factor tensor split, and faithfulness is removed throughout by the
`ε → 0⁺` identity-shift perturbation. The nontriviality of the traced-out factor `T.space` — needed
so `I/d` is a genuine density operator — is furnished by the reduced state
`ρ.reducedRight : State T`.
This is the monotonicity that, applied to a mutual-information relative entropy, yields the strong
subadditivity of the von Neumann entropy (N&C Theorem 11.14). -/
theorem State.quantumRelativeEntropy_reduced_le_of_hasSupportLE {S T : QSystem}
    (ρ σ : State (S.compose T)) (hsupp : ρ.op.HasSupportLE σ.op) :
    ρ.reducedLeft.quantumRelativeEntropy σ.reducedLeft ≤ ρ.quantumRelativeEntropy σ := by
  have : Nontrivial T.space := ρ.reducedRight.nontrivial_space
  have : Nonempty (Fin (Module.finrank ℂ T.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  simp only [State.quantumRelativeEntropy_def, State.reducedLeft_op]
  exact ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le_of_hasSupportLE
    (stdOrthonormalBasis ℂ T.space) ρ.isDensity.isPositive σ.isDensity.isPositive hsupp

/-- **Monotonicity of the quantum relative entropy under the partial trace, for faithful states**
(Nielsen–Chuang Theorem 11.17): the `IsStrictlyPositive` (full-rank) special case of the faithful
finite-branch statement `State.quantumRelativeEntropy_reduced_le_of_hasSupportLE`. For faithful
states `ρ, σ` (strictly positive spectrum) the support condition `ρ.op.HasSupportLE σ.op` holds
unconditionally (`ker σ.op = ⊥`), so tracing out the right subsystem cannot increase the relative
entropy, `S(ρ_A ‖ σ_A) ≤ S(ρ_AB ‖ σ_AB)`, where `ρ_A = Tr_T ρ = ρ.reducedLeft`.

Requiring strict positivity *narrows* the theorem (it excludes rank-deficient states the support
condition admits), so this is only a convenience corollary; it is retained for callers already
working with strictly positive states (e.g. the strong-subadditivity argument, N&C Theorem 11.14,
whose twirl constituents are faithful). It lifts the density-operator inequality
`ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le`, whose strict-positivity engine is
the special case where both operators are full-rank. -/
theorem State.quantumRelativeEntropy_reduced_le {S T : QSystem}
    (ρ σ : State (S.compose T))
    (hρ : IsStrictlyPositive ρ.op) (hσ : IsStrictlyPositive σ.op) :
    ρ.reducedLeft.quantumRelativeEntropy σ.reducedLeft ≤ ρ.quantumRelativeEntropy σ := by
  have : Nontrivial T.space := ρ.reducedRight.nontrivial_space
  have : Nonempty (Fin (Module.finrank ℂ T.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  simp only [State.quantumRelativeEntropy_def, State.reducedLeft_op]
  exact ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le
    (stdOrthonormalBasis ℂ T.space) ρ.isDensity σ.isDensity hρ hσ

end AxQM
