/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativeEntropy
import AxQM.Postulates.API.Mixture
import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropyMixture

/-!
# AxQM — concavity of the von Neumann entropy and its equality condition

The von Neumann entropy is a **concave** function of its input (Nielsen & Chuang,
*Quantum Computation and Quantum Information*, §11.3.5, eq. (11.79)): for a probability
distribution `p` and a family of states `ρ : ι → State S`,

`∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`,

and, moreover, the entropy is *strictly* concave — equality holds iff all the `ρᵢ` with `pᵢ > 0`
coincide (N&C **Exercise 11.18**). Both facts flow from a single algebraic identity relating the
concavity gap to the average relative entropy of the components to the mixture,

`S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ) = ∑ᵢ pᵢ S(ρᵢ ‖ ∑ⱼ pⱼ ρⱼ)`,        (†)

which is the `State`-level form of the operator identity
`ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix`. Klein's inequality
(`State.quantumRelativeEntropy_nonneg`, `S(ρ ‖ σ) ≥ 0`) makes the right-hand side non-negative,
giving concavity; its equality condition (`State.quantumRelativeEntropy_eq_zero_iff`,
`S(ρ ‖ σ) = 0 ↔ ρ = σ`) turns the vanishing of the gap into the component-equality condition.

This is a cleaner route than N&C's own proof (which derives concavity from subadditivity via an
auxiliary system `B` and reads the equality condition off the subadditivity equality condition
`ρ_AB = ρ_A ⊗ ρ_B`): identity (†) is exactly the relative-entropy content of that argument,
already proved for operators in `ToMathlib`.

## Faithfulness

Klein's inequality and its equality condition hold, in the finite real-valued branch of this
library, only for a **faithful** second argument — every eigenvalue of `σ.op` strictly positive
(`IsStrictlyPositive`; see `AxQM/Postulates/API/RelativeEntropy.lean` for why finiteness
forces this). Here the second argument is the mixture `μ = ∑ᵢ pᵢ ρᵢ`, so the concavity inequality
and its equality condition are stated with the hypothesis `IsStrictlyPositive μ.op` — the mixture
is full rank. This is the weakest faithfulness hypothesis for the argument (it does **not** require
the individual `ρᵢ` to be faithful) and is the finite-branch convention shared with the rest of the
Chapter 11 entropy cluster (Klein's inequality, joint convexity, subadditivity, strong
subadditivity). The mixing **identity** (†) itself needs no faithfulness — it holds for every
family of states.

## Main results

The statement of N&C Exercise 11.18 is in `AxQM/NC/Ch11/Exercise11_18.lean`; the
declarations are here.

* `AxQM.State.sum_mul_quantumRelativeEntropy_mix` — the mixing identity (†).
* `AxQM.State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix` — concavity of the von
  Neumann entropy (N&C eq. (11.79)), `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`, for a faithful mixture.
* `AxQM.State.vonNeumannEntropy_mix_eq_sum_iff` — **Exercise 11.18**: equality holds in the
  concavity inequality iff all the components with positive weight coincide.
* `AxQM.State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'` /
  `AxQM.State.vonNeumannEntropy_mix_eq_sum_iff'` — the **faithfulness-free** forms of the
  concavity inequality and its equality condition (via the support-condition Klein inequality),
  needed for the generally rank-deficient pinched state of Exercise 11.20.
-/

namespace AxQM

variable {S : QSystem}

/-- **The mixing identity for the von Neumann entropy.** The concavity gap of a mixture
`μ = ∑ᵢ pᵢ ρᵢ` equals the average relative entropy of the components to the mixture:

`∑ᵢ pᵢ S(ρᵢ ‖ μ) = S(μ) − ∑ᵢ pᵢ S(ρᵢ)`.

This is the algebraic heart of both the concavity inequality (N&C eq. (11.79)) and its equality
condition (N&C Exercise 11.18); no faithfulness is needed. Lifts the operator identity
`ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix` to states through the `_def` lemmas and
`State.mix_op` (`μ.op = ∑ᵢ (pᵢ : ℂ) • ρᵢ.op`). -/
theorem State.sum_mul_quantumRelativeEntropy_mix {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    ∑ i, p i * (ρ i).quantumRelativeEntropy (State.mix p hp hsum ρ)
      = (State.mix p hp hsum ρ).vonNeumannEntropy - ∑ i, p i * (ρ i).vonNeumannEntropy := by
  simp only [State.quantumRelativeEntropy_def, State.vonNeumannEntropy_def]
  exact ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix
    (fun i => (ρ i).isDensity) p (State.mix p hp hsum ρ).isDensity (State.mix_op p hp hsum ρ)

/-- **Concavity of the von Neumann entropy** (Nielsen & Chuang §11.3.5, eq. (11.79)): for a
probability distribution `p` and a family of states `ρ : ι → State S` whose mixture
`μ = ∑ᵢ pᵢ ρᵢ` is **faithful** (`IsStrictlyPositive μ.op`),

`∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`.

Immediate from the mixing identity `State.sum_mul_quantumRelativeEntropy_mix`: the concavity gap is
the average relative entropy `∑ᵢ pᵢ S(ρᵢ ‖ μ)`, non-negative because each `pᵢ ≥ 0` and each
`S(ρᵢ ‖ μ) ≥ 0` is Klein's inequality (`State.quantumRelativeEntropy_nonneg`) for the faithful
mixture `μ`. See the module docstring for the finite-branch faithfulness convention. -/
theorem State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (hμ : IsStrictlyPositive (State.mix p hp hsum ρ).op) :
    ∑ i, p i * (ρ i).vonNeumannEntropy ≤ (State.mix p hp hsum ρ).vonNeumannEntropy := by
  have hμ_pos : ∀ j, 0 < (State.mix p hp hsum ρ).isDensity.isSymmetric.eigenvalues rfl j :=
    fun j => hμ.eigenvalues_pos _ rfl j
  have hid := State.sum_mul_quantumRelativeEntropy_mix p hp hsum ρ
  have hnn : 0 ≤ ∑ i, p i * (ρ i).quantumRelativeEntropy (State.mix p hp hsum ρ) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hp i) (State.quantumRelativeEntropy_nonneg _ _ hμ_pos)
  linarith [hid, hnn]

/-- **Equality in the concavity inequality — strict concavity of the von Neumann entropy**
(Nielsen & Chuang **Exercise 11.18**): for a probability distribution `p` and a family of states
`ρ : ι → State S` whose mixture `μ = ∑ᵢ pᵢ ρᵢ` is **faithful** (`IsStrictlyPositive μ.op`),
equality holds in the concavity inequality (11.79),

`S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ)`,

**iff all the components carrying positive weight are identical**,
`∀ i j, 0 < pᵢ → 0 < pⱼ → ρᵢ = ρⱼ`. (This is the precise reading of N&C's "all the `ρᵢ`s are the
same": components with `pᵢ = 0` are free, as they do not enter the mixture.)

Proof via the mixing identity `State.sum_mul_quantumRelativeEntropy_mix`: the concavity gap is the
average relative entropy `∑ᵢ pᵢ S(ρᵢ ‖ μ)`, a sum of non-negative terms (Klein's inequality for the
faithful `μ`), so it vanishes iff each `pᵢ S(ρᵢ ‖ μ) = 0`
(`Finset.sum_eq_zero_iff_of_nonneg`). For `pᵢ > 0` this forces `S(ρᵢ ‖ μ) = 0`, i.e. `ρᵢ = μ` by the
equality condition of Klein's inequality (`State.quantumRelativeEntropy_eq_zero_iff`). Hence
equality ⟺ every positive-weight component equals the average `μ` ⟺ all positive-weight components
coincide (the reverse implication computes `μ = ρᵢ` from `μ.op = ∑ⱼ (pⱼ : ℂ) • ρⱼ.op` with the
common value factored out and `∑ⱼ pⱼ = 1`). See the module docstring for the faithfulness
convention. -/
theorem State.vonNeumannEntropy_mix_eq_sum_iff {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (hμ : IsStrictlyPositive (State.mix p hp hsum ρ).op) :
    (State.mix p hp hsum ρ).vonNeumannEntropy = ∑ i, p i * (ρ i).vonNeumannEntropy
      ↔ ∀ i j, 0 < p i → 0 < p j → ρ i = ρ j := by
  classical
  have hid := State.sum_mul_quantumRelativeEntropy_mix p hp hsum ρ
  have hμ_pos : ∀ j, 0 < (State.mix p hp hsum ρ).isDensity.isSymmetric.eigenvalues rfl j :=
    fun j => hμ.eigenvalues_pos _ rfl j
  have hterm : ∀ i ∈ Finset.univ,
      0 ≤ p i * (ρ i).quantumRelativeEntropy (State.mix p hp hsum ρ) :=
    fun i _ => mul_nonneg (hp i) (State.quantumRelativeEntropy_nonneg _ _ hμ_pos)
  set μ := State.mix p hp hsum ρ with hμdef
  -- Reduce the entropy equality to the vanishing of every weighted relative-entropy term.
  rw [← sub_eq_zero, ← hid, Finset.sum_eq_zero_iff_of_nonneg hterm]
  constructor
  · -- equality ⇒ every positive-weight component equals the average `μ`, hence all coincide
    intro hall i j hpi hpj
    have key : ∀ k, 0 < p k → ρ k = μ := by
      intro k hpk
      have hD : (ρ k).quantumRelativeEntropy μ = 0 := by
        rcases mul_eq_zero.mp (hall k (Finset.mem_univ k)) with h | h
        · exact absurd h (ne_of_gt hpk)
        · exact h
      exact (State.quantumRelativeEntropy_eq_zero_iff (ρ k) μ hμ_pos).mp hD
    rw [key i hpi, key j hpj]
  · -- all positive-weight components coincide ⇒ each equals `μ` ⇒ its relative entropy vanishes
    intro hall i _
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · simp [← h0]
    · have hiμ : ρ i = μ :=
        (State.mix_eq_of_forall_pos_eq p hp hsum ρ (ρ i) fun j hpj => hall j i hpj hpos).symm
      rw [(State.quantumRelativeEntropy_eq_zero_iff (ρ i) μ hμ_pos).mpr hiμ, mul_zero]

section Nonfaithful

open ContinuousLinearMap
open scoped ComplexOrder

/-- **Every component of a mixture is supported inside the mixture.** For a probability distribution
`p`, a family `ρ : ι → State S`, and an index `i` with `0 < pᵢ`, the density operator of `ρ i` is
supported inside that of the mixture `μ = ∑ⱼ pⱼ ρⱼ`, i.e. `(ρ i).op.HasSupportLE μ.op`
(`ker μ.op ≤ ker (ρ i).op`).

This is the atomic fact behind faithfulness-free concavity below: a vector `x` killed by the mixture
satisfies `0 = ⟪x, μ.op x⟫ = ∑ⱼ pⱼ ⟪x, ρⱼ.op x⟫`, a sum of non-negative complex terms (each `ρⱼ.op`
positive, each `pⱼ ≥ 0`); it therefore vanishes termwise, and the `i`-th term with `pᵢ > 0` forces
`⟪x, ρᵢ.op x⟫ = 0`, whence `ρᵢ.op x = 0` because a positive operator annihilates the vectors on
which its quadratic form vanishes (`ContinuousLinearMap.apply_eq_zero_of_re_inner_self_eq_zero`). -/
theorem State.hasSupportLE_mix {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (i : ι) (hpi : 0 < p i) :
    (ρ i).op.HasSupportLE (State.mix p hp hsum ρ).op := by
  rw [ContinuousLinearMap.hasSupportLE_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [ContinuousLinearMap.coe_coe] at hx ⊢
  -- `hx : (State.mix …).op x = 0`, goal `(ρ i).op x = 0`.
  have hzsum : ∑ j, (p j : ℂ) * inner ℂ x ((ρ j).op x) = 0 := by
    have h0 : inner ℂ x ((State.mix p hp hsum ρ).op x) = 0 := by rw [hx]; simp
    rw [State.mix_op, _root_.sum_apply, inner_sum] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun j _ => by
      rw [_root_.smul_apply, inner_smul_right]
  have hznn : ∀ j ∈ (Finset.univ : Finset ι), (0 : ℂ) ≤ (p j : ℂ) * inner ℂ x ((ρ j).op x) :=
    fun j _ => mul_nonneg (by exact_mod_cast hp j) ((ρ j).isDensity.isPositive.inner_nonneg_right x)
  have hzi : (p i : ℂ) * inner ℂ x ((ρ i).op x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hznn).mp hzsum i (Finset.mem_univ i)
  have hpi' : (p i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpi
  have hinner0 : inner ℂ x ((ρ i).op x) = 0 := (mul_eq_zero.mp hzi).resolve_left hpi'
  exact ContinuousLinearMap.apply_eq_zero_of_re_inner_self_eq_zero
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (ρ i).isDensity.isPositive)
    (by rw [hinner0]; simp)

-- The `State`-level support-condition Klein inequalities
-- (`State.quantumRelativeEntropy_nonneg_of_hasSupportLE` and
-- `…_eq_zero_iff_of_hasSupportLE`) are the faithful finite-branch form of N&C Theorem 11.7 and
-- are in `AxQM.Postulates.API.RelativeEntropy` (imported above); they
-- are applied below through the mixture support fact `State.hasSupportLE_mix`.

/-- **Concavity of the von Neumann entropy — faithfulness-free form** (Nielsen & Chuang eq. (11.79)
in full generality). For any probability distribution `p` and family `ρ : ι → State S`,

`∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`,

with **no faithfulness hypothesis** on the mixture. This strengthens
`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix` (which assumes a faithful mixture,
`IsStrictlyPositive μ.op`); the faithfulness-free *equality* condition is
`State.vonNeumannEntropy_mix_eq_sum_iff'` below (via the support-condition Klein equality case). The
faithfulness-free form is what makes both applicable to the generally rank-deficient pinched state
of Exercise 11.20.

Proof: the mixing identity `State.sum_mul_quantumRelativeEntropy_mix` writes the concavity gap as
`∑ᵢ pᵢ S(ρᵢ ‖ μ)`; each summand is `≥ 0` because for `pᵢ > 0` the support condition
`HasSupportLE (ρᵢ) μ` holds (`State.hasSupportLE_mix`), so the support-condition Klein inequality
`State.quantumRelativeEntropy_nonneg_of_hasSupportLE` applies, while a `pᵢ = 0` summand vanishes. -/
theorem State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix' {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    ∑ i, p i * (ρ i).vonNeumannEntropy ≤ (State.mix p hp hsum ρ).vonNeumannEntropy := by
  have hid := State.sum_mul_quantumRelativeEntropy_mix p hp hsum ρ
  have hnn : 0 ≤ ∑ i, p i * (ρ i).quantumRelativeEntropy (State.mix p hp hsum ρ) := by
    refine Finset.sum_nonneg fun i _ => ?_
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · rw [← h0]; simp
    · exact mul_nonneg (hp i) ((ρ i).quantumRelativeEntropy_nonneg_of_hasSupportLE _
        (State.hasSupportLE_mix p hp hsum ρ i hpos))
  linarith [hid, hnn]

/-- **Equality in the concavity inequality — strict concavity, faithfulness-free form.** For any
probability distribution `p` and family `ρ : ι → State S`, equality in the (faithfulness-free)
concavity inequality `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)` holds **iff every component carrying positive
weight equals the mixture**:

`S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ) ↔ ∀ i, 0 < pᵢ → ρᵢ = ∑ⱼ pⱼ ρⱼ`.

Unlike `State.vonNeumannEntropy_mix_eq_sum_iff` (Exercise 11.18, which assumes a **faithful**
mixture `IsStrictlyPositive μ.op`) this needs **no faithfulness**: it runs the same mixing-identity
argument but discharges the equality case of Klein's inequality through the *support condition*
(`State.hasSupportLE_mix` — each positive-weight component is supported inside the mixture — and the
support-condition Klein equality `State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE`). It
therefore applies to the generally rank-deficient pinched state of Exercise 11.20, where it supplies
the equality case of the concavity-based alternate proof of Theorem 11.9. -/
theorem State.vonNeumannEntropy_mix_eq_sum_iff' {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).vonNeumannEntropy = ∑ i, p i * (ρ i).vonNeumannEntropy
      ↔ ∀ i, 0 < p i → ρ i = State.mix p hp hsum ρ := by
  classical
  have hid := State.sum_mul_quantumRelativeEntropy_mix p hp hsum ρ
  set μ := State.mix p hp hsum ρ with hμdef
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ p i * (ρ i).quantumRelativeEntropy μ := by
    intro i _
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · rw [← h0, zero_mul]
    · exact mul_nonneg (hp i) ((ρ i).quantumRelativeEntropy_nonneg_of_hasSupportLE _
        (State.hasSupportLE_mix p hp hsum ρ i hpos))
  have hequiv : (μ.vonNeumannEntropy = ∑ i, p i * (ρ i).vonNeumannEntropy)
      ↔ (∑ i, p i * (ρ i).quantumRelativeEntropy μ = 0) := by
    rw [hid]; constructor <;> intro hh <;> linarith
  rw [hequiv, Finset.sum_eq_zero_iff_of_nonneg hterm]
  constructor
  · intro hall i hpi
    have hD : (ρ i).quantumRelativeEntropy μ = 0 :=
      (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_left (ne_of_gt hpi)
    exact (State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE (ρ i) μ
      (State.hasSupportLE_mix p hp hsum ρ i hpi)).mp hD
  · intro hall i _
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · rw [← h0, zero_mul]
    · rw [(State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE (ρ i) μ
        (State.hasSupportLE_mix p hp hsum ρ i hpos)).mpr (hall i hpos), mul_zero]

end Nonfaithful

end AxQM
