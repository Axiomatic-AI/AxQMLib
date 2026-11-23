/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StrongSubadditivity
import AxQM.Postulates.API.ArakiLiebEqualityConditions
import AxQM.NC.Ch11.Theorem11_10

/-!
# General (faithfulness-free) strong subadditivity of the von Neumann entropy

The theorem `State.vonNeumannEntropy_add_le_add` (N&C Theorem 11.14, eq. (11.73))
proves strong subadditivity `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` only for a **faithful** (strictly
positive) tripartite state.
This file removes that hypothesis:

* `AxQM.State.vonNeumannEntropy_add_le_add'` — strong subadditivity
  `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` for an **arbitrary** state `ρ` on `A ⊗ (B ⊗ C)`.

This is N&C eq. (11.73) exactly as stated, with no restriction on the state, and it is the general
form used for the "form-1" inequality (weak monotonicity, N&C eq. (11.72) / Exercise 11.24) and
hence the second-entry subadditivity of the conditional entropy (Theorem 11.16, eq. (11.118)):
those two derive from strong subadditivity applied to a **marginal of a purification**, which is a
pure (rank-one) state's reduced state and hence generically **not** faithful — so the faithful form
alone cannot reach them.

## Method

The removal of faithfulness is a **perturbation/limiting** argument (below), continuous in the trace
distance via Fannes' inequality. The continuity corollary
`State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance` is in
`AxQM/NC/Ch11/Theorem11_10.lean` (it uses the Fannes bound of `AxQM/NC/Ch11/Theorem11_6.lean`).
The perturbation proof mirrors that of the sibling `State.vonNeumannEntropy_mix_le'`.

## Proof

For `εₙ = 1/(n+1) ↓ 0`, replace `ρ` by the faithful state `ρₙ = (1 − εₙ) ρ + εₙ (I/d)`
(strictly positive, since the maximally mixed `I/d` is and `IsStrictlyPositive.nonneg_add`), apply
the faithful strong subadditivity to `ρₙ`, and pass to the limit `n → ∞`. Every one of the four
entropy terms is `S` of a marginal of `ρₙ`, and each marginal of a finite mixture is the mixture of
the marginals — reusing the operator-linearity facts `State.reducedLeft_mix`,
`State.reducedRight_mix` (`AxQM/Postulates/API/ArakiLiebEqualityConditions.lean`) and
`State.congr_mix` (`AxQM/Postulates/API/Mixture.lean`) — so it converges to the corresponding
marginal of `ρ` in trace distance (joint convexity of the trace distance,
`State.traceDistance_mix_jointly_convex`). Continuity of the
entropy in trace distance (`State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance`) turns each
into an entropy limit, and `le_of_tendsto_of_tendsto'` carries the per-`n` faithful inequality
across to the limit. The perturbation is written as a two-point `State.mix` over `Fin 2` (rather
than `State.mixPair`) so those marginal-of-mixture identities discharge through the `Finset.sum`
linearity of the partial trace. This keeps full N&C generality.
-/

open Filter
open scoped Topology TensorProduct InnerProductSpace

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **Entropy convergence for a two-point perturbation** (the limiting engine of the general strong
subadditivity below). If a sequence of states `G n` is the two-point mixture
`(wₙ)₀ g₀ + (wₙ)₁ g₁` and the second weight `(wₙ)₁ → 0`, then `S(G n) → S(g₀)`. Proof: the trace
distance `D(G n, g₀)` is bounded by `(wₙ)₁ · D(g₁, g₀)` (joint convexity of the trace distance,
`State.traceDistance_mix_jointly_convex`, with `D(g₀, g₀) = 0`), which tends to `0`; continuity of
the entropy in trace distance (`State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance`) finishes.
Kept universe-polymorphic in `W`, to apply to marginals on different composite systems. -/
private theorem State.tendsto_vonNeumannEntropy_mixPerturb {W : QSystem} (w : ℕ → Fin 2 → ℝ)
    (hw0 : ∀ n i, 0 ≤ w n i) (hwsum : ∀ n, ∑ i, w n i = 1)
    (hε : Tendsto (fun n : ℕ => w n 1) atTop (𝓝 0)) (G : ℕ → State W) (g₀ g₁ : State W)
    (hG : ∀ n, G n = State.mix (w n) (hw0 n) (hwsum n) ![g₀, g₁]) :
    Tendsto (fun n => (G n).vonNeumannEntropy) atTop (𝓝 g₀.vonNeumannEntropy) := by
  apply State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance
  have hbnd : Tendsto (fun n : ℕ => w n 1 * g₁.traceDistance g₀) atTop (𝓝 0) := by
    simpa using hε.mul_const (g₁.traceDistance g₀)
  refine squeeze_zero (fun n => State.traceDistance_nonneg _ _) (fun n => ?_) hbnd
  rw [hG n]
  calc (State.mix (w n) (hw0 n) (hwsum n) ![g₀, g₁]).traceDistance g₀
      = (State.mix (w n) (hw0 n) (hwsum n) ![g₀, g₁]).traceDistance
          (State.mix (w n) (hw0 n) (hwsum n) (fun _ => g₀)) := by rw [State.mix_const]
    _ ≤ ∑ i, w n i * (![g₀, g₁] i).traceDistance g₀ :=
        State.traceDistance_mix_jointly_convex _ _ _ _ _
    _ = w n 1 * g₁.traceDistance g₀ := by
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, State.traceDistance_self, mul_zero,
          zero_add]

set_option maxHeartbeats 800000 in
-- The perturbation-and-limit argument threads a `Fin 2` mixture through the four nested-tensor
-- marginal entropies of `A ⊗ (B ⊗ C)`, whose elaboration exceeds the default `maxHeartbeats`.
/-- **Strong subadditivity of the von Neumann entropy, general form** (Nielsen & Chuang,
Theorem 11.14, eq. (11.73)): for an **arbitrary** state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)`,

with the marginals read off as reduced states exactly as in the faithful form
`State.vonNeumannEntropy_add_le_add`. This is the faithfulness-free strengthening: it drops the
`IsStrictlyPositive ρ.op` hypothesis, matching N&C's statement, which is what the weak-monotonicity
"form-1" inequality (eq. (11.72) / Exercise 11.24) and the second-entry conditional subadditivity
(Theorem 11.16, eq. (11.118)) require — they apply strong subadditivity to a marginal of a
purification, a non-faithful state.

The proof perturbs `ρ` toward the maximally mixed state, `ρₙ = (1 − εₙ) ρ + εₙ (I/d)` with
`εₙ = 1/(n+1) ↓ 0` (strictly positive, so the faithful form applies), and passes to the limit; both
sides are continuous in trace distance via Fannes' inequality
(`State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance`), and each marginal of `ρₙ` converges to
that of `ρ` because the marginal of a mixture is the mixture of the marginals. -/
theorem State.vonNeumannEntropy_add_le_add' (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.vonNeumannEntropy + ρ.reducedRight.reducedLeft.vonNeumannEntropy ≤
      (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy +
        ρ.reducedRight.vonNeumannEntropy := by
  classical
  have : Nontrivial (A ⊗ (B ⊗ C)).space := ρ.nontrivial_space
  -- The maximally mixed reference state `I/d`, and the two-point family `![ρ, I/d]`.
  set τ : State (A ⊗ (B ⊗ C)) := maximallyMixedState (A ⊗ (B ⊗ C)) with hτ
  have hτpos : IsStrictlyPositive τ.op := by
    rw [hτ]; exact maximallyMixedState_isStrictlyPositive _
  -- Make `τ` opaque (only `hτpos` is needed below): this keeps the marginal-identity `rfl`s cheap,
  -- since they would otherwise unfold `maximallyMixedState` through the nested partial traces.
  clear_value τ
  set states : Fin 2 → State (A ⊗ (B ⊗ C)) := ![ρ, τ] with hstates
  -- Perturbation weights `wₙ = ![1 − εₙ, εₙ]`, `εₙ = 1/(n+1) ↓ 0`.
  have hεpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hεle : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  set w : ℕ → Fin 2 → ℝ := fun n => ![1 - 1 / (n + 1), 1 / (n + 1)] with hw
  have hw0 : ∀ n, ∀ i, 0 ≤ w n i := fun n => by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;> simp only [hw, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linarith [hεle n]
    · linarith [hεpos n]
  have hwsum : ∀ n, ∑ i, w n i = 1 := fun n => by
    simp only [hw, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hεtendsto : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- The perturbed state `ρₙ = (1 − εₙ) ρ + εₙ (I/d)`, faithful for every `n`.
  set F : ℕ → State (A ⊗ (B ⊗ C)) := fun n => State.mix (w n) (hw0 n) (hwsum n) states with hF
  have hposN : ∀ n, IsStrictlyPositive (F n).op := by
    intro n
    rw [hF, State.mix_op, Fin.sum_univ_two]
    simp only [hw, hstates, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.coe_smul]
    refine IsStrictlyPositive.nonneg_add ?_ ?_
    · exact smul_nonneg (by linarith [hεle n]) ρ.isDensity.nonneg
    · exact IsStrictlyPositive.smul (hεpos n) hτpos
  -- Generic marginal convergence: for endpoint states `g₀ g₁`, the entropy of the perturbed mixture
  -- `(1 − εₙ) g₀ + εₙ g₁` converges to `S(g₀)` (as `εₙ ↓ 0`).
  have hε : Tendsto (fun n : ℕ => w n 1) atTop (𝓝 0) := by
    simpa only [hw, Matrix.cons_val_one, Matrix.cons_val_zero] using hεtendsto
  -- The four entropy terms converge; each is `S` of a marginal of `F n`, identified with the
  -- corresponding two-point mixture `(1 − εₙ) (marginal ρ) + εₙ (marginal τ)`. Passing the marginal
  -- *sequence* to `tendsto_vonNeumannEntropy_mixPerturb` keeps its conclusion syntactically equal
  -- to the goal (no `whnf` on the marginal-of-mixture terms, which would unfold partial traces).
  have hABC : Tendsto (fun n => (F n).vonNeumannEntropy) atTop (𝓝 ρ.vonNeumannEntropy) :=
    State.tendsto_vonNeumannEntropy_mixPerturb w hw0 hwsum hε F ρ τ
      (fun n => by simp only [hF, hstates])
  have hBC : Tendsto (fun n => (F n).reducedRight.vonNeumannEntropy) atTop
      (𝓝 ρ.reducedRight.vonNeumannEntropy) := by
    have hfam : (fun i => (states i).reducedRight) = ![ρ.reducedRight, τ.reducedRight] := by
      funext i; fin_cases i <;> rfl
    exact State.tendsto_vonNeumannEntropy_mixPerturb w hw0 hwsum hε
      ((fun n => (F n).reducedRight) : ℕ → State (B ⊗ C)) ρ.reducedRight τ.reducedRight
      (fun n => by simp only [hF, State.reducedRight_mix, hfam])
  have hB : Tendsto (fun n => (F n).reducedRight.reducedLeft.vonNeumannEntropy) atTop
      (𝓝 ρ.reducedRight.reducedLeft.vonNeumannEntropy) := by
    have hfam : (fun i => (states i).reducedRight.reducedLeft)
        = ![ρ.reducedRight.reducedLeft, τ.reducedRight.reducedLeft] := by
      funext i; fin_cases i <;> (rw [hstates]; rfl)
    exact State.tendsto_vonNeumannEntropy_mixPerturb w hw0 hwsum hε
      ((fun n => (F n).reducedRight.reducedLeft) : ℕ → State B) ρ.reducedRight.reducedLeft
      τ.reducedRight.reducedLeft
      (fun n => by simp only [hF, State.reducedRight_mix, State.reducedLeft_mix, hfam])
  have hAB : Tendsto (fun n => ((F n).congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy)
      atTop (𝓝 (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy) := by
    have hfam : (fun i => ((states i).congr (QSystem.assoc A B C)).reducedLeft)
        = ![(ρ.congr (QSystem.assoc A B C)).reducedLeft,
            (τ.congr (QSystem.assoc A B C)).reducedLeft] := by
      funext i; fin_cases i <;> (rw [hstates]; rfl)
    exact State.tendsto_vonNeumannEntropy_mixPerturb w hw0 hwsum hε
      ((fun n => ((F n).congr (QSystem.assoc A B C)).reducedLeft) : ℕ → State (A ⊗ B))
      (ρ.congr (QSystem.assoc A B C)).reducedLeft (τ.congr (QSystem.assoc A B C)).reducedLeft
      (fun n => by simp only [hF, State.congr_mix, State.reducedLeft_mix, hfam])
  -- The faithful inequality holds along the sequence; pass to the limit.
  have hbound : ∀ n, (F n).vonNeumannEntropy + (F n).reducedRight.reducedLeft.vonNeumannEntropy ≤
      ((F n).congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy +
        (F n).reducedRight.vonNeumannEntropy :=
    fun n => State.vonNeumannEntropy_add_le_add (F n) (hposN n)
  exact le_of_tendsto_of_tendsto' (hABC.add hB) (hAB.add hBC) hbound

end AxQM
