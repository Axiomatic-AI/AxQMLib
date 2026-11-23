/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.DataProcessingInequality

/-!
# Conditional entropy grows when adjoining a variable (Nielsen & Chuang, Problem 11.3, part 1)

For a tripartite distribution `p : ι × κ × μ → ℝ` of `(X, Y, Z)` (read as `ι × (κ × μ)`), this file
proves the classical **conditional-entropy monotonicity** of Nielsen & Chuang, Problem 11.3, part 1:

`H(X, Y | Z) ≥ H(X | Z)`,

i.e. adjoining a variable `Y` to the un-conditioned side of a conditional entropy never decreases
it. Both conditional entropies are built on `Real.condEntropy` / `Real.entropy`
(`ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`) and the `(X, Z)`-marginal
`Real.marginalFstLast` (`ToMathlib/Analysis/SpecialFunctions/DataProcessingInequality.lean`).

Since `H(X, Y | Z) = H(X, Y, Z) − H(Z)` and `H(X | Z) = H(X, Z) − H(Z)` share the same conditioning
term `H(Z)`, the statement reduces to `H(X, Z) ≤ H(X, Y, Z)` — the joint entropy dominates the
`(X, Z)`-marginal entropy (`Real.entropy_marginalFstLast_le`), the middle-variable analogue of
`Real.entropy_marginalFst_le` (obtained by regrouping the distribution as `((X, Z), Y)`).

## Main results

* `Real.entropy_marginalFstLast_le` — `H(X, Z) ≤ H(X, Y, Z)`.
* `Real.condEntropyPairGivenLast` — the pair conditional entropy `H(X, Y | Z) = H(X, Y, Z) − H(Z)`.
* `Real.condEntropy_marginalFstLast_le_condEntropyPairGivenLast` — Nielsen & Chuang, Problem 11.3,
  part 1: `H(X | Z) ≤ H(X, Y | Z)`.

This is pure finite-probability real analysis on `p : ι × κ × μ → ℝ`; the statement of Problem 11.3
is in `AxQM/NC/Ch11/Problem11_3.lean`. It is the classical
inequality whose *quantum* analogue `S(A, B | C) ≥ S(A | C)` **fails** — see Problem 11.3, part 2
(`AxQM.exists_condEntropyPairGivenC_lt`). Entropy is in nats; the inequality is
base-invariant, so this is a faithful reformulation of N&C's base-2 statement.
-/

@[expose] public section

namespace Real

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

omit [Fintype μ] in
/-- The second marginal of the `(X, Z)`-marginal is the `Z`-marginal: `(p_{XZ})_Z = p_Z`. Both equal
`∑_{x, y} p(x, y, z)`; they differ only in summation order. -/
theorem marginalSnd_marginalFstLast (p : ι × κ × μ → ℝ) :
    marginalSnd (marginalFstLast p) = marginalSnd (marginalSnd p) := by
  funext z
  simp only [marginalSnd_apply, marginalFstLast_apply]
  rw [Finset.sum_comm]

/-- **The joint entropy dominates the `(X, Z)`-marginal entropy**: `H(X, Z) ≤ H(X, Y, Z)`. This is
the analogue of `Real.entropy_marginalFst_le` that sums out the *middle* variable `Y`. Regrouping
the tripartite distribution as `((X, Z), Y)` turns the `(X, Z)`-marginal into an ordinary first
marginal, to which `entropy_marginalFst_le` applies (the regrouping leaves the entropy unchanged, a
reindexing of the defining sum). -/
theorem entropy_marginalFstLast_le {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    entropy (marginalFstLast p) ≤ entropy p := by
  have hmf : marginalFst (fun w : (ι × μ) × κ ↦ p (w.1.1, w.2, w.1.2)) = marginalFstLast p := by
    funext w
    obtain ⟨x, z⟩ := w
    simp only [marginalFst_apply, marginalFstLast_apply]
  have he : entropy (fun w : (ι × μ) × κ ↦ p (w.1.1, w.2, w.1.2)) = entropy p := by
    rw [entropy_eq, entropy_eq]
    exact Fintype.sum_equiv
      { toFun := fun w ↦ (w.1.1, w.2, w.1.2), invFun := fun t ↦ ((t.1, t.2.2), t.2.1),
        left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl, right_inv := fun ⟨_, _, _⟩ ↦ rfl } _ _ fun _ ↦ rfl
  calc entropy (marginalFstLast p)
      = entropy (marginalFst (fun w : (ι × μ) × κ ↦ p (w.1.1, w.2, w.1.2))) := by rw [hmf]
    _ ≤ entropy (fun w : (ι × μ) × κ ↦ p (w.1.1, w.2, w.1.2)) :=
        entropy_marginalFst_le (fun _ ↦ hp _)
    _ = entropy p := he

/-- **The pair conditional entropy** `H(X, Y | Z) = H(X, Y, Z) − H(Z)` of a tripartite distribution
`p : ι × κ × μ → ℝ`: the entropy of the pair `(X, Y)` conditioned on the last variable `Z`, with
`H(Z)` the entropy of the `Z`-marginal `marginalSnd (marginalSnd p)`. Compare `Real.condEntropy`
(`= H(X | Y)`) and the quantum `AxQM.State.condEntropyPairGivenC` (`= S(A, B | C)`). -/
noncomputable def condEntropyPairGivenLast (p : ι × κ × μ → ℝ) : ℝ :=
  entropy p - entropy (marginalSnd (marginalSnd p))

/-- Unfolding lemma for `condEntropyPairGivenLast` (the citable rewrite mirroring
`Real.condEntropy_eq`): `H(X, Y | Z) = H(X, Y, Z) − H(Z)`. -/
theorem condEntropyPairGivenLast_eq (p : ι × κ × μ → ℝ) :
    condEntropyPairGivenLast p = entropy p - entropy (marginalSnd (marginalSnd p)) := rfl

/-- **Nielsen & Chuang, Problem 11.3, part 1**: conditioning on `Z`, adjoining a variable `Y` to
the un-conditioned side never decreases the conditional entropy — `H(X | Z) ≤ H(X, Y | Z)`. Here
`H(X | Z) = condEntropy (marginalFstLast p)` is the conditional entropy of the `(X, Z)`-marginal.
Both sides subtract the same `H(Z)` (`marginalSnd_marginalFstLast`), so the claim reduces to
`H(X, Z) ≤ H(X, Y, Z)` (`entropy_marginalFstLast_le`).

This is the classical inequality whose quantum analogue `S(A, B | C) ≥ S(A | C)` *fails* (Problem
11.3, part 2, `AxQM.exists_condEntropyPairGivenC_lt`): quantum conditional entropy can be
negative, so adjoining a system to the un-conditioned side can *decrease* it. -/
theorem condEntropy_marginalFstLast_le_condEntropyPairGivenLast {p : ι × κ × μ → ℝ}
    (hp : ∀ q, 0 ≤ p q) :
    condEntropy (marginalFstLast p) ≤ condEntropyPairGivenLast p := by
  rw [condEntropy_eq, condEntropyPairGivenLast_eq, marginalSnd_marginalFstLast]
  linarith [entropy_marginalFstLast_le hp]

end Real
