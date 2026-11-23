/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropyConcave

/-!
# N&C Exercise 11.21 — concavity of the Shannon entropy from concavity of the von Neumann entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.21, p. 518: *use the concavity of the von Neumann entropy to deduce that the Shannon
entropy is concave.*

The statement involves only the classical Shannon entropy and the von Neumann entropy of
operators.

## Where the formalisation lives

All declarations are in `ToMathlib/Analysis/InnerProductSpace/DiagonalOperatorEntropyConcave.lean`
(building on the operator↔Shannon-entropy bridge of
`ToMathlib/Analysis/InnerProductSpace/DiagonalOperatorEntropy.lean`):

* `Real.sum_mul_entropy_le_entropy_convexCombination` — **the exercise.** Concavity of the Shannon
  entropy in mixture form: for a probability distribution `p : ι → ℝ` and a family of probability
  distributions `q : ι → α → ℝ`,
  `∑ᵢ pᵢ H(qᵢ) ≤ H(∑ᵢ pᵢ qᵢ)`. (The abstract `ConcaveOn` rendering on the domain of nonnegative
  vectors is the independently-proved `Real.entropy_concave`; the statement here is the deduction
  *from the von Neumann entropy* that the exercise asks for.)

The supporting declarations, also in that file:

* `ContinuousLinearMap.IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE` — the
  **concavity of the von Neumann entropy** actually used, in faithfulness-free form
  (`∑ᵢ pᵢ S(ρᵢ) ≤ S(σ)` for `σ = ∑ᵢ pᵢ ρᵢ`, no strict-positivity hypothesis), obtained from the
  mixing (Holevo χ) identity `ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix` and the
  support-condition Klein inequality `quantumRelativeEntropy_nonneg_of_hasSupportLE`.
* `OrthonormalBasis.diagonalOperator_sum_smul` — diagonalisation is linear in the diagonal, so a
  mixture of distributions maps to the mixture of diagonal density operators.
* `OrthonormalBasis.hasSupportLE_diagonalOperator` — the support condition for two diagonal
  operators reduces to the pointwise support condition on their diagonals (discharging the
  hypothesis of the operator concavity for the diagonal mixture).

## Design note — why no perturbation argument is needed

Realising each distribution `qᵢ` as a diagonal density operator sends the classical mixture to an
operator mixture whose diagonal may vanish at some outcome (when the mixture assigns it zero
probability), so the mixture is generally *not* strictly positive. Rather than removing that
restriction by a regularisation/limit (`qᵢᵗ := (1−t)·qᵢ + t·uniform`, `t → 0⁺`, using continuity of
the Shannon entropy), we consume the **faithfulness-free** operator concavity directly: its
relative-entropy proof route needs only the support condition `supp ρᵢ ⊆ supp σ`, which holds for
any genuine mixture, so the general concavity — including distributions with zero entries — drops
out with no limiting argument.
-/
