/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import ToMathlib.Analysis.InnerProductSpace.Density

/-!
# AxQM.Postulates.API — the maximally mixed state `I/d`

The **maximally mixed state** of a quantum system `S`: the density operator `I/d` where
`d = dim S` is the dimension of the state space. It is the state of maximal von Neumann entropy —
"total ignorance" — and the reduced state of a maximally entangled bipartite pure state
(Nielsen & Chuang §2.4.3; the `I/2` of Exercise 2.75).

* `maximallyMixedState S` — the state `(dim S)⁻¹ • I`, a `State S` (requires `Nontrivial S.space`,
  since a `0`-dimensional space has no density operator).

## Design notes

The operator is `(finrank ℂ S.space : ℂ)⁻¹ • 1`; it is a density operator by the lemma
`ContinuousLinearMap.isDensityOp_finrank_inv_smul_one` (positive, trace `d · (1/d) = 1`), which
needs `Nontrivial S.space` (on a subsingleton space `finrank = 0` and `0⁻¹ • 1 = 0` has trace `0`).

-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **maximally mixed state** `I/d` of the system `S`, where `d = dim S`: the density operator
`(finrank ℂ S.space)⁻¹ • 1`. Requires `Nontrivial S.space` (a state needs a nontrivial space). This
is the state of maximal entropy, and the marginal of a maximally entangled pure state. -/
def maximallyMixedState (S : QSystem) [Nontrivial S.space] : State S where
  op := (Module.finrank ℂ S.space : ℂ)⁻¹ • 1
  isDensity := ContinuousLinearMap.isDensityOp_finrank_inv_smul_one

/-- The operator of the maximally mixed state is `(dim S)⁻¹ • I`. A `simp` lemma exposing the
operator for operator computations. -/
@[simp]
theorem maximallyMixedState_op (S : QSystem) [Nontrivial S.space] :
    (maximallyMixedState S).op = (Module.finrank ℂ S.space : ℂ)⁻¹ • 1 := rfl

/-- **The maximally mixed state is faithful (strictly positive):** its operator `(dim S)⁻¹ • I`
has strictly positive spectrum. The canonical faithful reference state — e.g. the perturbation
target `(1 − ε) ρ + ε (I/d)` in faithfulness-free entropy arguments. -/
theorem maximallyMixedState_isStrictlyPositive (S : QSystem) [Nontrivial S.space] :
    IsStrictlyPositive (maximallyMixedState S).op := by
  rw [maximallyMixedState_op]
  exact ContinuousLinearMap.isStrictlyPositive_finrank_inv_smul_one

/-- **Every unitary conjugation fixes the maximally mixed state:** `U (I/d) U† = I/d`, i.e.
`U.evolve (maximallyMixedState S) = maximallyMixedState S`. Since `I/d = (1/d) • I` and `U U† = I`
(`Evolution.comp_adjoint_self`), the conjugation `U ((1/d)•I) U† = (1/d) • (U U†) = (1/d) • I`. This
is the atomic reason a unitary channel — and hence any random-unitary mixture of unitary channels
(`RandomUnitaryChannel.isUnital`) — is unital. A general `Evolution` fact, placed here so it is
citable without the channel machinery. -/
theorem Evolution.evolve_maximallyMixedState {S : QSystem} [Nontrivial S.space] (U : Evolution S) :
    U.evolve (maximallyMixedState S) = maximallyMixedState S := by
  apply State.ext
  simp only [Evolution.evolve_op, maximallyMixedState_op, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    U.comp_adjoint_self]

end AxQM
