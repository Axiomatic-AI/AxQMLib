/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.GeneralizedRelativeEntropy

/-!
# Nielsen & Chuang, Problem 11.2 (Generalized relative entropy)

Generalized relative entropy for positive operators: scaling, subadditivity <-> joint convexity,
mixture bound.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 11.2 (p. 525).

The generalized relative entropy `S(r ‖ s) = tr(r log r) − tr(r log s)` of two positive operators,
and the identities/inequalities of parts (1)–(4), are statements of operator analysis (the
continuous functional calculus, trace, and the joint convexity of the relative entropy).

The generalized relative entropy itself is `ContinuousLinearMap.quantumRelativeEntropy` from
`ToMathlib/Analysis/InnerProductSpace/QuantumRelativeEntropy.lean`, whose definition
`re tr(ρ log ρ) − re tr(ρ log σ)` is exactly N&C's `(11.131)`. Its joint convexity — Lindblad's
theorem, `ContinuousLinearMap.convexOn_quantumRelativeEntropy` — is already in the library; Problem
11.2 takes it as given ("the earlier argument goes directly through").

## Faithful domain: positive operators on the finite branch

N&C states the problem for **any two positive operators**, not only strictly positive ones. The
`cfc`-based relative entropy `S(r ‖ s)` equals the true relative entropy precisely on the *finite
branch* — the support condition `supp r ⊆ supp s` (`ContinuousLinearMap.HasSupportLE r s`, i.e.
`ker s ≤ ker r`), on which the `Real.log 0 = 0` junk value off the support of `s` never contributes.
This is the domain of N&C's own joint-convexity theorem (Theorem 11.12,
`quantumRelativeEntropy_jointly_convex_of_hasSupportLE`). All four parts are therefore formalised
for `IsPositive` operators under `HasSupportLE`; the earlier strictly-positive statements are
retained as the special case `HasSupportLE.of_isStrictlyPositive`. (A wholly unconstrained positive
`r, s` is *not* faithful: off the support condition the very identities of parts (1)–(4) fail — the
cross term `tr(r log(d • s))` picks up a `log d · tr(r · P_{ker s})` discrepancy.)

## Where the formalisation lives

The parts of this problem are formalised in
`ToMathlib/Analysis/InnerProductSpace/GeneralizedRelativeEntropy.lean`, for positive operators on a
finite-dimensional complex Euclidean space satisfying the support condition (`IsPositive` +
`HasSupportLE`):

* `ContinuousLinearMap.quantumRelativeEntropy_smul_smul_of_hasSupportLE` — **part (1)**, the scaling
  law `S(c • r ‖ d • s) = c · S(r ‖ s) + c · tr(r) · log(c / d)`.
* `ContinuousLinearMap.quantumRelativeEntropy_subadditive_of_jointConvex_of_hasSupportLE` — **part
  (2)**, joint convexity implies subadditivity, and
  `ContinuousLinearMap.quantumRelativeEntropy_subadditive_of_hasSupportLE`, the concrete
  subadditivity obtained by discharging that hypothesis with the faithful Lindblad theorem
  (N&C Thm 11.12).
* `ContinuousLinearMap.quantumRelativeEntropy_jointConvex_of_subadditive_of_hasSupportLE` — **part
  (3)**, the converse implication, closing the equivalence `subadditivity ↔ joint convexity`.
* `ContinuousLinearMap.quantumRelativeEntropy_sum_le_sum_of_hasSupportLE` — the n-ary (finite
  `Finset`) subadditivity `S(∑ᵢ rᵢ ‖ ∑ᵢ sᵢ) ≤ ∑ᵢ S(rᵢ ‖ sᵢ)` (the finite iterate of the binary
  subadditivity, on which part (4) is built), with the per-term support transport
  `ContinuousLinearMap.hasSupportLE_smul_smul`.
* `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le_of_hasSupportLE` — **part (4)**, the
  mixture bound `(11.134)`,
  `S(∑ᵢ pᵢ rᵢ ‖ ∑ᵢ qᵢ sᵢ) ≤ ∑ᵢ pᵢ S(rᵢ ‖ sᵢ) + ∑ᵢ pᵢ tr(rᵢ) log(pᵢ / qᵢ)`, via n-ary subadditivity
  applied to `pᵢ • rᵢ`, `qᵢ • sᵢ` plus the per-term scaling law. N&C phrases it for probability
  distributions; the bound needs only `pᵢ, qᵢ > 0`, so the formalised statement is the stronger
  positive-weight form.
* `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy_of_hasSupportLE` —
  the "pretty formula" `(11.135)`: for density operators (`tr(rᵢ) = 1`) the correction term
  collapses to the classical relative entropy `Real.relativeEntropy p q` (Kullback–Leibler
  divergence).

The strictly-positive forms of every part
(`quantumRelativeEntropy_smul_smul`, `..._subadditive`, `..._jointConvex_of_subadditive`,
`..._sum_le_sum`, `..._sum_smul_smul_le`, `..._sum_smul_smul_le_relativeEntropy`) live in the same
file as the `HasSupportLE.of_isStrictlyPositive` special cases.
-/
