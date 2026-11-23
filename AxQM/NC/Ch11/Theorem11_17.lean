/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativeEntropy

/-!
# N&C Theorem 11.17 — Monotonicity of the relative entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.17, p. 524.

For two density operators `ρ^AB` and `σ^AB` of a composite system `AB`, discarding the subsystem `B`
cannot increase the quantum relative entropy (eq. (11.125)):

`S(ρ^A ‖ σ^A) ≤ S(ρ^AB ‖ σ^AB)`,

where `ρ^A = Tr_B ρ^AB` and `σ^A = Tr_B σ^AB` are the marginals on `A`. This is the distance-like
*monotonicity* of the relative entropy: ignoring part of a system makes two states harder to
distinguish, so any reasonable measure of their distinguishability decreases. Applied to the
mutual-information relative entropy `S(ρ^AB ‖ ρ^A ⊗ ρ^B)` it yields the strong subadditivity of the
von Neumann entropy (N&C Theorem 11.14).

## The formalisation

The relative entropy carries N&C's own two-branch definition (§11.3.1): `S(ρ ‖ σ) = +∞` when
`supp ρ ⊄ supp σ`, and `S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)` (finite) otherwise. The real-valued
`State.quantumRelativeEntropy` is the finite quantity, so the faithful
statement of monotonicity is N&C's theorem on the branch where that quantity is a real number — the
**support condition** `supp ρ^AB ⊆ supp σ^AB`, expressed as `ρ.op.HasSupportLE σ.op`
(`ker σ.op ≤ ker ρ.op`). The `A`-marginal support condition needed for the left-hand side descends
from the joint one automatically.

The hypothesis is stated for the density operators `.op` (`HasSupportLE`), and the marginals are
the left reduced states `State.reducedLeft = Tr_B`. Compare the other relative-entropy theorems
(Klein's inequality, Theorem 11.7; joint convexity, Theorem 11.12) and strong subadditivity
(Theorem 11.14), which follows from this one.

The two statements are in `AxQM/Postulates/API/RelativeEntropy.lean`, for
`State.quantumRelativeEntropy`:

* `AxQM.State.quantumRelativeEntropy_reduced_le_of_hasSupportLE` — the **faithful
  finite-branch statement**: `ρ.reducedLeft.quantumRelativeEntropy σ.reducedLeft ≤
  ρ.quantumRelativeEntropy σ` for states `ρ, σ : State (S.compose T)` with the support condition
  `ρ.op.HasSupportLE σ.op` — **no faithfulness (strict positivity) required**, rank-deficient states
  admitted. It is derived from the operator theorem
  `ContinuousLinearMap.quantumRelativeEntropy_partialTraceRight_le_of_hasSupportLE`
  (`ToMathlib/Analysis/InnerProductSpace/QuantumRelativeEntropyMonotone.lean`).
* `AxQM.State.quantumRelativeEntropy_reduced_le` — the strictly-stronger faithful-states
  (`IsStrictlyPositive`, full rank) special case, a corollary for strictly positive states
  (e.g. the strong-subadditivity twirl constituents).

## Proof route

Following N&C's proof (via Exercise 11.19), the completely depolarizing partial-trace channel
`τ ↦ (Tr_T τ) ⊗ I/d` is exhibited as a uniform mixed-unitary average over a unitary `1`-design
`{I_A ⊗ Uⱼ}` and fed into the mixed-unitary data-processing inequality
(`ContinuousLinearMap.quantumRelativeEntropy_sum_conjStarAlgEquiv_le`), whose engine is the
**support-condition joint convexity** of the relative entropy (N&C Theorem 11.12); the maximally
mixed `I/d` factor is then cancelled by the common-right-factor tensor split
(`quantumRelativeEntropy_mapL_right_eq`), giving eq. (11.129)
`S(ρ^A ⊗ I/d ‖ σ^A ⊗ I/d) = S(ρ^A ‖ σ^A)`. Strict positivity is removed throughout by the identity-
shift perturbation `ρ + ε • 1` and the limit `ε → 0⁺` (`ρ, σ` shifted by `ε`, their `A`-marginals by
`d · ε` since `Tr_B(ε • 1) = (d ε) • 1`), matching the faithfulness-free treatment of the
joint convexity used in this route.

## The finite branch is the theorem

The support condition is **not an added hypothesis narrowing the theorem** — it is exactly N&C's own
"finite otherwise" clause, the natural domain of the real-valued relative entropy. On it the
formalisation states eq. (11.125) verbatim for *every* pair of density operators with
`supp ρ^AB ⊆ supp σ^AB` — the states may be rank-deficient.

Requiring both states to be **faithful** (`IsStrictlyPositive`, full rank) would be a genuine
narrowing — it excludes finite-branch pairs with rank-deficient states — so that version is only
the corollary `State.quantumRelativeEntropy_reduced_le`, and the unrestricted support-condition
statement is the one formalised, as for Klein's inequality (Theorem 11.7) and joint
convexity (Theorem 11.12). The complementary `supp ρ^AB ⊄ supp σ^AB` branch carries no mathematical
content beyond the convention `S(ρ^AB ‖ σ^AB) = +∞` (the inequality then holds vacuously); encoding
it would require an extended-real (`EReal`) relative entropy distinct from the real-valued quantity
used throughout the Chapter 11 entropy development, and would add no content to the theorem.
-/
