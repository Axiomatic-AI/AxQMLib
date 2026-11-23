/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativeEntropy

/-!
# N&C Theorem 11.7 — Klein's inequality

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.7, p. 511.

Klein's inequality states that the quantum relative entropy of two states is non-negative,

* eq. (11.51): `S(ρ ‖ σ) ≥ 0`, **with equality if and only if `ρ = σ`**.

## The formalisation

The relative entropy carries N&C's own two-branch definition (eq. (11.50)): `S(ρ ‖ σ) = +∞` when
`supp ρ ⊄ supp σ` and `S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)` (finite) otherwise. The real-valued
`State.quantumRelativeEntropy` is the finite quantity, so the faithful
statement of Klein's inequality is N&C's theorem on the branch where that quantity is a real
number — the **support condition** `supp ρ ⊆ supp σ`, expressed as `ρ.op.HasSupportLE σ.op`
(`ker σ.op ≤ ker ρ.op`). The statements are in terms of the density operators `.op`. Compare the
relative-entropy results of Theorem 11.12, Theorem 11.14 and Theorem 11.17.

The two halves of Klein's inequality are in `AxQM/Postulates/API/RelativeEntropy.lean`, for
`State.quantumRelativeEntropy`:

* `AxQM.State.quantumRelativeEntropy_nonneg_of_hasSupportLE` — non-negativity
  `S(ρ ‖ σ) ≥ 0` (eq. (11.51)) on the finite branch `ρ.op.HasSupportLE σ.op`, **with no faithfulness
  restriction on `σ`**. It is derived from the operator support-condition Klein–Gibbs inequality
  `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg_of_hasSupportLE`.
* `AxQM.State.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE` — the **equality
  condition** `S(ρ ‖ σ) = 0 ↔ ρ = σ` on the finite branch. It is derived from the operator equality
  condition
  `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE`
  (`ToMathlib/Analysis/InnerProductSpace/GeneralizedKleinInequality.lean`),
  lifting operator equality `ρ.op = σ.op` to state equality `ρ = σ` via `State.ext`.

The reverse ("if") half `ρ = σ ⟹ S(ρ ‖ σ) = 0` is the unconditional
`AxQM.State.quantumRelativeEntropy_self_eq_zero` (`S(ρ ‖ ρ) = 0`, no hypothesis).

The corollaries `AxQM.State.quantumRelativeEntropy_nonneg` and
`…_eq_zero_iff` are the strictly-stronger **faithful-`σ`** special case `ker σ.op = ⊥` (every
eigenvalue of `σ.op` positive), used where the reference state is strictly positive (e.g. entropy
concavity).

## The finite branch is Klein's theorem, and the `+∞` branch is a convention

The support condition is **not an added hypothesis narrowing the theorem** — it is exactly N&C's own
"finite otherwise" clause, the natural domain of the real-valued relative entropy. On that domain
the formalisation states N&C's theorem verbatim: `S(ρ ‖ σ) ≥ 0`, with equality iff `ρ = σ`, for
*every* pair of density operators — `σ` may be rank-deficient, and so may `ρ`. Restricting `σ` to be
**faithful** (full rank) would be a genuine narrowing (it excludes finite-branch pairs where both
`ρ` and `σ` are rank-deficient), so that version is only a corollary of the unrestricted statement.

The complementary `supp ρ ⊄ supp σ` branch carries no mathematical content beyond the definitional
convention `S(ρ ‖ σ) = +∞`: there `S(ρ ‖ σ) = +∞ > 0` and `ρ ≠ σ` automatically (equal states have
equal support), so the inequality and its equality condition hold vacuously. Encoding it would
require an extended-real-valued (`EReal`) relative entropy — a different object from the
real-valued quantity used throughout the Chapter 11 entropy development (Klein → concavity →
subadditivity → strong subadditivity) — and would add no content to the theorem. The
real-valued relative entropy on its finite branch is the faithful formalisation.

## The proof

The `ToMathlib/` proof follows N&C's own argument: N&C write
`S(ρ ‖ σ) = ∑ᵢ pᵢ (log pᵢ − ∑ⱼ Pᵢⱼ log qⱼ)` with the doubly-stochastic overlap matrix
`Pᵢⱼ = |⟪i|j⟫|²`; the lemma
`generalized_klein_residual_eq` is exactly this doubly-stochastic gap-sum, and the equality case is
closed by strict convexity of `x ↦ x log x` where the overlaps are non-zero (giving `ρ = σ`) — the
zero-eigenvalue block of `σ` being handled not by faithfulness but by the support condition
`ker σ.op ≤ ker ρ.op` (`eigenvalue_eq_zero_of_hasSupportLE`).
-/
