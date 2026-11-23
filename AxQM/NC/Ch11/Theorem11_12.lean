/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativeEntropy

/-!
# N&C Theorem 11.12 — Joint convexity of the quantum relative entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.12, p. 520.

Theorem 11.12 (Convexity of the relative entropy) states that the quantum relative entropy
`S(ρ ‖ σ)` is **jointly convex** in its arguments: mixing a family of pairs `(ρₖ, σₖ)` with a
common set of probabilities `wₖ` cannot increase the relative entropy above the weighted average,

* `S(∑ₖ wₖ ρₖ ‖ ∑ₖ wₖ σₖ) ≤ ∑ₖ wₖ S(ρₖ ‖ σₖ)`.

## The formalisation

The relative entropy carries N&C's own two-branch definition (§11.3.1): `S(ρ ‖ σ) = +∞` when the
kernel of `σ` meets the support of `ρ` non-trivially, and `S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)`
(finite) otherwise. The real-valued `State.quantumRelativeEntropy` is the finite
quantity, so the faithful statement of joint convexity is N&C's theorem on the branch where that
quantity is a real number — the **support condition** `supp ρ ⊆ supp σ`, expressed as
`ρ.op.HasSupportLE σ.op` (`ker σ.op ≤ ker ρ.op`), imposed on each constituent pair.

The hypotheses are stated for the density operators `.op` (`HasSupportLE`), and the mixing is an
equation between density operators `ρ.op = ∑ₖ wₖ • (ρₖ).op`. Compare the relative-entropy results
of Theorem 11.7, Theorem 11.14 and Theorem 11.17.

The two forms of the theorem, both in `AxQM/Postulates/API/RelativeEntropy.lean` for
`State.quantumRelativeEntropy`:

* `AxQM.State.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE` — the **general
  `n`-ary form**: for families `ρs, σs : κ → State S` and convex weights `w` (`w k ≥ 0`,
  `∑ w k = 1`) with the support condition `(ρs k).op.HasSupportLE (σs k).op` on every component, if
  `ρ.op = ∑ₖ wₖ • (ρsₖ).op` and `σ.op = ∑ₖ wₖ • (σsₖ).op` then `S(ρ ‖ σ) ≤ ∑ₖ wₖ S(ρsₖ ‖ σsₖ)`.
  **No faithfulness (strict positivity) is required** — rank-deficient constituents are admitted.
  This is the form used in the strong-subadditivity route (`Theorem11_14`), where the partial
  trace is averaged as a twirl over a unitary `1`-design — a convex combination of unitary
  conjugates.
* `AxQM.State.quantumRelativeEntropy_jointly_convex_of_hasSupportLE` — N&C's **literal
  two-point statement**: for probabilities `t, s ≥ 0` with `t + s = 1`, states with the support
  conditions `ρ₁.op.HasSupportLE σ₁.op` and `ρ₂.op.HasSupportLE σ₂.op`, and `ρ.op = t • ρ₁.op +
  s • ρ₂.op`, `σ.op = t • σ₁.op + s • σ₂.op`, `S(ρ ‖ σ) ≤ t · S(ρ₁ ‖ σ₁) + s · S(ρ₂ ‖ σ₂)`. Obtained
  by instantiating the `n`-ary form over a two-element index.

The convenience corollaries `AxQM.State.quantumRelativeEntropy_jointly_convex_sum` and
`…_jointly_convex` are the strictly-stronger **faithful-constituent** special case — every `ρₖ, σₖ`
strictly positive (`IsStrictlyPositive`, i.e. full rank, `ker (σₖ).op = ⊥`) — used for the
strong-subadditivity argument, which works with strictly positive states.

Both faithful forms are derived from
`ContinuousLinearMap.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE`
(`ToMathlib/Analysis/InnerProductSpace/QuantumRelativeEntropyConvexNonfaithful.lean`); the two
positivity hypotheses that operator inequality needs hold for any state (`isDensity.isPositive`), so
only the support condition is a genuine hypothesis. That inequality is **Lindblad's theorem** —
itself a consequence of **Lieb's theorem** (N&C Theorem 11.11), following N&C's own derivation:
`I(A, X)` of eq. (11.99) is concave in `A` by Lieb, and the block-matrix substitution eq. (11.103)
gives `I(A, X) = −S(ρ ‖ σ)`, so joint convexity of `S` is concavity of `I` — with the
strict-positivity restriction of Lindblad's cone removed by the `ε → 0⁺` perturbation-and-limit
engine (shift each operator by `ε • 1`, apply the strictly-positive inequality, and pass to the
limit on the finite branch, where the support condition keeps the `ker σ`-block harmless).

## The finite branch is the theorem, and the `+∞` branch is a convention

The support condition is **not an added hypothesis narrowing the theorem** — it is exactly N&C's own
"finite otherwise" clause, the natural domain of the real-valued relative entropy: `cfc Real.log`
sends the zero eigenvalues of a rank-deficient operator to `0` rather than `−∞`, so the
finite-valued inequality genuinely lives on that branch. On it the formalisation states N&C's
theorem verbatim,
`S(∑ₖ wₖ ρₖ ‖ ∑ₖ wₖ σₖ) ≤ ∑ₖ wₖ S(ρₖ ‖ σₖ)`, for *every* family of density operators with
`supp ρₖ ⊆ supp σₖ` — the `ρₖ, σₖ` may be rank-deficient.

Requiring every constituent to be **faithful** (`IsStrictlyPositive`, full rank) would be a
genuine narrowing — it excludes finite-branch pairs where the constituents are rank-deficient — so
that version is only a corollary (`State.quantumRelativeEntropy_jointly_convex_sum` /
`…_jointly_convex`), and the unrestricted support-condition statement is the one formalised,
as for Klein's inequality (Theorem 11.7) and strong subadditivity (Theorem 11.14).

The complementary `supp ρ ⊄ supp σ` branch carries no mathematical content beyond the definitional
convention `S(ρ ‖ σ) = +∞`: there the right-hand side is `+∞` whenever some constituent violates the
support condition, so the inequality holds vacuously. Encoding it would require an extended-real
(`EReal`) relative entropy, a different object from the real-valued quantity used throughout the
Chapter 11 entropy development, and would add no content to the theorem itself. The real-valued
relative entropy on its finite branch is the faithful formalisation.
-/
