/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Nielsen & Chuang, Theorem 11.1 (Non-negativity of the relative entropy)

*(N&C p. 505.)*

Non-negativity of relative entropy H(p||q)>=0 with equality iff p=q.

Here `p, q` are probability distributions over a finite outcome set and
`H(p‖q) = ∑ₓ p(x) log(p(x)/q(x))` is the classical relative entropy (Kullback–Leibler
divergence). N&C's proof is the tangent-line bound `log x ≤ x − 1` (equality iff `x = 1`)
applied per outcome to `x = q(x)/p(x)`, summed against `p`. N&C fix the conventions
`−0 log 0 ≡ 0` and `−p(x) log 0 ≡ +∞` for `p(x) > 0` (p. 504), so `H(p‖q)` is finite exactly
when `supp p ⊆ supp q` and `= +∞` otherwise.

## Where this is formalised

Theorem 11.1 is a statement of pure **finite-probability real analysis**: it quantifies over
functions `p q : ι → ℝ` on a finite type and the real-valued quantity `Real.relativeEntropy p q`.
Its formalisation is below, alongside the Shannon entropy development it belongs to.

The base-2 logarithm of N&C is replaced by the natural logarithm (nats), matching the
`Real.entropy`/`Real.relativeEntropy` convention of `ToMathlib/`; non-negativity and the
equality condition are independent of the logarithm base, so this is a faithful reformulation, not
a weakening.

The real-valued `Real.relativeEntropy` uses the junk value `log 0 = 0`, so it agrees with N&C's
`H(p‖q)` precisely on the absolute-continuity domain `supp p ⊆ supp q` (`q x = 0 → p x = 0`),
where N&C's quantity is finite. The results below are therefore stated at exactly that
generality — matching the `≥ 0` sibling — rather than restricting to strictly
positive `q`. Outside that domain N&C set `H(p‖q) = +∞`, which is `> 0` with `p ≠ q`, consistent
with Theorem 11.1 but not representable in `ℝ`; that regime is not a weakening of the statement,
merely outside the finite real-valued encoding.

## The formalisation (in `ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`)

The classical relative entropy `Real.relativeEntropy p q = ∑ x, p x * (log (p x) - log (q x))`
and its two halves, both under `p ≥ 0`, `q ≥ 0`, `supp p ⊆ supp q`, equal total mass `∑ p = ∑ q`:

* `Real.relativeEntropy_nonneg_of_support_subset` — **the `≥ 0` half** (Gibbs' inequality):
  `0 ≤ D(p‖q)`. (`Real.relativeEntropy_nonneg` is its strictly-positive-`q`
  specialization with `∑ p = ∑ q = 1`.)
* `Real.relativeEntropy_eq_zero_iff` — **the equality half**: `D(p‖q) = 0 ↔ p = q`, under the
  same hypotheses. This is the "with equality if and only if `p = q`" clause; together
  with the support-aware non-negativity it is the faithful real-valued rendering of Theorem 11.1
  on the domain where `Real.relativeEntropy` equals N&C's `H(p‖q)`.
* `Real.relativeEntropy_pos_of_ne` — the sharp contrapositive form `p ≠ q → 0 < D(p‖q)`.

The equality half is proved via the strict per-outcome tangent bound
`Real.mul_log_div_lt_sub_of_ne` (`p * log (q / p) < q - p` when `p ≠ q`), the strict companion
of `Real.mul_log_div_le_sub_of_nonneg`, in
`ToMathlib/Analysis/SpecialFunctions/Log/Basic.lean` beside its non-strict sibling. Summing the
pointwise bound and using
`Finset.sum_eq_sum_iff_of_le` turns the global equality `D(p‖q) = 0` into per-outcome equality;
at each outcome either `q x = 0` (so `p x = 0 = q x` by the support hypothesis) or `q x > 0`,
where the strict bound refutes the equality unless `p x = q x`.
-/
